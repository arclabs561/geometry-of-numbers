#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# dependencies = ["requests"]
# ///

"""
LLM-based “read everything and critique” review.

This is intentionally NOT part of CI by default:
- it is non-deterministic
- it requires network + secrets

Intended usage (locally):
  OPENROUTER_API_KEY=... uv run Scripts/llm_review.py --scope staged
  # or:
  OPENAI_API_KEY=... uv run Scripts/llm_review.py --scope staged

To disable from `Scripts/check.sh pre-commit`:
  COVOLUME_LLM_REVIEW=0

Providers (auto-detected):
  - OpenRouter (preferred if OPENROUTER_API_KEY is set)
  - OpenAI (if OPENAI_API_KEY is set)

OpenRouter env:
  - OPENROUTER_API_KEY
  - OPENROUTER_BASE_URL (default: https://openrouter.ai/api/v1)
  - OPENROUTER_MODEL (override; otherwise chosen from COVOLUME_LLM_REVIEW_TIER)
  - COVOLUME_LLM_REVIEW_TIER (fast|balanced|heavy; default: balanced)
  - OPENROUTER_SITE_URL (optional; sent as HTTP-Referer)
  - OPENROUTER_APP_NAME (optional; sent as X-Title)

OpenAI env:
  - OPENAI_API_KEY
  - OPENAI_BASE_URL (default: https://api.openai.com/v1)
  - OPENAI_MODEL (default: gpt-4o-mini)
"""

from __future__ import annotations

import argparse
import hashlib
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

import requests


def sh(*args: str) -> str:
    return subprocess.check_output(list(args), text=True).strip()


def load_dotenv_if_present(root: Path) -> None:
    """
    Minimal dotenv loader.

    Policy:
    - Reads `.env` in the *repo root* by default.
    - Never overrides existing environment variables.
    - Supports KEY=VALUE with optional single/double quotes.

    Opt-in extra paths:
    - COVOLUME_DOTENV_PATH: colon-separated list of dotenv files to load (in order).
      This is the escape hatch if you keep your OpenRouter key elsewhere.

    Convenience (default-on) workspace search:
    - If no API key is configured after loading the candidates above, we scan one level deep
      under the parent directory of the repo root (e.g. `/Users/arc/Documents/dev/*/.env`),
      and load the first dotenv file that contains `OPENROUTER_API_KEY` or `OPENAI_API_KEY`.

      This matches the “super-workspace” setup where keys live in a sibling repo.
      Disable with: COVOLUME_DOTENV_SEARCH=0
      Override search root with: COVOLUME_DOTENV_SEARCH_ROOT=/abs/path
    """

    def parse_line(line: str) -> tuple[str, str] | None:
        s = line.strip()
        if not s or s.startswith("#"):
            return None
        if s.startswith("export "):
            s = s[len("export ") :].lstrip()
        if "=" not in s:
            return None
        k, v = s.split("=", 1)
        k = k.strip()
        v = v.strip()
        if not k:
            return None
        if (v.startswith('"') and v.endswith('"')) or (v.startswith("'") and v.endswith("'")):
            v = v[1:-1]
        return k, v

    def load_file(p: Path) -> bool:
        """
        Load dotenv file `p`.

        Returns true if we successfully read the file (even if it contained nothing relevant).
        Never overrides existing env vars.
        """
        try:
            if not p.exists() or not p.is_file():
                return False
            for line in p.read_text(encoding="utf-8", errors="replace").splitlines():
                kv = parse_line(line)
                if not kv:
                    continue
                k, v = kv
                if k in os.environ:
                    continue
                os.environ[k] = v
            return True
        except Exception:
            # dotenv loading must never block the commit hook.
            return False

    def has_any_key() -> bool:
        return bool(os.environ.get("OPENROUTER_API_KEY", "").strip() or os.environ.get("OPENAI_API_KEY", "").strip())

    candidates: list[Path] = []
    extra = os.environ.get("COVOLUME_DOTENV_PATH", "").strip()
    if extra:
        for part in extra.split(":"):
            part = part.strip()
            if not part:
                continue
            candidates.append(Path(part))
    else:
        candidates.append(root / ".env")

    for p in candidates:
        load_file(p)

    # If we still have no keys, scan the dev “super-workspace” for a sibling `.env`.
    # This is intentionally shallow (one directory deep) to avoid expensive recursive walks.
    if not has_any_key():
        search = os.environ.get("COVOLUME_DOTENV_SEARCH", "1").strip().lower()
        if search not in ("0", "false", "no", "off"):
            search_root_raw = os.environ.get("COVOLUME_DOTENV_SEARCH_ROOT", "").strip()
            search_root = Path(search_root_raw) if search_root_raw else root.parent

            try:
                # Only scan immediate child directories; skip hidden dirs.
                for child in sorted(search_root.iterdir()):
                    if not child.is_dir():
                        continue
                    if child.name.startswith("."):
                        continue
                    if child.resolve() == root.resolve():
                        continue

                    p = child / ".env"
                    # Cheap “does it contain a key?” pre-scan without parsing everything.
                    try:
                        if not p.exists() or not p.is_file():
                            continue
                        txt = p.read_text(encoding="utf-8", errors="replace")
                        if "OPENROUTER_API_KEY" not in txt and "OPENAI_API_KEY" not in txt:
                            continue
                    except Exception:
                        continue

                    load_file(p)
                    if has_any_key():
                        break
            except Exception:
                # Never block; just give up.
                pass


def repo_root() -> Path:
    return Path(sh("git", "rev-parse", "--show-toplevel"))


def staged_paths(root: Path) -> list[Path]:
    out = subprocess.check_output(
        ["git", "diff", "--cached", "--name-only", "--diff-filter=ACMRT"],
        text=True,
    )
    paths: list[Path] = []
    for line in out.splitlines():
        line = line.strip()
        if not line:
            continue
        p = (root / line).resolve()
        if p.exists() and p.is_file():
            paths.append(p)
    return paths


def staged_diff() -> str:
    # Keep this bounded; it is easy to overflow context.
    # (We use max_total_bytes at the prompt-assembly layer as the hard cap.)
    return subprocess.check_output(["git", "diff", "--cached"], text=True)


def all_review_paths(root: Path) -> list[Path]:
    # Keep this narrow; avoid build artifacts and archives.
    globs = [
        "README.md",
        "PROOF_ROADMAP.md",
        "doc/**/*.md",
        "docs/**/*.md",
        "Covolume/**/*.lean",
        "Experiments/**/*.lean",
        "Scripts/**/*.lean",
        "Scripts/**/*.sh",
        ".github/workflows/*.yml",
        ".github/workflows/*.yaml",
    ]
    out: list[Path] = []
    for g in globs:
        out.extend(sorted(root.glob(g)))
    # De-dup while preserving order.
    seen: set[Path] = set()
    uniq: list[Path] = []
    for p in out:
        rp = p.resolve()
        if rp in seen:
            continue
        if rp.is_file():
            seen.add(rp)
            uniq.append(rp)
    return uniq


@dataclass(frozen=True)
class FileBlob:
    rel: str
    bytes_len: int
    sha256: str
    content: str
    truncated: bool


def read_blob(p: Path, root: Path, max_bytes: int) -> FileBlob:
    raw = p.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    truncated = len(raw) > max_bytes
    raw2 = raw[:max_bytes]
    text = raw2.decode("utf-8", errors="replace")
    rel = str(p.relative_to(root))
    return FileBlob(
        rel=rel,
        bytes_len=len(raw),
        sha256=digest,
        content=text,
        truncated=truncated,
    )


def assemble_corpus(blobs: Iterable[FileBlob], max_total_bytes: int) -> tuple[str, int]:
    total = 0
    chunks: list[str] = []
    for b in blobs:
        header = (
            f"===== {b.rel} (bytes={b.bytes_len}, sha256={b.sha256}"
            + (", TRUNCATED" if b.truncated else "")
            + ") =====\n"
        )
        body = b.content
        piece = header + body + ("\n" if not body.endswith("\n") else "") + "\n"
        piece_bytes = len(piece.encode("utf-8"))
        if total + piece_bytes > max_total_bytes:
            break
        chunks.append(piece)
        total += piece_bytes
    return "".join(chunks), total


def cache_dir(root: Path) -> Path:
    d = root / ".git" / "llm_review_cache"
    d.mkdir(parents=True, exist_ok=True)
    return d


def cache_key(*, model: str, scope: str, diff_txt: str, blobs: list[FileBlob]) -> str:
    h = hashlib.sha256()
    h.update(model.encode("utf-8"))
    h.update(b"\0")
    h.update(scope.encode("utf-8"))
    h.update(b"\0")
    h.update(diff_txt.encode("utf-8"))
    h.update(b"\0")
    for b in blobs:
        h.update(b.rel.encode("utf-8"))
        h.update(b"\0")
        h.update(b.sha256.encode("utf-8"))
        h.update(b"\0")
    return h.hexdigest()


def domain_prompt() -> str:
    return """You are doing a pre-commit review of a Lean 4 / mathlib project implementing
geometry-of-numbers tooling for Ankeny (1957) + Minkowski, with supporting number theory
(Cauchy polygonal reduction).

Be adversarial and highly opinionated. Your job is to catch the kinds of mistakes that:
- compile today but break on mathlib updates,
- introduce proof fragility via `simp`/defeq coercions,
- indicate missing hypotheses (positivity/invertibility) that the math relies on,
- make the project read like it doesn't understand Lean or the domain.

Strong priors (apply them):
- Prefer proof terms that match mathlib idioms (short lemmas, stable goal shapes).
- Large `simp [...]` sets with comm/assoc lemmas are a smell: prefer `ring_nf`, `nlinarith`, or a
  dedicated lemma.
- If coercions/definitional equality are the blocker, introduce a named lemma that fixes the type
  presentation once (e.g. `Fin 3 → ℝ` vs `EuclideanSpace ℝ (Fin 3)`).
- Keep `Scripts/` (capital S) as canonical; call out casing/paths that will break on Linux.

Focus areas:
1) Lean / mathlib hygiene (fragility, casts, simp misuse, typeclass gotchas)
2) Mathematical coherence (hypotheses, invariants, goal alignment)
3) Repo coherence (README/docs vs reality, scaffolds clearly marked, naming consistency)

Constraints:
   - Some files are scaffolds and contain `sorry` intentionally, especially under Experiments/.
   - Prefer small, concrete edits that reduce future proof friction.

Output format:
   - Top issues (each must include: file path, quote/snippet anchor, and a concrete edit)
   - Then "Nice-to-have"
   - Then "Most likely future break" (1–3 bullets: where/why).
"""


def openai_chat(
    *,
    base_url: str,
    api_key: str,
    model: str,
    system: str,
    user: str,
    timeout_s: int,
    extra_headers: dict[str, str] | None = None,
) -> str:
    url = base_url.rstrip("/") + "/chat/completions"
    headers = {"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"}
    if extra_headers:
        headers.update(extra_headers)
    payload = {
        "model": model,
        "temperature": 0.2,
        "messages": [
            {"role": "system", "content": system},
            {"role": "user", "content": user},
        ],
    }
    r = requests.post(url, headers=headers, json=payload, timeout=timeout_s)
    r.raise_for_status()
    data = r.json()
    return data["choices"][0]["message"]["content"]


def default_openrouter_model() -> str:
    """
    Opinionated defaults for OpenRouter.

    Rationale:
    - pre-commit should be usable by default (latency/cost bounded)
    - allow opting into heavier models without editing scripts

    Controls:
    - OPENROUTER_MODEL: explicit override
    - COVOLUME_LLM_REVIEW_TIER: fast|balanced|heavy
    """

    # Explicit override wins.
    m = os.environ.get("OPENROUTER_MODEL", "").strip()
    if m:
        return m

    tier = os.environ.get("COVOLUME_LLM_REVIEW_TIER", "balanced").strip().lower()
    if tier == "heavy":
        # Dedicated coding/review model (higher cost).
        return "openai/gpt-5.2-codex"
    if tier == "fast":
        return "openai/gpt-4o-mini"
    # balanced: prefer a slightly stronger general model if available.
    return "openai/gpt-4.1-mini"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", choices=["staged", "all"], default="staged")
    ap.add_argument("--include-diff", action="store_true", default=True)
    ap.add_argument("--no-include-diff", dest="include_diff", action="store_false")
    ap.add_argument("--max-bytes-per-file", type=int, default=12_000)
    ap.add_argument("--max-total-bytes", type=int, default=220_000)
    ap.add_argument("--timeout-s", type=int, default=60)
    ap.add_argument("--provider", choices=["auto", "openrouter", "openai"], default="auto")
    ap.add_argument("--base-url", default="")
    ap.add_argument("--model", default="")
    ap.add_argument("--doctor", action="store_true", help="Print provider/model/base_url selection and exit.")
    ap.add_argument(
        "--require-key",
        action="store_true",
        help="Exit nonzero if no provider API key is configured.",
    )
    args = ap.parse_args()

    root = repo_root()
    load_dotenv_if_present(root)

    openrouter_key = os.environ.get("OPENROUTER_API_KEY", "").strip()
    openai_key = os.environ.get("OPENAI_API_KEY", "").strip()

    # Doctor mode should be able to run even when no keys exist.
    if args.doctor:
        chosen = args.provider
        if chosen == "auto":
            if openrouter_key:
                chosen = "openrouter"
            elif openai_key:
                chosen = "openai"
            else:
                chosen = "none"

        if chosen == "openrouter":
            base_url = args.base_url or os.environ.get("OPENROUTER_BASE_URL", "https://openrouter.ai/api/v1")
            model = args.model or default_openrouter_model()
        elif chosen == "openai":
            base_url = args.base_url or os.environ.get("OPENAI_BASE_URL", "https://api.openai.com/v1")
            model = args.model or os.environ.get("OPENAI_MODEL", "gpt-4o-mini")
        else:
            base_url = args.base_url or ""
            model = args.model or ""

        print(f"provider_request={args.provider}")
        print(f"provider_selected={chosen}")
        print(f"openrouter_key_present={bool(openrouter_key)}")
        print(f"openai_key_present={bool(openai_key)}")
        print(f"model={model}")
        print(f"base_url={base_url}")
        return 0

    provider = args.provider
    if provider == "auto":
        if openrouter_key:
            provider = "openrouter"
        elif openai_key:
            provider = "openai"
        else:
            if args.require_key:
                print("llm_review: no OPENROUTER_API_KEY or OPENAI_API_KEY", file=sys.stderr)
                return 2
            print("llm_review: no OPENROUTER_API_KEY or OPENAI_API_KEY; skipping", file=sys.stderr)
            return 0

    if provider == "openrouter":
        api_key = openrouter_key
        if not api_key:
            if args.require_key:
                print("llm_review: OPENROUTER_API_KEY not set", file=sys.stderr)
                return 2
            print("llm_review: OPENROUTER_API_KEY not set; skipping", file=sys.stderr)
            return 0
        base_url = args.base_url or os.environ.get("OPENROUTER_BASE_URL", "https://openrouter.ai/api/v1")
        model = args.model or default_openrouter_model()
        extra_headers: dict[str, str] = {}
        site_url = os.environ.get("OPENROUTER_SITE_URL", "").strip()
        app_name = os.environ.get("OPENROUTER_APP_NAME", "").strip()
        if site_url:
            extra_headers["HTTP-Referer"] = site_url
        if app_name:
            extra_headers["X-Title"] = app_name
    else:
        api_key = openai_key
        if not api_key:
            if args.require_key:
                print("llm_review: OPENAI_API_KEY not set", file=sys.stderr)
                return 2
            print("llm_review: OPENAI_API_KEY not set; skipping", file=sys.stderr)
            return 0
        base_url = args.base_url or os.environ.get("OPENAI_BASE_URL", "https://api.openai.com/v1")
        model = args.model or os.environ.get("OPENAI_MODEL", "gpt-4o-mini")
        extra_headers = None

    if args.scope == "staged":
        paths = staged_paths(root)
        # Always include top-level docs for coherence checks (cheap, high value).
        for p in [root / "README.md", root / "PROOF_ROADMAP.md"]:
            if p.exists() and p.is_file():
                if p not in paths:
                    paths.append(p)
    else:
        paths = all_review_paths(root)

    blobs = [read_blob(p, root, args.max_bytes_per_file) for p in paths]
    corpus, used = assemble_corpus(blobs, args.max_total_bytes)

    diff_txt = ""
    if args.scope == "staged" and args.include_diff:
        diff_txt = staged_diff()

    key_id = cache_key(model=model, scope=args.scope, diff_txt=diff_txt, blobs=blobs)
    cache_path = cache_dir(root) / f"{key_id}.txt"
    if cache_path.exists():
        print(cache_path.read_text(encoding="utf-8", errors="replace"))
        return 0

    meta = (
        f"Review scope: {args.scope}\n"
        f"Files included: {len(blobs)}\n"
        f"Bytes included: {used} (max_total_bytes={args.max_total_bytes})\n"
        f"Per-file truncation: max_bytes_per_file={args.max_bytes_per_file}\n"
    )

    diff_block = ""
    if diff_txt.strip():
        diff_block = "===== git diff --cached =====\n" + diff_txt + "\n\n"

    user_prompt = meta + "\n" + diff_block + corpus

    try:
        out = openai_chat(
            base_url=base_url,
            api_key=api_key,
            model=model,
            system=domain_prompt(),
            user=user_prompt,
            timeout_s=args.timeout_s,
            extra_headers=extra_headers,
        )
    except Exception as e:
        # If a default OpenRouter model is unavailable, fall back once to a safer model id.
        # This is deliberately narrow: we only retry for OpenRouter with an implicit default.
        msg = str(e)
        can_fallback = (
            provider == "openrouter"
            and not args.model
            and not os.environ.get("OPENROUTER_MODEL", "").strip()
            and model != "openai/gpt-4o-mini"
        )
        if can_fallback:
            try:
                out = openai_chat(
                    base_url=base_url,
                    api_key=api_key,
                    model="openai/gpt-4o-mini",
                    system=domain_prompt(),
                    user=user_prompt,
                    timeout_s=args.timeout_s,
                    extra_headers=extra_headers,
                )
            except Exception as e2:
                print(f"llm_review: request failed: {e2}", file=sys.stderr)
                return 1
        else:
            print(f"llm_review: request failed: {msg}", file=sys.stderr)
            return 1

    try:
        cache_path.write_text(out, encoding="utf-8")
    except Exception:
        # Cache failures should never block.
        pass

    print(out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

