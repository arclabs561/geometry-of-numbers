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
  OPENAI_API_KEY=... uv run Scripts/llm_review.py --scope staged

To disable from `Scripts/check.sh pre-commit`:
  COVOLUME_LLM_REVIEW=0

OpenAI-compatible API:
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
) -> str:
    url = base_url.rstrip("/") + "/chat/completions"
    headers = {"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"}
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


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", choices=["staged", "all"], default="staged")
    ap.add_argument("--include-diff", action="store_true", default=True)
    ap.add_argument("--no-include-diff", dest="include_diff", action="store_false")
    ap.add_argument("--max-bytes-per-file", type=int, default=12_000)
    ap.add_argument("--max-total-bytes", type=int, default=220_000)
    ap.add_argument("--timeout-s", type=int, default=60)
    ap.add_argument("--base-url", default=os.environ.get("OPENAI_BASE_URL", "https://api.openai.com/v1"))
    ap.add_argument("--model", default=os.environ.get("OPENAI_MODEL", "gpt-4o-mini"))
    args = ap.parse_args()

    key = os.environ.get("OPENAI_API_KEY", "").strip()
    if not key:
        print("llm_review: OPENAI_API_KEY not set; skipping", file=sys.stderr)
        return 0

    root = repo_root()
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

    key_id = cache_key(model=args.model, scope=args.scope, diff_txt=diff_txt, blobs=blobs)
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
            base_url=args.base_url,
            api_key=key,
            model=args.model,
            system=domain_prompt(),
            user=user_prompt,
            timeout_s=args.timeout_s,
        )
    except Exception as e:
        print(f"llm_review: request failed: {e}", file=sys.stderr)
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

