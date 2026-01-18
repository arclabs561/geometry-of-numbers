#!/usr/bin/env python3
# /// script
# requires-python = ">=3.11"
# dependencies = ["requests", "pydantic", "pydantic-ai", "openai"]
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
import asyncio
import hashlib
import json
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Literal
from typing import Iterable

import requests
from pydantic import BaseModel, Field
from pydantic_ai import Agent
from pydantic_ai.models.openai import OpenAIChatModel
from pydantic_ai.providers.openai import OpenAIProvider
from pydantic_ai.models.openrouter import OpenRouterModel
from pydantic_ai.providers.openrouter import OpenRouterProvider


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
   - This repo intentionally uses `Scripts/` (capital S). Do not suggest renaming it to `scripts/`.

Output format:
   - Top issues (each must include: file path, quote/snippet anchor, and a concrete edit)
   - Then "Nice-to-have"
   - Then "Most likely future break" (1–3 bullets: where/why).
"""


def repo_wisdom(root: Path, *, max_bytes: int = 12_000) -> str:
    """
    Small dynamic injection of repo policy.

    Goal: prevent generic “ecosystem advice” that contradicts this repo.
    We keep this intentionally short to avoid blowing token budgets.
    """
    candidates = [
        root / ".cursor" / "rules" / "polygonal-number-theorem.mdc",
        root / ".cursor" / "rules" / "markdown-math-and-lint-triage.mdc",
    ]
    chunks: list[str] = []
    total = 0
    for p in candidates:
        try:
            if not p.exists() or not p.is_file():
                continue
            txt = p.read_text(encoding="utf-8", errors="replace")
            piece = f"\n===== REPO_WISDOM {p.relative_to(root)} =====\n{txt}\n"
            b = len(piece.encode("utf-8"))
            if total + b > max_bytes:
                break
            chunks.append(piece)
            total += b
        except Exception:
            continue
    return "".join(chunks).strip()


class ReviewIssue(BaseModel):
    severity: Literal["blocker", "high", "medium", "low", "nit"] = "medium"
    file_path: str | None = None
    snippet_anchor: str = Field(
        description="Short quote/snippet (or anchor phrase) identifying the location."
    )
    concrete_edit: str = Field(description="A specific suggested edit, not general advice.")
    rationale: str = Field(description="Why this matters (fragility, missing hypothesis, etc).")
    confidence: float = Field(ge=0.0, le=1.0, default=0.6)
    tags: list[str] = Field(default_factory=list)


class ReviewReport(BaseModel):
    top_issues: list[ReviewIssue] = Field(default_factory=list)
    nice_to_have: list[str] = Field(default_factory=list)
    most_likely_future_break: list[str] = Field(default_factory=list)
    meta: list[str] = Field(default_factory=list)


def _severity_weight(sev: str) -> int:
    return {
        "blocker": 50,
        "high": 20,
        "medium": 10,
        "low": 5,
        "nit": 1,
    }.get(sev, 10)


def _is_policy_conflict(issue: ReviewIssue) -> bool:
    txt = (issue.concrete_edit + "\n" + issue.rationale).lower()
    # The model frequently “helpfully” suggests this, but it's explicitly wrong here.
    # Repo policy: `Scripts/` is canonical and intentionally capitalized.
    if "rename" in txt and "`scripts/`" in txt:
        return True
    if "rename" in txt and "scripts/" in txt and "capital" in txt:
        return True
    if "standardize" in txt and "`scripts/`" in txt:
        return True
    return False


def role_prompts() -> dict[str, str]:
    """
    Role-specific deltas appended to the base system prompt.

    Enable multiple roles with:
      COVOLUME_LLM_REVIEW_ROLES=lean,math,repo
    """
    return {
        "default": (
            "ROLE: Blended reviewer.\n"
            "- Cover Lean hygiene, mathematical coherence, and repo coherence.\n"
            "- Prefer concrete edits over general advice.\n"
        ),
        "lean": (
            "ROLE: Lean hygiene.\n"
            "- Prefer issues that mention a specific lemma/definition and a concrete rewrite.\n"
            "- Prioritize: simp fragility, casts, defeq coercions, typeclass inference risks.\n"
        ),
        "math": (
            "ROLE: Mathematical coherence.\n"
            "- Prioritize: missing hypotheses, incorrect quantifiers, wrong domains (ℕ/ℤ/ℝ), nontriviality.\n"
            "- If a step is called “trivial”, demand the exact lemma/inequality used.\n"
        ),
        "repo": (
            "ROLE: Repo coherence.\n"
            "- Prioritize: docs diverging from code, scaffolds unclear, stale paths, misleading claims.\n"
            "- Do NOT suggest renaming Scripts/.\n"
        ),
    }


def aggregate_reports(reports: list[tuple[str, ReviewReport]]) -> ReviewReport:
    """
    Merge multiple model reports into a single report with light consensus weighting.

    We intentionally keep this heuristic and transparent.
    """
    # Key by (file, snippet_anchor prefix) to dedup near-identical issues.
    buckets: dict[tuple[str, str], list[tuple[str, ReviewIssue]]] = {}
    policy_conflicts: list[tuple[str, ReviewIssue]] = []

    for model_id, rep in reports:
        for iss in rep.top_issues:
            if _is_policy_conflict(iss):
                policy_conflicts.append((model_id, iss))
                continue
            fp = (iss.file_path or "").strip()
            anchor = iss.snippet_anchor.strip()
            key = (fp, anchor[:120])
            buckets.setdefault(key, []).append((model_id, iss))

    merged: list[ReviewIssue] = []
    for (_fp, _anch), xs in buckets.items():
        # choose representative: max severity, then highest confidence
        xs_sorted = sorted(xs, key=lambda t: (_severity_weight(t[1].severity), t[1].confidence), reverse=True)
        rep_issue = xs_sorted[0][1]
        votes = len(xs)
        rep_issue = ReviewIssue(
            severity=rep_issue.severity,
            file_path=rep_issue.file_path,
            snippet_anchor=rep_issue.snippet_anchor,
            concrete_edit=rep_issue.concrete_edit,
            rationale=rep_issue.rationale,
            confidence=min(1.0, rep_issue.confidence + 0.1 * (votes - 1)),
            tags=sorted(set(rep_issue.tags + [f"votes:{votes}"])),
        )
        merged.append(rep_issue)

    merged.sort(key=lambda i: (_severity_weight(i.severity), i.confidence), reverse=True)

    out = ReviewReport(
        top_issues=merged[:10],
        nice_to_have=[],
        most_likely_future_break=[],
        meta=[],
    )

    if policy_conflicts:
        out.meta.append(
            "Dropped policy-conflicting suggestions (e.g. renaming `Scripts/`); see per-model output for details."
        )
    return out


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


def _parse_models_env(env_value: str) -> list[str]:
    xs = [x.strip() for x in env_value.split(",") if x.strip()]
    # De-dup preserving order.
    out: list[str] = []
    seen: set[str] = set()
    for x in xs:
        if x in seen:
            continue
        seen.add(x)
        out.append(x)
    return out


def default_models_for_provider(provider: str, *, stage: str) -> list[str]:
    """
    Choose a model ensemble for the given provider.

    Overrides:
    - COVOLUME_LLM_REVIEW_MODELS_<STAGE>: comma-separated model ids for that stage
    - COVOLUME_LLM_REVIEW_MODELS: comma-separated model ids
    - OPENROUTER_MODEL / OPENAI_MODEL: single-model override (provider-specific)
    - COVOLUME_LLM_REVIEW_TIER: fast|balanced|heavy (OpenRouter only for now)
    """
    stage_key = f"COVOLUME_LLM_REVIEW_MODELS_{stage.upper()}"
    explicit = os.environ.get(stage_key, "").strip()
    if explicit:
        return _parse_models_env(explicit)[:8]

    explicit = os.environ.get("COVOLUME_LLM_REVIEW_MODELS", "").strip()
    if explicit:
        return _parse_models_env(explicit)[:8]

    if provider == "openrouter":
        tier = os.environ.get("COVOLUME_LLM_REVIEW_TIER", "balanced").strip().lower()
        if tier == "heavy":
            # Stage-aware defaults:
            # - triage: fast-ish frontier models (still “big”), no need for max depth
            # - deep: full ensemble
            if stage == "triage":
                return [
                    "anthropic/claude-opus-4.5",
                    "openai/gpt-4.1-mini",
                ]
            return [
                "openai/gpt-5.2-codex",
                "anthropic/claude-opus-4.5",
                "google/gemini-3-pro-preview",
            ]
        if tier == "fast":
            return ["openai/gpt-4o-mini"]
        return ["openai/gpt-4.1-mini"]

    # OpenAI direct: keep conservative.
    m = os.environ.get("OPENAI_MODEL", "").strip()
    return [m] if m else ["gpt-4o-mini"]


def format_report(rep: ReviewReport) -> str:
    def fmt_issue(i: ReviewIssue, k: int) -> str:
        fp = i.file_path or "(no file)"
        sev = i.severity
        conf = f"{i.confidence:.2f}"
        tags = f" [{', '.join(i.tags)}]" if i.tags else ""
        return (
            f"{k}. ({sev}, conf={conf}) {fp}{tags}\n"
            f"   Snippet:\n"
            f"   ```\n{i.snippet_anchor}\n   ```\n"
            f"   Concrete edit:\n"
            f"   {i.concrete_edit}\n"
            f"   Rationale:\n"
            f"   {i.rationale}\n"
        )

    out: list[str] = []
    if rep.meta:
        out.append("Meta:")
        for m in rep.meta:
            out.append(f"- {m}")
        out.append("")

    out.append("Top issues:")
    if not rep.top_issues:
        out.append("(none)")
    else:
        for idx, iss in enumerate(rep.top_issues, start=1):
            out.append(fmt_issue(iss, idx))

    out.append("Nice-to-have:")
    if not rep.nice_to_have:
        out.append("(none)")
    else:
        for s in rep.nice_to_have:
            out.append(f"- {s}")

    out.append("")
    out.append("Most likely future break:")
    if not rep.most_likely_future_break:
        out.append("(none)")
    else:
        for s in rep.most_likely_future_break:
            out.append(f"- {s}")
    return "\n".join(out).rstrip() + "\n"


async def run_one_report(
    *,
    provider: str,
    model_id: str,
    api_key: str,
    base_url: str,
    app_url: str,
    app_title: str,
    system_prompt: str,
    user_prompt: str,
    timeout_s: int,
) -> ReviewReport:
    def extract_json_object(s: str) -> str:
        """
        Best-effort extraction of a single top-level JSON object from a text response.

        This is for “JSON mode” prompts where models sometimes add prose before/after.
        """
        i = s.find("{")
        j = s.rfind("}")
        if i == -1 or j == -1 or j <= i:
            raise ValueError("no JSON object delimiters found")
        return s[i : j + 1]

    # Gemini models on OpenRouter currently have tool/function-calling constraints
    # (thought_signature / reasoning-details preservation) that break structured tool calling.
    # Workaround: use plain JSON output (no tools) and parse locally.
    if provider == "openrouter" and model_id.startswith("google/gemini-"):
        schema_hint = """
Return a single JSON object (no surrounding prose) of the form:
{
  "top_issues": [
    {
      "severity": "blocker|high|medium|low|nit",
      "file_path": "path or null",
      "snippet_anchor": "short quote or anchor",
      "concrete_edit": "specific edit",
      "rationale": "why",
      "confidence": 0.0-1.0,
      "tags": ["..."]
    }
  ],
  "nice_to_have": ["..."],
  "most_likely_future_break": ["..."],
  "meta": ["..."]
}
"""
        # We intentionally do NOT include any function/tool calling. Just JSON.
        txt = openai_chat(
            base_url=base_url,
            api_key=api_key,
            model=model_id,
            system=system_prompt + "\n\n" + schema_hint,
            user=user_prompt,
            timeout_s=timeout_s,
            extra_headers={
                **({"HTTP-Referer": app_url} if app_url else {}),
                **({"X-Title": app_title} if app_title else {}),
            }
            or None,
        )
        try:
            return ReviewReport.model_validate_json(txt)
        except Exception:
            try:
                obj_txt = extract_json_object(txt)
                return ReviewReport.model_validate(json.loads(obj_txt))
            except Exception as e:
                # Return a structured error instead of crashing the whole reviewer.
                tail = txt[-800:] if isinstance(txt, str) else ""
                return ReviewReport(
                    meta=[
                        f"gemini_json_parse_failed: {type(e).__name__}: {e!r}",
                        "gemini_raw_tail(last_800_chars):",
                        tail,
                    ]
                )

    # Default: pydantic-ai structured output (uses tool calling internally).
    if provider == "openrouter":
        model = OpenRouterModel(
            model_id,
            provider=OpenRouterProvider(
                api_key=api_key,
                app_url=app_url or None,
                app_title=app_title or None,
            ),
        )
    else:
        model = OpenAIChatModel(
            model_id,
            provider=OpenAIProvider(
                base_url=base_url,
                api_key=api_key,
            ),
        )

    agent = Agent(model, output_type=ReviewReport, system_prompt=system_prompt)
    # Hard timeout at the coroutine level.
    res = await asyncio.wait_for(agent.run(user_prompt), timeout=timeout_s)
    return res.output


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
    ap.add_argument("--stage", choices=["triage", "deep", "both"], default="")
    ap.add_argument("--roles", default="")
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
        # For pydantic-ai, we use OpenRouterProvider which handles attribution headers.
        site_url = os.environ.get("OPENROUTER_SITE_URL", "").strip()
        app_name = os.environ.get("OPENROUTER_APP_NAME", "").strip()
    else:
        api_key = openai_key
        if not api_key:
            if args.require_key:
                print("llm_review: OPENAI_API_KEY not set", file=sys.stderr)
                return 2
            print("llm_review: OPENAI_API_KEY not set; skipping", file=sys.stderr)
            return 0
        base_url = args.base_url or os.environ.get("OPENAI_BASE_URL", "https://api.openai.com/v1")
        # Model selection is handled below.
        site_url = ""
        app_name = ""

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

    meta = (
        f"Review scope: {args.scope}\n"
        f"Files included: {len(blobs)}\n"
        f"Bytes included: {used} (max_total_bytes={args.max_total_bytes})\n"
        f"Per-file truncation: max_bytes_per_file={args.max_bytes_per_file}\n"
    )

    diff_block = ""
    if diff_txt.strip():
        diff_block = "===== git diff --cached =====\n" + diff_txt + "\n\n"

    stage = args.stage.strip().lower() or os.environ.get("COVOLUME_LLM_REVIEW_STAGE", "").strip().lower()
    if stage not in ("triage", "deep", "both"):
        # Default: keep pre-commit fast.
        stage = "triage" if args.scope == "staged" else "deep"

    # Default ensemble can depend on stage; if --model is specified, it applies to both stages.
    models_override = [args.model.strip()] if args.model.strip() else []
    concurrency_default = int(os.environ.get("COVOLUME_LLM_REVIEW_CONCURRENCY", "3").strip() or "3")
    timeout_default = int(os.environ.get("COVOLUME_LLM_REVIEW_TIMEOUT_S", str(args.timeout_s)).strip() or str(args.timeout_s))

    system = domain_prompt()
    wisdom = repo_wisdom(root)
    if wisdom:
        system = system + "\n\n" + wisdom

    role_cfg = args.roles.strip() or os.environ.get("COVOLUME_LLM_REVIEW_ROLES", "").strip()
    role_map = role_prompts()
    if role_cfg:
        roles = [r.strip() for r in role_cfg.split(",") if r.strip()]
        # Filter to known roles; keep order.
        roles = [r for r in roles if r in role_map]
        if not roles:
            roles = ["lean", "math", "repo"]
    else:
        # Default: single blended reviewer (fast).
        roles = ["default"]

    # Stage prompts.
    triage_prompt = (
        meta
        + "\n"
        + diff_block
        + "===== FILE LIST =====\n"
        + "\n".join(f"- {b.rel}" for b in blobs)
        + "\n"
        + "\n\nTRIAGE MODE:\n"
        + "- You do NOT have full file contents.\n"
        + "- Do NOT complain about missing content.\n"
        + "- Only report issues you can justify from the diff or file list.\n"
        + "- If you must recommend a deeper check, express it as a concrete follow-up action, not as a complaint.\n"
        + "\n(Do not ask questions. Propose edits.)\n"
    )
    deep_prompt = meta + "\n" + diff_block + corpus

    async def run_stage(stage_name: str, user_prompt: str) -> ReviewReport:
        reports: list[tuple[str, ReviewReport]] = []
        stage_timeout = int(os.environ.get(f"COVOLUME_LLM_REVIEW_TIMEOUT_S_{stage_name.upper()}", str(timeout_default)).strip() or str(timeout_default))
        stage_concurrency = int(os.environ.get(f"COVOLUME_LLM_REVIEW_CONCURRENCY_{stage_name.upper()}", str(concurrency_default)).strip() or str(concurrency_default))
        sem = asyncio.Semaphore(max(1, stage_concurrency))
        models = models_override or default_models_for_provider(provider, stage=stage_name)

        async def run_model(m: str, role: str) -> tuple[str, ReviewReport] | None:
            key_id = cache_key(
                model=f"{provider}:{m}:{stage_name}:role={role}",
                scope=args.scope,
                diff_txt=diff_txt,
                blobs=blobs,
            )
            cache_path = cache_dir(root) / f"{key_id}.json"
            if cache_path.exists():
                try:
                    rep = ReviewReport.model_validate_json(cache_path.read_text(encoding="utf-8", errors="replace"))
                    if role != "default":
                        for iss in rep.top_issues:
                            iss.tags = sorted(set(iss.tags + [f"role:{role}"]))
                    return (m, rep)
                except Exception:
                    pass

            async with sem:
                try:
                    sys2 = system if role == "default" else (system + "\n\n" + role_map[role])
                    rep = await run_one_report(
                        provider=provider,
                        model_id=m,
                        api_key=api_key,
                        base_url=base_url,
                        app_url=site_url,
                        app_title=app_name,
                        system_prompt=sys2,
                        user_prompt=user_prompt,
                        timeout_s=stage_timeout,
                    )
                    if role != "default":
                        for iss in rep.top_issues:
                            iss.tags = sorted(set(iss.tags + [f"role:{role}"]))
                    try:
                        cache_path.write_text(rep.model_dump_json(indent=2), encoding="utf-8")
                    except Exception:
                        pass
                    return (m, rep)
                except Exception as e:
                    # Non-blocking: missing model / transient error shouldn't break pre-commit.
                    print(
                        f"llm_review: model_failed model={m} stage={stage_name} role={role}: {type(e).__name__}: {e!r}",
                        file=sys.stderr,
                    )
                    return None

        # Role x model grid, concurrent with a semaphore.
        xs = await asyncio.gather(*(run_model(m, role) for role in roles for m in models))
        for x in xs:
            if x is not None:
                reports.append(x)

        if not reports:
            return ReviewReport(meta=[f"All models failed for stage={stage_name}."])
        merged = aggregate_reports(reports)
        # Pull through any “nice-to-have” / “future break” content without trying to do semantic dedup.
        nice: list[str] = []
        brk: list[str] = []
        for _, rep in reports:
            nice.extend(rep.nice_to_have)
            brk.extend(rep.most_likely_future_break)
        merged.nice_to_have = list(dict.fromkeys(nice))[:20]
        merged.most_likely_future_break = list(dict.fromkeys(brk))[:10]
        return merged

    async def run_pipeline() -> list[ReviewReport]:
        tasks: list[asyncio.Task[ReviewReport]] = []
        if stage in ("triage", "both"):
            tasks.append(asyncio.create_task(run_stage("triage", triage_prompt)))
        if stage in ("deep", "both"):
            tasks.append(asyncio.create_task(run_stage("deep", deep_prompt)))
        if not tasks:
            return []
        return await asyncio.gather(*tasks)

    reps = asyncio.run(run_pipeline())

    final = ReviewReport()
    for r in reps:
        final.top_issues.extend(r.top_issues)
        final.nice_to_have.extend(r.nice_to_have)
        final.most_likely_future_break.extend(r.most_likely_future_break)
        final.meta.extend(r.meta)

    # De-dup combined issues by (file, snippet prefix).
    combined = aggregate_reports([("combined", ReviewReport(top_issues=final.top_issues, meta=final.meta))])
    combined.nice_to_have = list(dict.fromkeys(final.nice_to_have))[:20]
    combined.most_likely_future_break = list(dict.fromkeys(final.most_likely_future_break))[:10]
    combined.meta = list(dict.fromkeys(final.meta))[:20]

    print(format_report(combined))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

