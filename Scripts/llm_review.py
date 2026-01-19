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
  GON_LLM_REVIEW=0

Backwards-compatibility:
- This script historically used `COVOLUME_*` env vars. We still accept them.
- New preferred prefix is `GON_*` (GeometryOfNumbers).

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
import time
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
import re
from typing import Literal
from typing import Iterable

import requests
from pydantic import BaseModel, Field
from pydantic_ai import Agent
from pydantic_ai.models.openai import OpenAIChatModel
from pydantic_ai.providers.openai import OpenAIProvider
from pydantic_ai.models.openrouter import OpenRouterModel
from pydantic_ai.models.openrouter import OpenRouterModelSettings
from pydantic_ai.providers.openrouter import OpenRouterProvider

WORLD_WISDOM = """WORLD KNOWLEDGE (curated, short):

- OpenRouter Models API: GET /models returns a JSON object with `data: [ { id, canonical_slug, context_length,
  pricing, supported_parameters, ... } ]`. Model ids are the strings you pass as `model`.

- OpenRouter reasoning/tool-calling: reasoning-enabled models may return `reasoning_details`. For multi-step
  tool calling, the client must preserve and resend the *exact* `reasoning_details` blocks between steps.

- Gemini 3 (and similar Gemini reasoning models) enforce an additional constraint: function/tool calling can
  fail with 400 errors if `thought_signature` / reasoning-details continuity is not preserved. Many OpenAI-style
  wrappers (and some structured-output libraries) drop these fields. Workaround: avoid tool calling for Gemini
  and request plain JSON, then parse locally.
"""

CACHE_VERSION = "2026-01-18-v4"


def _apply_env_aliases() -> None:
    """
    Accept `GON_*` environment variables as aliases for historical `COVOLUME_*`.

    We do the aliasing early so the rest of the file can continue to use the old names
    without churn.
    """

    pairs = [
        ("GON_LLM_REVIEW_PROGRESS", "COVOLUME_LLM_REVIEW_PROGRESS"),
        ("GON_LLM_REVIEW_PROGRESS_VERBOSITY", "COVOLUME_LLM_REVIEW_PROGRESS_VERBOSITY"),
        ("GON_LLM_REVIEW_PROGRESS_FILE", "COVOLUME_LLM_REVIEW_PROGRESS_FILE"),
        ("GON_LLM_REVIEW_POWER", "COVOLUME_LLM_REVIEW_POWER"),
        ("GON_LLM_REVIEW_TIER", "COVOLUME_LLM_REVIEW_TIER"),
        ("GON_LLM_REVIEW_STRICT", "COVOLUME_LLM_REVIEW_STRICT"),
        ("GON_LLM_REVIEW", "COVOLUME_LLM_REVIEW"),
    ]
    for new, old in pairs:
        nv = os.environ.get(new)
        if nv is not None and os.environ.get(old) in (None, ""):
            os.environ[old] = nv


_apply_env_aliases()


class ProgressEvent(BaseModel):
    """
    Structured progress event (JSONL-friendly).

    This is meant for:
    - live human visibility in pre-commit
    - machine parsing (e.g. feeding into another LLM pass)
    """

    event: str
    ts: str
    phase: Literal[
        "start",
        "context",
        "plan",
        "stage",
        "model",
        "cache",
        "aggregate",
        "done",
        "error",
    ]
    message: str = ""
    stage: str | None = None
    role: str | None = None
    model: str | None = None
    round: int | None = None
    data: dict[str, object] = Field(default_factory=dict)


def _now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def _progress_mode() -> str:
    """
    Progress output control.

    Modes (comma-separated):
    - "pretty": human-readable incremental logs (stderr)
    - "jsonl": emit JSONL progress events (stderr) and optionally write to a file
    - "0"/"off": disable
    """
    v = os.environ.get("COVOLUME_LLM_REVIEW_PROGRESS", "").strip().lower()
    if not v:
        # Default on: pre-commit wants transparency more than silence.
        return "pretty"
    return v


def _progress_pretty_verbosity() -> str:
    """
    Control how much structured data is echoed in the human-readable stream.

    - low: one-line summaries only (default)
    - high: append a compact `k=v` payload for key fields
    """
    v = os.environ.get("COVOLUME_LLM_REVIEW_PROGRESS_VERBOSITY", "").strip().lower()
    if not v:
        # Default to high signal: pre-commit is about understanding what happened.
        return "high"
    if v not in ("low", "high"):
        return "high"
    return v


def _progress_jsonl_path(root: Path) -> Path | None:
    """
    Default to a git-ignored location.
    """
    v = os.environ.get("COVOLUME_LLM_REVIEW_PROGRESS_FILE", "").strip()
    if v:
        try:
            return Path(v)
        except Exception:
            return None
    return root / ".git" / "llm_review_progress.jsonl"


def _jsonl_enabled() -> bool:
    mode = _progress_mode()
    if mode in ("0", "off", "false", "no"):
        return False
    return "jsonl" in mode.split(",")


def _compact_kv(d: dict[str, object], *, max_items: int = 10) -> str:
    """
    Best-effort compact key=value formatter (stable-ish, single-line).
    """
    items: list[str] = []
    for k in sorted(d.keys()):
        v = d.get(k)
        if v is None:
            continue
        if isinstance(v, str):
            s = v
            if len(s) > 120:
                s = s[:120] + "…"
            items.append(f"{k}={s}")
        elif isinstance(v, bool):
            items.append(f"{k}={'1' if v else '0'}")
        elif isinstance(v, (int, float)):
            items.append(f"{k}={v}")
        elif isinstance(v, list):
            # keep short list preview only
            preview = v[:5]
            items.append(f"{k}={preview!r}{'…' if len(v) > 5 else ''}")
        else:
            items.append(f"{k}={str(v)[:80]}")
        if len(items) >= max_items:
            break
    return " ".join(items)


def _estimate_tokens_from_bytes(n_bytes: int) -> int:
    # Very rough heuristic: ~4 bytes per token in typical English/Lean mix.
    return max(1, int(n_bytes / 4))


def emit_progress(root: Path, ev: ProgressEvent) -> None:
    mode = _progress_mode()
    if mode in ("0", "off", "false", "no"):
        return

    # Always include a ts if caller didn't.
    if not ev.ts:
        ev.ts = _now_iso()

    want_pretty = "pretty" in mode.split(",")
    want_jsonl = "jsonl" in mode.split(",")

    if want_pretty:
        parts = [f"llm_review[{ev.phase}]"]
        if ev.stage:
            parts.append(f"stage={ev.stage}")
        if ev.role:
            parts.append(f"role={ev.role}")
        if ev.model:
            parts.append(f"model={ev.model}")
        if ev.round is not None:
            parts.append(f"round={ev.round}")
        hdr = " ".join(parts)
        msg = ev.message.strip()
        if _progress_pretty_verbosity() == "high" and ev.data:
            msg = (msg + " " + _compact_kv(ev.data)).strip()
        if msg:
            print(f"{hdr}: {msg}", file=sys.stderr)
        else:
            print(f"{hdr}", file=sys.stderr)

    if want_jsonl:
        line = ev.model_dump_json()
        print(line, file=sys.stderr)
        try:
            p = _progress_jsonl_path(root)
            if p is not None:
                p.parent.mkdir(parents=True, exist_ok=True)
                with p.open("a", encoding="utf-8") as f:
                    f.write(line + "\n")
        except Exception:
            # progress logging must never block the hook
            pass


class ReviewPlan(BaseModel):
    """
    Small “agentic” plan emitted before deep review.

    Purpose: provide immediate intermediate output that is structured enough to feed into
    another pass (or just to orient a human).
    """

    model_config = {"extra": "ignore"}

    focus_files: list[str] = Field(default_factory=list)
    hypotheses_to_check: list[str] = Field(default_factory=list)
    expected_failure_modes: list[str] = Field(default_factory=list)
    intended_evidence: list[str] = Field(default_factory=list)
    next_actions: list[dict[str, object]] = Field(
        default_factory=list,
        description="Up to 3 concrete next actions, each tied to a focus file + anchor.",
    )
    notes: list[str] = Field(default_factory=list)



def model_blacklist() -> list[str]:
    """
    Return model id patterns to exclude.

    Patterns:
    - exact id match: "x-ai/grok-code-fast-1"
    - prefix match: "x-ai/grok*" (suffix `*`)
    """
    raw = os.environ.get("COVOLUME_LLM_REVIEW_MODEL_BLACKLIST", "").strip()
    if raw:
        xs = [x.strip() for x in raw.split(",") if x.strip()]
        return xs
    # Default policy: exclude Grok variants.
    return ["x-ai/grok*"]


def is_blacklisted_model(model_id: str) -> bool:
    mid = (model_id or "").strip()
    if not mid:
        return False
    for pat in model_blacklist():
        if pat.endswith("*"):
            if mid.startswith(pat[:-1]):
                return True
        else:
            if mid == pat:
                return True
    return False


def is_sensitive_path(root: Path, p: Path) -> bool:
    """
    Defensive filter: never read or send obvious secrets to the LLM.

    Notes:
    - This is intentionally conservative.
    - It applies to *all* scopes, including `--scope staged`.
      (If you staged a secret, this tool should not exfiltrate it.)
    """
    try:
        rel = p.resolve().relative_to(root.resolve())
        parts = [x.lower() for x in rel.parts]
    except Exception:
        parts = [x.lower() for x in p.parts]

    if any(x in (".git", ".lake", "lake-packages") for x in parts):
        return True

    name = p.name.lower()
    if name == ".env" or name.startswith(".env."):
        return True
    if name in (".envrc",):
        return True
    if "id_rsa" in name or "id_ed25519" in name:
        return True
    if name.endswith((".pem", ".key", ".p12", ".pfx", ".gpg", ".asc")):
        return True

    # Binary-ish / likely unhelpful for text review (also often contains embedded data).
    if p.suffix.lower() in (".pdf", ".png", ".jpg", ".jpeg", ".gif", ".webp", ".zip", ".gz", ".xz", ".bz2"):
        return True

    return False


def filter_review_paths(root: Path, paths: list[Path]) -> list[Path]:
    out: list[Path] = []
    for p in paths:
        try:
            rp = p.resolve()
        except Exception:
            rp = p
        if is_sensitive_path(root, rp):
            continue
        out.append(rp)
    return out


def sh(*args: str) -> str:
    return subprocess.check_output(list(args), text=True).strip()


def sh_timeout(args: list[str], *, timeout_s: float) -> str:
    """
    Best-effort shell helper for local probes.

    Never raise: callers should treat empty output as “unavailable”.
    """
    try:
        r = subprocess.run(args, text=True, capture_output=True, timeout=timeout_s)
        if r.returncode != 0:
            return ""
        return (r.stdout or "").strip()
    except Exception:
        return ""


def lake_path() -> str:
    """
    Resolve `lake` in a way that works in non-interactive shells.

    Order:
    - env override `LAKE=...`
    - ~/.elan/bin/lake (common for elan installs)
    - fallback "lake"
    """
    v = os.environ.get("LAKE", "").strip()
    if v:
        return v
    p = Path.home() / ".elan" / "bin" / "lake"
    if p.exists() and p.is_file():
        return str(p)
    return "lake"


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


def load_cursor_mcp_env_if_present() -> None:
    """
    Best-effort loader for Cursor MCP env blocks (local convenience).

    Reads `~/.cursor/mcp.json` and merges `mcpServers.*.env` keys into the current process env
    *only if they are not already set*.

    Notes:
    - Never prints secrets.
    - Only merges explicit `env` blocks (does NOT parse tokens embedded in URLs/args).
    - Never blocks: failures are silently ignored.
    """
    try:
        p = Path.home() / ".cursor" / "mcp.json"
        if not p.exists() or not p.is_file():
            return
        data = json.loads(p.read_text(encoding="utf-8", errors="replace"))
        servers = (data or {}).get("mcpServers", {}) or {}
        if not isinstance(servers, dict):
            return
        for _, cfg in servers.items():
            if not isinstance(cfg, dict):
                continue
            env = cfg.get("env", {}) or {}
            if not isinstance(env, dict):
                continue
            for k, v in env.items():
                if not isinstance(k, str) or not isinstance(v, str):
                    continue
                if k in os.environ:
                    continue
                os.environ[k] = v
    except Exception:
        return


def _redact_secrets(s: str) -> str:
    """
    Best-effort redaction for obvious secret patterns.

    Goal: when we include local transcript tails into LLM prompts, avoid leaking tokens.
    This is not perfect; it targets the common cases.
    """
    if not s:
        return s
    s = re.sub(r"(OPENROUTER_API_KEY|OPENAI_API_KEY)\s*=\s*[^\s]+", r"\1=[REDACTED]", s)
    s = re.sub(r"(Authorization:\s*Bearer)\s+[^\s]+", r"\1 [REDACTED]", s, flags=re.IGNORECASE)
    s = re.sub(r"\b(sk-[A-Za-z0-9_\-]{16,})\b", "[REDACTED_TOKEN]", s)
    return s


def agent_transcript_tail(*, max_bytes: int = 24_000) -> str:
    """
    Include a small tail of the most recent Cursor agent transcript, if present.

    This is best-effort and must never block.
    Disable with: COVOLUME_LLM_REVIEW_INCLUDE_TRANSCRIPT=0
    Override path with: COVOLUME_LLM_REVIEW_TRANSCRIPT_PATH=/abs/path/to/transcript.txt
    """
    try:
        include = os.environ.get("COVOLUME_LLM_REVIEW_INCLUDE_TRANSCRIPT", "1").strip().lower()
        if include in ("0", "false", "no", "off"):
            return ""

        explicit = os.environ.get("COVOLUME_LLM_REVIEW_TRANSCRIPT_PATH", "").strip()
        candidates: list[Path] = []
        if explicit:
            p = Path(explicit)
            if p.exists() and p.is_file():
                candidates.append(p)
        else:
            base = Path.home() / ".cursor" / "projects"
            if base.exists() and base.is_dir():
                candidates.extend(base.glob("**/agent-transcripts/*.txt"))

        if not candidates:
            return ""
        candidates.sort(key=lambda p: p.stat().st_mtime, reverse=True)
        p = candidates[0]
        raw = p.read_bytes()
        tail = raw[-max_bytes:]
        txt = tail.decode("utf-8", errors="replace")
        txt = _redact_secrets(txt)
        return f"===== AGENT_TRANSCRIPT_TAIL {p.name} (bytes={len(raw)}, tail_bytes={len(tail)}) =====\n{txt}\n"
    except Exception:
        return ""


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
    return filter_review_paths(root, paths)


def unstaged_paths(root: Path) -> list[Path]:
    out = subprocess.check_output(
        ["git", "diff", "--name-only", "--diff-filter=ACMRT"],
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
    return filter_review_paths(root, paths)


def untracked_paths(root: Path) -> list[Path]:
    out = subprocess.check_output(
        ["git", "ls-files", "--others", "--exclude-standard"],
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
    return filter_review_paths(root, paths)


def worktree_paths(root: Path) -> list[Path]:
    # Deterministic order; de-dupe by resolved path.
    seen: set[Path] = set()
    out: list[Path] = []
    for p in staged_paths(root) + unstaged_paths(root) + untracked_paths(root):
        rp = p.resolve()
        if rp in seen:
            continue
        seen.add(rp)
        out.append(rp)
    return out


def staged_diff() -> str:
    # Keep this bounded; it is easy to overflow context.
    # (We use max_total_bytes at the prompt-assembly layer as the hard cap.)
    return subprocess.check_output(["git", "diff", "--cached"], text=True)


def worktree_diff() -> str:
    # Includes staged + unstaged diffs. This can be noisy, so still subject to prompt size caps.
    staged = subprocess.check_output(["git", "diff", "--cached"], text=True)
    unstaged = subprocess.check_output(["git", "diff"], text=True)
    return staged + ("\n\n" if staged and unstaged else "") + unstaged


def _truncate_utf8(s: str, *, max_bytes: int, label: str) -> str:
    b = s.encode("utf-8")
    if len(b) <= max_bytes:
        return s
    out = b[:max_bytes].decode("utf-8", errors="replace").rstrip()
    out += f"\n\n[TRUNCATED {label}: {len(b)} bytes -> {max_bytes} bytes]\n"
    return out


def lean_file_header(p: Path, *, max_lines: int = 80) -> str:
    """
    Extract enough to support Lean-specific review: module intent + imports.

    Intentionally shallow: no parsing, no build.
    """
    try:
        lines = p.read_text(encoding="utf-8", errors="replace").splitlines()
    except Exception:
        return ""

    out: list[str] = []
    for i, line in enumerate(lines[:max_lines]):
        out.append(line)
        # Stop early once we’re plausibly past imports + the initial comment/doc block.
        if i >= 15 and line.strip() == "" and any(l.strip().startswith("import ") for l in out):
            break
    return "\n".join(out).strip()


def lean_context(root: Path, *, focus_paths: list[Path], max_bytes: int = 7000) -> str:
    """
    Lean-specific context injection (cheap, high-signal).

    Includes:
    - `lean-toolchain`
    - `lake --version`, `lake env lean --version` (best-effort)
    - import headers for changed Lean files
    """
    chunks: list[str] = []

    toolchain = root / "lean-toolchain"
    if toolchain.exists() and toolchain.is_file():
        try:
            tc = toolchain.read_text(encoding="utf-8", errors="replace").strip()
            if tc:
                chunks.append("===== LEAN_TOOLCHAIN =====\n" + tc + "\n")
        except Exception:
            pass

    lake_ver = sh_timeout([lake_path(), "--version"], timeout_s=2.0)
    if lake_ver:
        chunks.append("===== LAKE_VERSION =====\n" + lake_ver + "\n")
    lean_ver = sh_timeout([lake_path(), "env", "lean", "--version"], timeout_s=3.0)
    if lean_ver:
        chunks.append("===== LEAN_VERSION =====\n" + lean_ver + "\n")

    lean_files = [p for p in focus_paths if p.suffix == ".lean"]
    lean_files = sorted({p.resolve() for p in lean_files})[:12]
    for p in lean_files:
        hdr = lean_file_header(p, max_lines=80)
        if not hdr:
            continue
        try:
            rel = str(p.relative_to(root))
        except Exception:
            rel = str(p)
        chunks.append(f"===== LEAN_HEADER {rel} =====\n{hdr}\n")

    out = "\n".join(chunks).strip()
    if not out:
        return ""
    b = out.encode("utf-8")
    if len(b) > max_bytes:
        out = b[:max_bytes].decode("utf-8", errors="replace").rstrip()
        out += "\n\n[TRUNCATED lean_context]\n"
    return out


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
    return filter_review_paths(root, uniq)


@dataclass(frozen=True)
class FileBlob:
    rel: str
    bytes_len: int
    sha256: str
    content: str
    truncated: bool


def read_blob(p: Path, root: Path, max_bytes: int) -> FileBlob:
    # For large files we compute the digest on the prefix we actually include.
    # This keeps the tool responsive while still allowing caching/dedup.
    raw = p.read_bytes()
    truncated = len(raw) > max_bytes
    raw2 = raw[:max_bytes]
    digest = hashlib.sha256(raw2).hexdigest()
    if truncated:
        digest = "prefix:" + digest
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
    h.update(CACHE_VERSION.encode("utf-8"))
    h.update(b"\0")
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

Lean “tactic loop” protocol (important; follow it):
- If Lean reports recursion depth / simp loop (e.g. “maximum recursion depth has been reached”),
  do NOT recommend `set_option maxRecDepth ...` as the fix.
- Instead:
  1) isolate the looping rewrite into a small named lemma (`have hp2 : ... := by ...`)
  2) apply it explicitly via `rw` / `calc` to stabilize goal shape
  3) then use `simp` with a tight whitelist (avoid comm/assoc spam), or finish with `ring_nf`.

Focus areas:
1) Lean / mathlib hygiene (fragility, casts, simp misuse, typeclass gotchas)
2) Mathematical coherence (hypotheses, invariants, goal alignment)
3) Repo coherence (README/docs vs reality, scaffolds clearly marked, naming consistency)

Constraints:
   - Some files are scaffolds and contain `sorry` intentionally, especially under Experiments/.
   - Prefer small, concrete edits that reduce future proof friction.
   - This repo intentionally uses `Scripts/` (capital S). Do not suggest renaming it to `scripts/`.
   - Do not treat model popularity/rankings as evidence. “This model is #1 on OpenRouter” is not a reason
     to change code or process; only technical constraints and measured behavior count.

Output discipline (important; follow it):
- Prefer ONE repair step at a time:
  - pick the single most important issue (blocker/high) and make its `concrete_edit` extremely specific
  - other issues (if any) should be brief and should not trigger refactors
- “Concrete edit” must be a minimal patch, not general advice:
  - name the exact lemma / block to change
  - show the replacement snippet (or an exact insert)
  - avoid broad renames or “rewrite the file” suggestions

Custom tools (optional; only if evidence is insufficient):
   You MAY request small, bounded evidence via `tool_requests` in your JSON output.
   Available tools:
   - read_file: fetch a file (repo-local), truncated
   - read_file_lines: fetch a specific line range from a repo-local file
   - rg: run ripgrep in the repo (bounded output; no pipes)
   - lean_imports: show the import/header block of a `.lean` file
   - lean_compile: compile a single `.lean` file via `lake env lean` (bounded timeout)

Output format:
   - Top issues (each must include: file path, quote/snippet anchor, and a concrete edit)
   - Then "Nice-to-have"
   - Then "Most likely future break" (1–3 bullets: where/why).
"""


def default_suggested_commands(*, scope: str) -> list[str]:
    """
    Deterministic, repo-native validation commands.

    This is intentionally not model-generated (reduces noise and keeps “reality” anchored).
    """
    base = [
        "git diff --cached",
        "git diff --cached --name-only",
        "./Scripts/check.sh pre-commit",
        "lake build",
        "lake lint",
    ]
    if scope == "staged":
        return base
    # Scope=all: encourage the CI-like profile too.
    return base + ["./Scripts/check.sh pre-push"]


def repo_wisdom(root: Path, *, max_bytes: int = 12_000) -> str:
    """
    Small dynamic injection of repo policy.

    Goal: prevent generic “ecosystem advice” that contradicts this repo.
    We keep this intentionally short to avoid blowing token budgets.
    """
    candidates = [
        root / ".cursor" / "rules" / "polygonal-number-theorem.mdc",
        root / ".cursor" / "rules" / "markdown-math-and-lint-triage.mdc",
        # Super-workspace rules (best-effort): helpful when repo-local rules are thin.
        root.parent / ".cursor" / "rules" / "covolume.mdc",
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


def local_status_block(root: Path, *, max_bytes: int = 18_000) -> str:
    """
    Deterministic local “ground truth” context.

    This runs only local commands and is capped. It should never block the hook.
    """
    try:
        pieces: list[str] = []
        now = sh_timeout(["date", "-Iseconds"], timeout_s=1.0)
        if now:
            pieces.append("===== date -Iseconds =====\n" + now + "\n")
        # git status (porcelain) is stable and small.
        st = sh_timeout(["git", "status", "--porcelain=v1"], timeout_s=2.5)
        if st:
            pieces.append("===== git status --porcelain=v1 =====\n" + st + "\n")

        # project status report (offline): shows sorry counts, high-signal for reviewers.
        lake = lake_path()
        sr = sh_timeout([lake, "exe", "status_report"], timeout_s=6.0)
        if sr:
            pieces.append("===== lake exe status_report =====\n" + sr + "\n")

        out = "\n".join(pieces).strip()
        if not out:
            return ""
        b = out.encode("utf-8")
        if len(b) > max_bytes:
            out = b[:max_bytes].decode("utf-8", errors="replace").rstrip()
            out += "\n\n[TRUNCATED local_status_block]\n"
        return out
    except Exception:
        return ""


def extract_status_report_text(local_block: str) -> str:
    """
    Pull out the `lake exe status_report` payload from `local_status_block()`.

    Returns empty string if absent.
    """
    if not local_block:
        return ""
    m = re.search(r"===== lake exe status_report =====\n([\s\S]*?)\n?$", local_block)
    if not m:
        return ""
    return m.group(1).strip()


def parse_sorry_summary(status_report: str, *, max_items: int = 12) -> list[tuple[str, int]]:
    """
    Parse lines like:
      - Covolume/Legendre/Minkowski.lean: 4
    """
    if not status_report:
        return []
    out: list[tuple[str, int]] = []
    for line in status_report.splitlines():
        m = re.match(r"^\s*-\s+(.+?\.lean)\s*:\s*(\d+)\s*$", line)
        if not m:
            continue
        p = m.group(1).strip()
        k = int(m.group(2))
        if k <= 0:
            continue
        out.append((p, k))
        if len(out) >= max_items:
            break
    return out


def _iter_sorry_lines(text: str, *, max_hits: int = 5) -> list[int]:
    """
    Find line numbers containing a `sorry` token, ignoring Lean comments/docstrings.

    We implement a small Lean comment stripper with nesting for `/- ... -/` and `-- ...`.
    This is not a full lexer, but it is good enough to avoid the common false positives
    from docstrings and archived experiment comments.
    """

    rx = re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])")
    hits: list[int] = []
    depth = 0
    in_str = False
    in_triple = False
    for i, line in enumerate(text.splitlines(), start=1):
        j = 0
        out_chars: list[str] = []
        n = len(line)
        while j < n:
            if depth == 0 and not in_str and not in_triple and line.startswith('"""', j):
                in_triple = True
                j += 3
                continue
            if depth == 0 and in_triple and line.startswith('"""', j):
                in_triple = False
                j += 3
                continue
            if depth == 0 and not in_triple:
                ch = line[j]
                if in_str:
                    # End string on an unescaped quote.
                    if ch == '"' and (j == 0 or line[j - 1] != "\\"):
                        in_str = False
                    j += 1
                    continue
                else:
                    if ch == '"':
                        in_str = True
                        j += 1
                        continue
            two = line[j : j + 2]
            if depth == 0 and two == "--":
                break  # rest of line is a comment
            if two == "/-":
                depth += 1
                j += 2
                continue
            if two == "-/" and depth > 0:
                depth -= 1
                j += 2
                continue
            if depth == 0 and (not in_str) and (not in_triple):
                out_chars.append(line[j])
            j += 1
        code = "".join(out_chars)
        if rx.search(code):
            hits.append(i)
            if len(hits) >= max_hits:
                break
    return hits


def count_sorry_tokens_text(text: str, *, max_hits: int = 5000) -> int:
    """
    Count `sorry` tokens, ignoring Lean comments/docstrings.

    Note: the count is “line hits”, not raw token occurrences, to keep the signal stable.
    """

    rx = re.compile(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])")
    n_hits = 0
    depth = 0
    in_str = False
    in_triple = False
    for line in text.splitlines():
        j = 0
        out_chars: list[str] = []
        m = len(line)
        while j < m:
            if depth == 0 and not in_str and not in_triple and line.startswith('"""', j):
                in_triple = True
                j += 3
                continue
            if depth == 0 and in_triple and line.startswith('"""', j):
                in_triple = False
                j += 3
                continue
            if depth == 0 and not in_triple:
                ch = line[j]
                if in_str:
                    if ch == '"' and (j == 0 or line[j - 1] != "\\"):
                        in_str = False
                    j += 1
                    continue
                else:
                    if ch == '"':
                        in_str = True
                        j += 1
                        continue
            two = line[j : j + 2]
            if depth == 0 and two == "--":
                break
            if two == "/-":
                depth += 1
                j += 2
                continue
            if two == "-/" and depth > 0:
                depth -= 1
                j += 2
                continue
            if depth == 0 and (not in_str) and (not in_triple):
                out_chars.append(line[j])
            j += 1
        code = "".join(out_chars)
        if rx.search(code):
            n_hits += 1
            if n_hits >= max_hits:
                break
    return n_hits


def sorry_focus_block(
    root: Path,
    *,
    top: list[tuple[str, int]],
    max_files: int = 3,
    max_sorry_sites_per_file: int = 2,
    context_lines: int = 18,
    max_bytes: int = 24_000,
) -> tuple[str, list[Path]]:
    """
    Return:
    - a deterministic prompt block focusing attention on the top `sorry` files
    - the corresponding repo-local Paths (existing `.lean` files only)
    """
    if not top:
        return ("", [])
    max_files = max(0, max_files)
    if max_files == 0:
        return ("", [])

    chosen = top[:max_files]
    paths: list[Path] = []
    lines: list[str] = []

    lines.append("===== SORRY_FOCUS (from status_report; deterministic) =====")
    lines.append("")
    lines.append("Top `sorry` files:")
    for rel, k in chosen:
        lines.append(f"- {rel}: {k}")

    lines.append("")
    lines.append("First `sorry` sites (approx, line numbers):")
    for rel, _k in chosen:
        p = (root / rel).resolve()
        try:
            p.relative_to(root.resolve())
        except Exception:
            continue
        if not p.exists() or not p.is_file() or p.suffix != ".lean":
            continue
        paths.append(p)
        try:
            txt = p.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        hits = _iter_sorry_lines(txt, max_hits=max_sorry_sites_per_file)
        if not hits:
            lines.append(f"- {rel}: (no `sorry` token found by scanner)")
        else:
            for ln in hits:
                lines.append(f"- {rel}:{ln}")

    # Excerpts (small, high-signal)
    lines.append("")
    lines.append("Excerpts:")
    for p in paths:
        try:
            rel = str(p.relative_to(root))
        except Exception:
            rel = str(p)
        try:
            txt_lines = p.read_text(encoding="utf-8", errors="replace").splitlines()
        except Exception:
            continue
        hits = _iter_sorry_lines("\n".join(txt_lines), max_hits=max_sorry_sites_per_file)
        for ln in hits:
            lo = max(1, ln - context_lines)
            hi = min(len(txt_lines), ln + context_lines)
            snippet = "\n".join(f"{i}|{txt_lines[i-1]}" for i in range(lo, hi + 1))
            lines.append(f"--- {rel}:{ln} ---")
            lines.append(snippet)
            lines.append("")

    out = "\n".join(lines).rstrip() + "\n"
    b = out.encode("utf-8")
    if len(b) > max_bytes:
        out = b[:max_bytes].decode("utf-8", errors="replace").rstrip()
        out += "\n\n[TRUNCATED sorry_focus_block]\n"
    # De-dupe paths (preserve order)
    seen: set[Path] = set()
    uniq: list[Path] = []
    for p in paths:
        rp = p.resolve()
        if rp in seen:
            continue
        seen.add(rp)
        uniq.append(rp)
    return (out, uniq)


def local_lean_diagnostics_block(root: Path, *, focus_paths: list[Path], max_bytes: int = 26_000) -> str:
    """
    Deterministic local Lean diagnostics for the current working tree.

    We compile a small number of `.lean` files (usually the ones you touched) and attach:
    - compiler output (warnings/errors)
    - small source-context windows around errors (via `execute_tool_requests`)

    This is capped and must never block the hook.
    """
    try:
        enable = os.environ.get("COVOLUME_LLM_REVIEW_LEAN_DIAGNOSTICS", "1").strip().lower()
        if enable in ("0", "false", "no", "off"):
            return ""

        max_files = int(os.environ.get("COVOLUME_LLM_REVIEW_LEAN_DIAG_MAX_FILES", "3").strip() or "3")
        if max_files <= 0:
            return ""

        # Preserve focus ordering (first is most important).
        seen: set[Path] = set()
        lean_files: list[Path] = []
        for p in focus_paths:
            if p.suffix != ".lean":
                continue
            rp = p.resolve()
            if rp in seen:
                continue
            seen.add(rp)
            lean_files.append(rp)
            if len(lean_files) >= max_files:
                break
        if not lean_files:
            return ""

        reqs: list[ToolRequest] = []
        for p in lean_files:
            try:
                rel = str(p.relative_to(root))
            except Exception:
                rel = str(p)
            reqs.append(ToolRequest(kind="lean_compile", path=rel))

        tool_out = execute_tool_requests(root, reqs, max_tools=max_files)
        if not tool_out:
            return ""

        hint = ""
        if "maximum recursion depth has been reached" in tool_out:
            hint = (
                "\n\n===== TACTIC_LOOP_HINT (repo policy) =====\n"
                "- This is usually a simp/proof normalization loop.\n"
                "- Preferred fix: extract the looping rewrite into a named lemma, apply with `rw`/`calc`,\n"
                "  then use a small `simp` set (or `ring_nf`) on the stabilized goal.\n"
                "- Avoid “fix” by increasing recursion limits (`set_option maxRecDepth ...`).\n"
            )
        out = "===== LEAN_DIAGNOSTICS (local, bounded) =====\n" + tool_out.strip() + hint + "\n"
        b = out.encode("utf-8")
        if len(b) > max_bytes:
            out = b[:max_bytes].decode("utf-8", errors="replace").rstrip()
            out += "\n\n[TRUNCATED local_lean_diagnostics_block]\n"
        return out
    except Exception:
        return ""


def _compiled_files_from_lean_diag(diag: str) -> set[str]:
    """
    Extract compiled `.lean` relative paths from the diagnostics block.
    """
    out: set[str] = set()
    if not diag:
        return out
    for line in diag.splitlines():
        m = re.match(r"^===== TOOL lean_compile (.+?\.lean)\s+\(exit=", line.strip())
        if m:
            out.add(m.group(1).strip())
    return out


def _micro_compile_one(root: Path, rel: str, *, timeout_s: float) -> tuple[int, str]:
    """
    Compile one `.lean` file and return (exit_code, truncated_output).
    """
    try:
        r = subprocess.run(
            [lake_path(), "env", "lean", rel],
            text=True,
            capture_output=True,
            timeout=timeout_s,
            cwd=str(root),
        )
        out = ((r.stdout or "") + "\n" + (r.stderr or "")).strip() or "(no output)"
        b = out.encode("utf-8")
        if len(b) > 6000:
            out = b[:6000].decode("utf-8", errors="replace") + "\n[TRUNCATED lean output]\n"
        return (int(r.returncode), out)
    except Exception as e:
        return (99, f"(micro_compile failed: {type(e).__name__}: {e!r})")


def _summarize_lean_output(out: str) -> dict[str, object]:
    """
    Extract a small, actionable summary from `lake env lean` output.
    """
    if not out:
        return {"errors": 0, "warnings": 0, "sorry_warnings": 0}
    lines = out.splitlines()
    # Lean format usually contains "error:" / "warning:" substrings.
    errors = sum(1 for ln in lines if "error:" in ln)
    warnings = sum(1 for ln in lines if "warning:" in ln)
    sorry_warnings = sum(1 for ln in lines if "declaration uses 'sorry'" in ln or "uses 'sorry'" in ln)
    # capture first error/warning anchor lines (file:line:col)
    pat = re.compile(r"^(.+?\.lean):(\d+):(\d+):")
    first_anchor = None
    for ln in lines:
        m = pat.match(ln.strip())
        if m:
            first_anchor = m.group(0)
            break
    return {
        "errors": int(errors),
        "warnings": int(warnings),
        "sorry_warnings": int(sorry_warnings),
        "first_anchor": first_anchor or "",
    }


def _high_signal_lean_lines(out: str, *, max_lines: int = 12) -> list[str]:
    """
    Extract only high-signal lines from Lean output for progress logs.

    Heuristic: keep:
    - lines containing `error:`
    - lines mentioning `declaration uses 'sorry'`
    - the first anchor line (file:line:col:) if present
    """
    if not out:
        return []
    lines = out.splitlines()
    keep: list[str] = []
    summary = _summarize_lean_output(out)
    first_anchor = str(summary.get("first_anchor") or "").strip()
    if first_anchor:
        # include the exact line that starts with the anchor if present
        for ln in lines:
            if ln.strip().startswith(first_anchor):
                keep.append(ln.strip())
                break
    for ln in lines:
        s = ln.strip()
        if "error:" in s:
            keep.append(s)
        if "declaration uses 'sorry'" in s or "uses 'sorry'" in s:
            keep.append(s)
        if len(keep) >= max_lines:
            break
    # De-dup, preserve order.
    out2: list[str] = []
    seen: set[str] = set()
    for s in keep:
        if s in seen:
            continue
        seen.add(s)
        out2.append(s)
    return out2[:max_lines]


def _validate_plan_action_anchor(root: Path, *, file_path: str, snippet_anchor: str) -> tuple[bool, int]:
    """
    Validate that `snippet_anchor` appears in `file_path`.

    We treat `snippet_anchor` as a literal substring, not a regex.
    Returns: (found, count_approx)
    """
    fp = (file_path or "").strip()
    anch = (snippet_anchor or "").strip()
    if not fp or not anch:
        return (False, 0)
    try:
        p = (root / fp).resolve()
        # prevent path traversal
        _ = p.relative_to(root.resolve())
    except Exception:
        return (False, 0)
    if not p.exists() or not p.is_file():
        return (False, 0)
    if is_sensitive_path(root, p):
        return (False, 0)
    try:
        raw = p.read_bytes()
    except Exception:
        return (False, 0)
    # Avoid scanning huge blobs; snippet anchors are meant to be short.
    raw2 = raw[:200_000]
    txt = raw2.decode("utf-8", errors="replace")
    c = txt.count(anch)
    return (c > 0, int(c))


def _normalize_and_validate_plan(
    root: Path, plan: ReviewPlan, *, focus_files: set[str]
) -> tuple[ReviewPlan, dict[str, object]]:
    """
    Enforce focus discipline and validate anchors for plan actions.

    - Drop next_actions outside SORRY_FOCUS.
    - Clamp confidence if anchor doesn't match in the referenced file.
    - Normalize plan.focus_files to the computed focus set.
    """
    stats = {
        "actions_in": int(len(plan.next_actions or [])),
        "actions_kept": 0,
        "actions_dropped_out_of_focus": 0,
        "actions_anchor_missing": 0,
    }

    dropped = 0
    kept: list[dict[str, object]] = []
    for a in (plan.next_actions or [])[:10]:
        fp = str(a.get("file_path") or "").strip()
        if focus_files and fp and fp not in focus_files:
            dropped += 1
            continue
        # Validate anchor existence.
        anch = str(a.get("snippet_anchor") or "").strip()
        found, cnt = _validate_plan_action_anchor(root, file_path=fp, snippet_anchor=anch)
        a["anchor_found"] = bool(found)
        a["anchor_count_approx"] = int(cnt)
        if fp and anch and not found:
            stats["actions_anchor_missing"] = int(stats["actions_anchor_missing"]) + 1
            # Reduce confidence if provided; otherwise add a conservative default.
            try:
                conf = float(a.get("confidence", 0.6))
            except Exception:
                conf = 0.6
            a["confidence"] = min(conf, 0.2)
            # Add a small note that this action may be mis-anchored.
            a["rationale"] = (str(a.get("rationale") or "") + "\n\n(Anchor not found in file; verify location.)").strip()
        kept.append(a)

    if dropped:
        stats["actions_dropped_out_of_focus"] = int(dropped)
        plan.notes = list(plan.notes or []) + [f"dropped {dropped} next_actions outside SORRY_FOCUS"]

    plan.next_actions = kept[:3]
    stats["actions_kept"] = int(len(plan.next_actions))

    if focus_files:
        plan.focus_files = sorted(list(focus_files))[:12]

    return plan, stats


def _pick_microcheck_target(focus_files: set[str], compiled: set[str]) -> str | None:
    """
    Pick a single focus file to compile for a deterministic micro-check.

    Policy: prefer the highest-leverage glue file first if present.
    """
    if not focus_files:
        return None
    prefs = [
        "Covolume/Legendre/Main.lean",
        "Covolume/Legendre/Minkowski.lean",
    ]
    for p in prefs:
        if p in focus_files and p not in compiled:
            return p
    # Fall back to stable alphabetical.
    for fp in sorted(list(focus_files)):
        if fp.endswith(".lean") and fp not in compiled:
            return fp
    return None


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


class ToolRequest(BaseModel):
    kind: Literal["read_file", "read_file_lines", "rg", "lean_compile", "lean_imports"]
    # read_file / read_file_lines / lean_compile / lean_imports:
    path: str | None = None
    # read_file_lines:
    start_line: int | None = None
    end_line: int | None = None
    # rg:
    pattern: str | None = None
    glob: str | None = None
    ignore_case: bool = False


class ReviewReport(BaseModel):
    top_issues: list[ReviewIssue] = Field(default_factory=list)
    nice_to_have: list[str] = Field(default_factory=list)
    most_likely_future_break: list[str] = Field(default_factory=list)
    suggested_commands: list[str] = Field(
        default_factory=list,
        description="Concrete local commands to validate claims (non-destructive).",
    )
    tool_requests: list[ToolRequest] = Field(
        default_factory=list,
        description="Optional requests for extra evidence (executed only in power=high).",
    )
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

def power_presets() -> dict[str, dict[str, str]]:
    """
    A single knob for “simple but powerful”.

    - low: cheap-ish, fast; good default for hooks
    - high: stronger models + multi-role + deep by default
    """
    return {
        "low": {
            # Still run the “one default thing”, just with fewer rounds.
            "COVOLUME_LLM_REVIEW_TIER": "heavy",
            "COVOLUME_LLM_REVIEW_STAGE": "deep",
            "COVOLUME_LLM_REVIEW_ROLES": "default",
            "COVOLUME_LLM_REVIEW_TIMEOUT_S_DEEP": "180",
            "COVOLUME_LLM_REVIEW_CONCURRENCY_DEEP": "1",
            "COVOLUME_LLM_REVIEW_ROUNDS": "1",
        },
        "high": {
            # These are applied only if the user hasn't set the corresponding env vars.
            "COVOLUME_LLM_REVIEW_TIER": "heavy",
            # Single-role by default to reduce variation / flakiness.
            "COVOLUME_LLM_REVIEW_ROLES": "default",
            "COVOLUME_LLM_REVIEW_STAGE": "deep",
            # Deep needs more time; keep concurrency low to avoid rate/timeouts.
            "COVOLUME_LLM_REVIEW_TIMEOUT_S_DEEP": "240",
            "COVOLUME_LLM_REVIEW_CONCURRENCY_DEEP": "1",
            # Multi-round: first pass proposes issues, second pass tightens/drops unsupported claims.
            "COVOLUME_LLM_REVIEW_ROUNDS": "2",
        },
        "max": {
            # Commit-time “use the big models” preset.
            #
            # Rationale:
            # - This project’s failure mode is proof fragility / subtle missing hypotheses.
            # - The hook is primarily for *human time savings*, not for cheapest tokens.
            #
            # Still: keep concurrency low so we don't amplify flakiness/rate limits.
            "COVOLUME_LLM_REVIEW_TIER": "heavy",
            # Single-role by default: fewer calls, less variance.
            "COVOLUME_LLM_REVIEW_ROLES": "default",
            # Deep review (full corpus) is where the best models pay off.
            "COVOLUME_LLM_REVIEW_STAGE": "deep",
            "COVOLUME_LLM_REVIEW_TIMEOUT_S_DEEP": "360",
            "COVOLUME_LLM_REVIEW_CONCURRENCY_DEEP": "1",
            "COVOLUME_LLM_REVIEW_TIMEOUT_S_TRIAGE": "90",
            "COVOLUME_LLM_REVIEW_CONCURRENCY_TRIAGE": "2",
            # Two-pass: propose → skeptical tighten.
            "COVOLUME_LLM_REVIEW_ROUNDS": "2",
            # Avoid wasting requests on typos / deprecated ids.
            "COVOLUME_LLM_REVIEW_PREFLIGHT_MODELS": "1",
        },
    }


def apply_power_preset(power: str) -> None:
    preset = power_presets().get(power, {})
    for k, v in preset.items():
        if os.environ.get(k, "").strip():
            continue
        os.environ[k] = v


def world_wisdom() -> str:
    # Keep it short; this is for alignment against common provider pitfalls.
    return WORLD_WISDOM.strip()


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
        suggested_commands=[],
        meta=[],
    )

    if policy_conflicts:
        out.meta.append(
            "Dropped policy-conflicting suggestions (e.g. renaming `Scripts/`); see per-model output for details."
        )
    return out


def apply_sorry_focus_policy(rep: ReviewReport, *, focus_files: set[str]) -> ReviewReport:
    """
    When `SORRY_FOCUS` exists, we want the output to be about unblocking those proofs.

    Policy:
    - prioritize issues in focus files
    - drop lint-only issues outside focus files (unless severity is `blocker`)
    - if nothing in focus files is reported, say so explicitly (meta)
    """
    if not focus_files:
        return rep

    kept: list[ReviewIssue] = []
    dropped = 0
    saw_focus = False

    for iss in rep.top_issues:
        fp = (iss.file_path or "").strip()
        in_focus = fp in focus_files
        if in_focus:
            saw_focus = True
            kept.append(iss)
            continue

        is_lint = any(t.startswith("lint") or t.startswith("linter") for t in (iss.tags or []))
        if is_lint and iss.severity != "blocker":
            dropped += 1
            continue
        kept.append(iss)

    # Re-order: focus issues first.
    kept.sort(key=lambda i: ((i.file_path or "").strip() in focus_files, _severity_weight(i.severity), i.confidence), reverse=True)
    rep.top_issues = kept[:10]

    meta = list(rep.meta or [])
    if dropped:
        meta.append(f"Dropped {dropped} lint-only issues outside SORRY_FOCUS files.")
    if not saw_focus:
        meta.append("No top issues referenced SORRY_FOCUS files; reviewer may have missed the proof gaps.")
    rep.meta = meta[:20]
    return rep


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
        # Heavy default: pick a strong general-purpose frontier model.
        # (Ensemble selection happens in `default_models_for_provider`.)
        return "anthropic/claude-opus-4.5"
    if tier == "fast":
        # Very fast, very cheap.
        return "google/gemini-3-flash-preview"
    # balanced: default to the best model; this tool exists for proof fragility catching.
    return "anthropic/claude-opus-4.5"


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
        return [m for m in _parse_models_env(explicit) if not is_blacklisted_model(m)][:8]

    explicit = os.environ.get("COVOLUME_LLM_REVIEW_MODELS", "").strip()
    if explicit:
        return [m for m in _parse_models_env(explicit) if not is_blacklisted_model(m)][:8]

    if provider == "openrouter":
        # One default model chain (reduce variation):
        # try best → fall back to still-strong → fall back to fast.
        return [
            "anthropic/claude-opus-4.5",
            "anthropic/claude-sonnet-4.5",
            "google/gemini-3-flash-preview",
        ]

    # OpenAI direct: keep conservative.
    m = os.environ.get("OPENAI_MODEL", "").strip()
    return [m] if m else ["gpt-4o-mini"]


def model_selection_rationale(*, provider: str, stage: str, models_override: list[str]) -> str:
    """
    Short policy-based explanation for the progress stream.

    Keep this deterministic and technical (no popularity/rank arguments).
    """
    if models_override:
        return "explicit --model override (applies to all stages)"
    if provider == "openrouter":
        return "default chain: best → strong fallback → fast fallback; stop at first success"
    return "single model (OpenAI); stop at first success"


def openrouter_models_index(base_url: str, *, timeout_s: int = 10) -> set[str]:
    """
    Fetch OpenRouter model ids via GET /models.

    This is best-effort and should never block the hook. It’s used for:
    - validating that requested ids exist
    - avoiding wasting requests on typos / deprecated ids
    """
    url = base_url.rstrip("/") + "/models"
    r = requests.get(url, timeout=timeout_s)
    r.raise_for_status()
    data = r.json()
    out: set[str] = set()
    for m in data.get("data", []) or []:
        mid = (m.get("id") or "").strip()
        if mid:
            out.add(mid)
    return out


def pick_stage_tuning(*, stage: str, tier: str, timeout_default: int, concurrency_default: int) -> tuple[int, int]:
    """
    Conservative defaults so heavy+deep doesn’t time out constantly.

    Explicit env overrides still win (handled in main), but if the user doesn’t set them,
    these defaults keep behavior sane.
    """
    if tier == "heavy" and stage == "deep":
        return (max(timeout_default, 180), min(concurrency_default, 2))
    if stage == "triage":
        return (min(timeout_default, 60), concurrency_default)
    return (timeout_default, concurrency_default)


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

    out.append("")
    out.append("Suggested commands:")
    if not rep.suggested_commands:
        out.append("(none)")
    else:
        for s in rep.suggested_commands[:12]:
            out.append(f"- {s}")
    return "\n".join(out).rstrip() + "\n"


def refine_prompt(*, prev_json: str) -> str:
    return (
        "REFINE / SKEPTIC MODE:\n"
        "- You are given a previous JSON review output.\n"
        "- Delete issues that are not supported by the provided evidence (diff, file list, corpus, lean_context).\n"
        "- For remaining issues, rewrite `concrete_edit` as a minimal, directly actionable change.\n"
        "- Do not add new issues unless they are strictly implied by the evidence.\n"
        "\n"
        "Previous JSON:\n"
        "```json\n"
        + prev_json.strip()
        + "\n```\n"
    )


def _safe_relpath(root: Path, p: Path) -> str:
    try:
        return str(p.relative_to(root))
    except Exception:
        return str(p)


def execute_tool_requests(root: Path, reqs: list[ToolRequest], *, max_tools: int = 6) -> str:
    """
    Execute a bounded set of repo-local “pseudo tools”.

    Design constraints:
    - No network
    - Repo-local paths only
    - Bounded output and short timeouts
    """
    if not reqs:
        return ""

    root_r = root.resolve()
    chunks: list[str] = []
    n = 0

    for r in reqs:
        if n >= max_tools:
            break

        def resolve_repo_path(raw: str) -> Path | None:
            if not raw or raw.startswith(".."):
                return None
            p = (root / raw).resolve()
            try:
                p.relative_to(root_r)
            except Exception:
                return None
            if not p.exists() or not p.is_file():
                return None
            return p

        if r.kind == "read_file":
            p = resolve_repo_path((r.path or "").strip())
            if p is None:
                continue
            blob = read_blob(p, root, max_bytes=12_000)
            chunks.append(
                f"===== TOOL read_file {blob.rel} (bytes={blob.bytes_len}, sha256={blob.sha256}"
                + (", TRUNCATED" if blob.truncated else "")
                + ") =====\n"
                + blob.content
                + ("\n" if not blob.content.endswith("\n") else "")
            )
            n += 1
            continue

        if r.kind == "read_file_lines":
            p = resolve_repo_path((r.path or "").strip())
            if p is None:
                continue
            lo = int(r.start_line or 1)
            hi = int(r.end_line or lo + 80)
            lo = max(1, lo)
            hi = max(lo, hi)
            # Hard cap: keep this small.
            if hi - lo > 220:
                hi = lo + 220
            try:
                lines = p.read_text(encoding="utf-8", errors="replace").splitlines()
            except Exception:
                continue
            snippet = "\n".join(f"{i+1}|{lines[i]}" for i in range(lo - 1, min(hi, len(lines))))
            chunks.append(
                f"===== TOOL read_file_lines {_safe_relpath(root, p)}:{lo}-{hi} =====\n{snippet}\n"
            )
            n += 1
            continue

        if r.kind == "rg":
            pat = (r.pattern or "").strip()
            if not pat:
                continue
            args = ["rg", "-n", "--no-heading", "--max-count", "50"]
            if r.ignore_case:
                args.append("-i")
            if r.glob:
                args.extend(["--glob", r.glob])
            args.append(pat)
            args.append(str(root))
            txt = sh_timeout(args, timeout_s=3.0)
            if not txt:
                continue
            b = txt.encode("utf-8")
            if len(b) > 9000:
                txt = b[:9000].decode("utf-8", errors="replace")
                txt += "\n[TRUNCATED rg output]\n"
            chunks.append(f"===== TOOL rg pattern={pat!r} =====\n{txt}\n")
            n += 1
            continue

        if r.kind == "lean_imports":
            p = resolve_repo_path((r.path or "").strip())
            if p is None or p.suffix != ".lean":
                continue
            hdr = lean_file_header(p, max_lines=120)
            if not hdr:
                continue
            chunks.append(f"===== TOOL lean_imports {_safe_relpath(root, p)} =====\n{hdr}\n")
            n += 1
            continue

        if r.kind == "lean_compile":
            p = resolve_repo_path((r.path or "").strip())
            if p is None or p.suffix != ".lean":
                continue
            # Compile a single file to surface warnings/lints/errors relevant to this review.
            # Bounded timeout; output is capped.
            try:
                tmo = float(os.environ.get("COVOLUME_LLM_REVIEW_LEAN_COMPILE_TIMEOUT_S", "25").strip() or "25")
                r2 = subprocess.run(
                    [lake_path(), "env", "lean", _safe_relpath(root, p)],
                    text=True,
                    capture_output=True,
                    timeout=tmo,
                    cwd=str(root),
                )
            except Exception:
                continue
            out = ((r2.stdout or "") + "\n" + (r2.stderr or "")).strip()
            if not out:
                out = "(no output)"
            # If there are errors, attach a small source-context window.
            # This follows the “lean4check” pattern (compile + contextualize errors) and
            # reduces the reasoning tax when interpreting messages.
            ctx_chunks: list[str] = []
            # Match common Lean error prefix: path:line:col:
            # Example: Covolume/Core/ModularSquares.lean:114:43: unsolved goals
            pat = re.compile(r"^(.+?\.lean):(\d+):(\d+):", re.MULTILINE)
            hits = []
            for m in pat.finditer(out):
                hits.append((m.group(1), int(m.group(2)), int(m.group(3))))
                if len(hits) >= 3:
                    break
            for (fp, line, col) in hits:
                p2 = resolve_repo_path(fp.strip())
                if p2 is None:
                    continue
                lo = max(1, line - 4)
                hi = line + 4
                try:
                    lines = p2.read_text(encoding="utf-8", errors="replace").splitlines()
                except Exception:
                    continue
                snippet = "\n".join(
                    f"{i+1}|{lines[i]}" for i in range(lo - 1, min(hi, len(lines)))
                )
                caret = " " * (len(f"{line}|") + max(0, col - 1)) + "^"
                ctx_chunks.append(
                    f"--- {fp}:{line}:{col} ---\n{snippet}\n{caret}\n"
                )
            if ctx_chunks:
                out = out + "\n\n===== lean_error_context =====\n" + "\n".join(ctx_chunks).strip()
            b = out.encode("utf-8")
            if len(b) > 9000:
                out = b[:9000].decode("utf-8", errors="replace") + "\n[TRUNCATED lean output]\n"
            chunks.append(
                f"===== TOOL lean_compile {_safe_relpath(root, p)} (exit={r2.returncode}) =====\n{out}\n"
            )
            n += 1
            continue

    return "\n".join(chunks).strip()


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
        i = s.find("{")
        j = s.rfind("}")
        if i == -1 or j == -1 or j <= i:
            raise ValueError("no JSON object delimiters found")
        return s[i : j + 1]

    # Default behavior (reduce flakiness/variance): request plain JSON and parse locally.
    #
    # Rationale:
    # - pydantic-ai structured output can fail when models emit non-JSON or slightly-off schemas
    # - OpenRouter “reasoning_details” continuity and tool calling complicate retries
    # - we already shove full context, so tool calling adds little value
    use_pydantic_ai = os.environ.get("COVOLUME_LLM_REVIEW_USE_PYDANTIC_AI", "0").strip().lower()
    if use_pydantic_ai in ("0", "false", "no", "off"):
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
  "suggested_commands": ["..."],
  "tool_requests": [
    {"kind": "read_file", "path": "Covolume/Legendre/Ankeny.lean"},
    {"kind": "lean_imports", "path": "Covolume/Legendre/Ankeny.lean"},
    {"kind": "read_file_lines", "path": "Covolume/Legendre/Ankeny.lean", "start_line": 150, "end_line": 220},
    {"kind": "lean_compile", "path": "Covolume/Core/ModularSquares.lean"},
    {"kind": "rg", "pattern": "simpa", "glob": "*.lean", "ignore_case": false}
  ],
  "meta": ["..."]
}
"""
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

    # Optional legacy behavior: pydantic-ai structured output (uses tool calling internally).
    settings = None
    if provider == "openrouter":
        # Optional: ask OpenRouter for stronger reasoning on deep runs.
        # Keep opt-in to avoid surprising cost/latency increases.
        effort = os.environ.get("COVOLUME_LLM_REVIEW_REASONING_EFFORT", "").strip().lower()
        if effort in ("low", "medium", "high"):
            settings = OpenRouterModelSettings(openrouter_reasoning={"effort": effort})
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

    agent = Agent(model, output_type=ReviewReport, system_prompt=system_prompt, model_settings=settings)
    # Hard timeout at the coroutine level.
    res = await asyncio.wait_for(agent.run(user_prompt), timeout=timeout_s)
    return res.output


async def run_one_plan(
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
) -> ReviewPlan | None:
    """
    Optional “early” model call to emit a plan before the heavy review finishes.

    This should remain small (no full corpus), and it must never crash the pipeline.
    """
    schema_hint = """
Return a single JSON object (no surrounding prose) of the form:
{
  "focus_files": ["..."],
  "hypotheses_to_check": ["..."],
  "expected_failure_modes": ["..."],
  "intended_evidence": ["..."],
  "next_actions": [
    {
      "action": "edit|compile|search|run",
      "file_path": "Covolume/Legendre/Main.lean",
      "snippet_anchor": "short quote/anchor",
      "command": "optional local command",
      "rationale": "why this is next",
      "confidence": 0.0-1.0
    }
  ],
  "notes": ["..."]
}
"""
    try:
        t0 = time.perf_counter()
        txt = openai_chat(
            base_url=base_url,
            api_key=api_key,
            model=model_id,
            system=system_prompt
            + "\n\nPLAN MODE:\n"
            + "- Be brief, and be concrete.\n"
            + "- ONLY reference files in SORRY_FOCUS (or explicitly say 'out of focus').\n"
            + "- Prefer things we can validate locally (compile a file, point to a lemma, small patch).\n"
            + "- Produce at most 3 items in `next_actions`.\n\n"
            + schema_hint,
            user=user_prompt,
            timeout_s=timeout_s,
            extra_headers={
                **({"HTTP-Referer": app_url} if app_url else {}),
                **({"X-Title": app_title} if app_title else {}),
            }
            or None,
        )
        _ = t0  # keep for symmetry; caller measures externally too
        try:
            return ReviewPlan.model_validate_json(txt)
        except Exception:
            # attempt to extract a JSON object substring
            i = txt.find("{")
            j = txt.rfind("}")
            if i != -1 and j != -1 and j > i:
                return ReviewPlan.model_validate(json.loads(txt[i : j + 1]))
            return None
    except Exception:
        return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--scope", choices=["staged", "worktree", "all"], default="")
    ap.add_argument("--include-diff", action="store_true", default=True)
    ap.add_argument("--no-include-diff", dest="include_diff", action="store_false")
    ap.add_argument("--max-bytes-per-file", type=int, default=12_000)
    ap.add_argument("--max-total-bytes", type=int, default=320_000)
    ap.add_argument("--max-diff-bytes", type=int, default=180_000)
    ap.add_argument("--timeout-s", type=int, default=180)
    ap.add_argument("--provider", choices=["auto", "openrouter", "openai"], default="auto")
    ap.add_argument("--base-url", default="")
    ap.add_argument("--model", default="")
    ap.add_argument("--stage", choices=["triage", "deep", "both"], default="")
    ap.add_argument("--roles", default="")
    ap.add_argument("--power", choices=["low", "high", "max"], default="")
    ap.add_argument("--rounds", type=int, default=0, help="Number of LLM passes per model (default: env/preset).")
    ap.add_argument("--doctor", action="store_true", help="Print provider/model/base_url selection and exit.")
    ap.add_argument(
        "--require-key",
        action="store_true",
        help="Exit nonzero if no provider API key is configured.",
    )
    args = ap.parse_args()

    root = repo_root()
    t0_all = time.perf_counter()
    load_dotenv_if_present(root)
    mcp_env = os.environ.get("COVOLUME_LLM_REVIEW_LOAD_CURSOR_MCP_ENV", "1").strip().lower()
    if mcp_env not in ("0", "false", "no", "off"):
        load_cursor_mcp_env_if_present()

    # Apply the “power” preset early so it influences stage/tier/roles defaults.
    power = (args.power.strip() or os.environ.get("COVOLUME_LLM_REVIEW_POWER", "max")).strip().lower()
    if power not in ("low", "high", "max"):
        power = "max"
    apply_power_preset(power)

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
        print(f"power={power}")
        # Helpful for understanding what will run.
        stage2 = os.environ.get("COVOLUME_LLM_REVIEW_STAGE", "").strip() or "(default)"
        tier2 = os.environ.get("COVOLUME_LLM_REVIEW_TIER", "balanced").strip()
        roles2 = os.environ.get("COVOLUME_LLM_REVIEW_ROLES", "").strip() or "(default)"
        print(f"stage={stage2}")
        print(f"tier={tier2}")
        print(f"roles={roles2}")
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

    emit_progress(
        root,
        ProgressEvent(
            event="provider_selected",
            ts=_now_iso(),
            phase="start",
            message="provider selected; building context",
            data={
                "provider": provider,
                "base_url": base_url,
                "power": power,
                "openrouter_key_present": bool(openrouter_key),
                "openai_key_present": bool(openai_key),
                "mcp_env_loader": (mcp_env not in ("0", "false", "no", "off")),
            },
        ),
    )
    if _jsonl_enabled():
        p = _progress_jsonl_path(root)
        emit_progress(
            root,
            ProgressEvent(
                event="jsonl_enabled",
                ts=_now_iso(),
                phase="start",
                message="jsonl progress enabled",
                data={
                    "progress_file": str(p) if p is not None else "(none)",
                    "schema": "ProgressEvent (one JSON object per line)",
                },
            ),
        )

    # Default behavior: shove context in.
    scope = (args.scope.strip() or os.environ.get("COVOLUME_LLM_REVIEW_SCOPE", "all")).strip().lower()
    if scope not in ("staged", "worktree", "all"):
        scope = "all"
    args.scope = scope

    t_paths0 = time.perf_counter()
    if args.scope == "staged":
        changed_paths = staged_paths(root)
        if not changed_paths:
            # Ad-hoc runs often happen before staging; optionally fall back to unstaged changes.
            fb = os.environ.get("COVOLUME_LLM_REVIEW_FALLBACK_UNSTAGED", "1").strip().lower()
            if fb not in ("0", "false", "no", "off"):
                changed_paths = unstaged_paths(root)
        paths = list(changed_paths)
        # Always include top-level docs for coherence checks (cheap, high value).
        for p in [root / "README.md", root / "PROOF_ROADMAP.md"]:
            if p.exists() and p.is_file():
                if p not in paths:
                    paths.append(p)
    elif args.scope == "worktree":
        changed_paths = worktree_paths(root)
        paths = list(changed_paths)
        for p in [root / "README.md", root / "PROOF_ROADMAP.md"]:
            if p.exists() and p.is_file():
                if p not in paths:
                    paths.append(p)
    else:
        # Still track changed paths for Lean context (imports/versions) even when we dump a full corpus.
        changed_paths = worktree_paths(root)
        paths = all_review_paths(root)

    changed_list = list(changed_paths)
    emit_progress(
        root,
        ProgressEvent(
            event="paths_selected",
            ts=_now_iso(),
            phase="context",
            message="selected paths",
            data={
                "scope": args.scope,
                "changed_paths": int(len(changed_list)),
                "selected_paths": int(len(paths)),
                "changed_preview": [str(p) for p in changed_list[:10]],
                "elapsed_ms": int((time.perf_counter() - t_paths0) * 1000),
            },
        ),
    )

    t_blobs0 = time.perf_counter()
    blobs = [read_blob(p, root, args.max_bytes_per_file) for p in paths]
    corpus, used = assemble_corpus(blobs, args.max_total_bytes)
    emit_progress(
        root,
        ProgressEvent(
            event="context_built",
            ts=_now_iso(),
            phase="context",
            message="assembled corpus + diff + local diagnostics",
            data={
                "scope": args.scope,
                "files_total": len(blobs),
                "files_truncated": sum(1 for b in blobs if b.truncated),
                "truncated_files_preview": [b.rel for b in blobs if b.truncated][:10],
                "bytes_total_files": sum(int(b.bytes_len) for b in blobs),
                "bytes_used_corpus": used,
                "max_total_bytes": int(args.max_total_bytes),
                "max_bytes_per_file": int(args.max_bytes_per_file),
                "elapsed_ms": int((time.perf_counter() - t_blobs0) * 1000),
                "approx_tokens_corpus": _estimate_tokens_from_bytes(int(used)),
            },
        ),
    )

    diff_txt = ""
    if args.include_diff:
        t_diff0 = time.perf_counter()
        diff_txt = staged_diff() if args.scope == "staged" else worktree_diff()
        if diff_txt:
            diff_txt = _truncate_utf8(diff_txt, max_bytes=int(args.max_diff_bytes), label="diff")
        emit_progress(
            root,
            ProgressEvent(
                event="diff_loaded",
                ts=_now_iso(),
                phase="context",
                message="loaded diff",
                data={
                    "diff_bytes": len(diff_txt.encode("utf-8", errors="replace")),
                    "max_diff_bytes": int(args.max_diff_bytes),
                    "elapsed_ms": int((time.perf_counter() - t_diff0) * 1000),
                },
            ),
        )
    else:
        emit_progress(
            root,
            ProgressEvent(
                event="diff_skipped",
                ts=_now_iso(),
                phase="context",
                message="diff disabled",
            ),
        )

    meta = (
        f"Review scope: {args.scope}\n"
        f"Files included: {len(blobs)}\n"
        f"Bytes included: {used} (max_total_bytes={args.max_total_bytes})\n"
        f"Per-file truncation: max_bytes_per_file={args.max_bytes_per_file}\n"
    )

    diff_block = ""
    if diff_txt.strip():
        diff_block = "===== git diff --cached =====\n" + diff_txt + "\n\n"

    # Deterministic local status first: we use it both as prompt evidence and
    # to prioritize which files to compile / excerpt.
    local_block = local_status_block(root)
    status_report = extract_status_report_text(local_block)
    top_sorries = parse_sorry_summary(status_report, max_items=20)

    # Ensure we focus on *touched* files that still contain `sorry`, even if they
    # don't make the global "top-N by count" list.
    extra_focus: list[tuple[str, int]] = []
    for p in changed_paths:
        if p.suffix != ".lean":
            continue
        try:
            rel = str(p.relative_to(root))
        except Exception:
            continue
        try:
            txt = p.read_text(encoding="utf-8", errors="replace")
        except Exception:
            continue
        k = count_sorry_tokens_text(txt)
        if k > 0:
            extra_focus.append((rel, k))
        if len(extra_focus) >= 6:
            break

    # Focus policy:
    # - If we have any *touched files* containing `sorry`, focus ONLY on those.
    #   (This avoids drowning the review in unrelated high-sorry-count scaffolds.)
    # - Otherwise, fall back to the global top list from `status_report`.
    if extra_focus:
        merged_focus = list(extra_focus)
    else:
        merged_focus = list(top_sorries)

    sorry_focus, sorry_focus_paths = sorry_focus_block(root, top=merged_focus)
    sorry_focus_block_txt = (sorry_focus + "\n\n") if sorry_focus else ""
    focus_files: set[str] = set()
    for p in sorry_focus_paths:
        try:
            focus_files.add(str(p.relative_to(root)))
        except Exception:
            continue

    if focus_files:
        emit_progress(
            root,
            ProgressEvent(
                event="sorry_focus",
                ts=_now_iso(),
                phase="context",
                message="computed SORRY_FOCUS",
                data={
                    "focus_files_count": int(len(focus_files)),
                    "focus_files_preview": sorted(list(focus_files))[:12],
                    "extra_focus_preview": [rel for (rel, _k) in extra_focus][:12],
                },
            ),
        )
    else:
        emit_progress(
            root,
            ProgressEvent(
                event="sorry_focus_empty",
                ts=_now_iso(),
                phase="context",
                message="no SORRY_FOCUS files detected",
            ),
        )

    # Lean context: still derived from the *changed* paths (imports + toolchain + versions).
    lean_ctx = lean_context(root, focus_paths=changed_paths)
    lean_block = ""
    if lean_ctx:
        lean_block = "===== lean_context =====\n" + lean_ctx + "\n\n"
        emit_progress(
            root,
            ProgressEvent(
                event="lean_context",
                ts=_now_iso(),
                phase="context",
                message="built lean_context",
                data={
                    "bytes": len(lean_ctx.encode("utf-8", errors="replace")),
                },
            ),
        )

    # Diagnostics: compile changed `.lean` files first, then top-sorry files.
    diag_focus: list[Path] = []
    for p in changed_paths:
        if p.suffix == ".lean":
            diag_focus.append(p)
    for p in sorry_focus_paths:
        if p.suffix == ".lean":
            diag_focus.append(p)
    lean_diag = local_lean_diagnostics_block(root, focus_paths=diag_focus)
    lean_diag_block = (lean_diag + "\n\n") if lean_diag else ""
    emit_progress(
        root,
        ProgressEvent(
            event="lean_diagnostics",
            ts=_now_iso(),
            phase="context",
            message="ran local lean diagnostics (bounded)",
            data={
                "files_considered": int(len(diag_focus)),
                "max_files": int(os.environ.get("COVOLUME_LLM_REVIEW_LEAN_DIAG_MAX_FILES", "3").strip() or "3"),
                "timeout_s": float(os.environ.get("COVOLUME_LLM_REVIEW_LEAN_COMPILE_TIMEOUT_S", "25").strip() or "25"),
                "output_bytes": len(lean_diag.encode("utf-8", errors="replace")) if lean_diag else 0,
                "has_output": bool(lean_diag.strip()),
            },
        ),
    )

    # Micro-check: if SORRY_FOCUS exists but diagnostics didn't compile any focus file (cap=3),
    # compile exactly one focus file to get a deterministic error surface. Default on; bounded.
    micro = os.environ.get("COVOLUME_LLM_REVIEW_MICROCHECK", "1").strip().lower()
    if micro not in ("0", "false", "no", "off") and focus_files:
        compiled = _compiled_files_from_lean_diag(lean_diag)
        todo = _pick_microcheck_target(focus_files, compiled)
        if todo:
            t_mc0 = time.perf_counter()
            tmo = float(os.environ.get("COVOLUME_LLM_REVIEW_MICROCHECK_TIMEOUT_S", "20").strip() or "20")
            rc, out = _micro_compile_one(root, todo, timeout_s=tmo)
            summary = _summarize_lean_output(out)
            # Only include high-signal lines (errors + `uses sorry`), otherwise omit.
            sig_lines = _high_signal_lean_lines(out, max_lines=12)
            emit_progress(
                root,
                ProgressEvent(
                    event="microcheck_compile",
                    ts=_now_iso(),
                    phase="context",
                    message="micro-check: compiled one focus file",
                    data={
                        "file": todo,
                        "exit": int(rc),
                        "timeout_s": tmo,
                        "elapsed_ms": int((time.perf_counter() - t_mc0) * 1000),
                        **{f"summary_{k}": v for (k, v) in summary.items()},
                        "high_signal_lines": sig_lines,
                    },
                ),
            )

    stage = args.stage.strip().lower() or os.environ.get("COVOLUME_LLM_REVIEW_STAGE", "").strip().lower()
    if stage not in ("triage", "deep", "both"):
        # One default behavior: deep.
        stage = "deep"

    # Default ensemble can depend on stage; if --model is specified, it applies to both stages.
    models_override = [args.model.strip()] if args.model.strip() else []
    concurrency_default = int(os.environ.get("COVOLUME_LLM_REVIEW_CONCURRENCY", "3").strip() or "3")
    timeout_default = int(os.environ.get("COVOLUME_LLM_REVIEW_TIMEOUT_S", str(args.timeout_s)).strip() or str(args.timeout_s))
    tier = os.environ.get("COVOLUME_LLM_REVIEW_TIER", "balanced").strip().lower()

    emit_progress(
        root,
        ProgressEvent(
            event="start",
            ts=_now_iso(),
            phase="start",
            message="starting llm review pipeline",
            data={
                "provider": provider,
                "base_url": base_url,
                "scope": args.scope,
                "stage": stage,
                "tier": tier,
                "power": power,
                "roles": args.roles.strip() or os.environ.get("COVOLUME_LLM_REVIEW_ROLES", "").strip() or "(default)",
                "include_diff": bool(args.include_diff),
                "cache_version": CACHE_VERSION,
            },
        ),
    )
    emit_progress(
        root,
        ProgressEvent(
            event="cache_config",
            ts=_now_iso(),
            phase="start",
            message="cache enabled",
            data={
                "cache_dir": str(cache_dir(root)),
                "cache_version": CACHE_VERSION,
            },
        ),
    )

    system = domain_prompt()
    system = system + "\n\n" + world_wisdom()
    wisdom = repo_wisdom(root)
    if wisdom:
        system = system + "\n\n" + wisdom

    if local_block:
        system = system + "\n\n" + local_block

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

    transcript = agent_transcript_tail()

    # Stage prompts.
    triage_prompt = (
        meta
        + "\n"
        + diff_block
        + sorry_focus_block_txt
        + lean_block
        + lean_diag_block
        + transcript
        + "===== FILE LIST =====\n"
        + "\n".join(f"- {b.rel}" for b in blobs)
        + "\n"
        + "\n\nTRIAGE MODE:\n"
        + "- You do NOT have full file contents.\n"
        + "- Do NOT complain about missing content.\n"
        + "- Only report issues you can justify from the diff or file list.\n"
        + "- If you must recommend a deeper check, express it as a concrete follow-up action, not as a complaint.\n"
        + "- Prioritize closing `sorry` sites in SORRY_FOCUS files. Ignore lint-only nits unless they block that work.\n"
        + "\n(Do not ask questions. Propose edits.)\n"
    )
    deep_prompt = (
        meta
        + "\n"
        + diff_block
        + sorry_focus_block_txt
        + lean_block
        + lean_diag_block
        + transcript
        + "\n\nDEEP MODE:\n"
        + "- Prioritize closing `sorry` sites in SORRY_FOCUS files. Ignore lint-only nits unless they block that work.\n"
        + "- If you cannot propose a concrete proof step, say so explicitly and name the missing lemma you would search for.\n\n"
        + corpus
    )

    async def run_stage(stage_name: str, user_prompt: str) -> ReviewReport:
        base_timeout, base_conc = pick_stage_tuning(
            stage=stage_name,
            tier=tier,
            timeout_default=timeout_default,
            concurrency_default=concurrency_default,
        )
        stage_timeout = int(os.environ.get(f"COVOLUME_LLM_REVIEW_TIMEOUT_S_{stage_name.upper()}", str(base_timeout)).strip() or str(base_timeout))
        stage_concurrency = int(os.environ.get(f"COVOLUME_LLM_REVIEW_CONCURRENCY_{stage_name.upper()}", str(base_conc)).strip() or str(base_conc))
        # One default behavior: try models in order and stop at first success.
        models = models_override or default_models_for_provider(provider, stage=stage_name)
        models = [m for m in models if not is_blacklisted_model(m)]

        emit_progress(
            root,
            ProgressEvent(
                event="stage_start",
                ts=_now_iso(),
                phase="stage",
                stage=stage_name,
                message="stage starting",
                data={
                    "models": models,
                    "models_rationale": model_selection_rationale(
                        provider=provider, stage=stage_name, models_override=models_override
                    ),
                    "blacklist": model_blacklist(),
                    "timeout_s": int(stage_timeout),
                    "concurrency": int(stage_concurrency),
                    "rounds": int(args.rounds if args.rounds > 0 else int(os.environ.get("COVOLUME_LLM_REVIEW_ROUNDS", "").strip() or "1")),
                },
            ),
        )

        # Optional preflight: drop unknown OpenRouter model ids early to avoid wasting requests.
        if provider == "openrouter":
            preflight = os.environ.get("COVOLUME_LLM_REVIEW_PREFLIGHT_MODELS", "1").strip().lower()
            if preflight not in ("0", "false", "no", "off"):
                try:
                    known = openrouter_models_index(base_url, timeout_s=10)
                    emit_progress(
                        root,
                        ProgressEvent(
                            event="openrouter_preflight_models",
                            ts=_now_iso(),
                            phase="stage",
                            stage=stage_name,
                            message="model id preflight completed",
                            data={
                                "known_count": int(len(known)),
                                "models_before": list(models),
                            },
                        ),
                    )
                    models2 = [m for m in models if (m in known and (not is_blacklisted_model(m)))]
                    if models2:
                        models = models2
                    else:
                        # If everything got filtered, keep original list (don’t brick the reviewer).
                        pass
                    emit_progress(
                        root,
                        ProgressEvent(
                            event="openrouter_models_selected",
                            ts=_now_iso(),
                            phase="stage",
                            stage=stage_name,
                            message="models selected after preflight",
                            data={"models_after": list(models)},
                        ),
                    )
                except Exception:
                    pass

        async def run_model(m: str, role: str) -> tuple[str, ReviewReport] | None:
            rounds_env = os.environ.get("COVOLUME_LLM_REVIEW_ROUNDS", "").strip()
            rounds = args.rounds if args.rounds > 0 else int(rounds_env or "1")
            rounds = max(1, min(rounds, 3))

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
                    emit_progress(
                        root,
                        ProgressEvent(
                            event="cache_hit",
                            ts=_now_iso(),
                            phase="cache",
                            stage=stage_name,
                            role=role,
                            model=m,
                            message="loaded report from cache",
                            data={"cache_path": str(cache_path)},
                        ),
                    )
                    return (m, rep)
                except Exception:
                    pass

            try:
                sys2 = system if role == "default" else (system + "\n\n" + role_map[role])
                emit_progress(
                    root,
                    ProgressEvent(
                        event="model_start",
                        ts=_now_iso(),
                        phase="model",
                        stage=stage_name,
                        role=role,
                        model=m,
                        message="starting model call",
                        data={
                            "timeout_s": int(stage_timeout),
                            "prompt_bytes_system": len(sys2.encode("utf-8", errors="replace")),
                            "prompt_bytes_user": len(user_prompt.encode("utf-8", errors="replace")),
                        },
                    ),
                )

                # Optional: emit an early “plan” for deep runs (cached separately).
                plan_enabled = os.environ.get("COVOLUME_LLM_REVIEW_PLAN", "1").strip().lower()
                if stage_name == "deep" and plan_enabled not in ("0", "false", "no", "off"):
                    plan_key = cache_key(
                        model=f"{provider}:{m}:{stage_name}:role={role}:plan",
                        scope=args.scope,
                        diff_txt=diff_txt,
                        blobs=blobs,
                    )
                    plan_path = cache_dir(root) / f"{plan_key}.plan.json"
                    plan_obj: ReviewPlan | None = None
                    if plan_path.exists():
                        try:
                            plan_obj = ReviewPlan.model_validate_json(
                                plan_path.read_text(encoding="utf-8", errors="replace")
                            )
                            emit_progress(
                                root,
                                ProgressEvent(
                                    event="plan_cache_hit",
                                    ts=_now_iso(),
                                    phase="cache",
                                    stage=stage_name,
                                    role=role,
                                    model=m,
                                    message="loaded plan from cache",
                                    data={"cache_path": str(plan_path)},
                                ),
                            )
                        except Exception:
                            plan_obj = None
                    if plan_obj is None:
                        # Plan prompt is intentionally “triage-like”: no full corpus.
                        plan_user = triage_prompt if stage_name == "deep" else user_prompt
                        t_plan0 = time.perf_counter()
                        plan_obj = await run_one_plan(
                            provider=provider,
                            model_id=m,
                            api_key=api_key,
                            base_url=base_url,
                            app_url=site_url,
                            app_title=app_name,
                            system_prompt=sys2,
                            user_prompt=plan_user,
                            timeout_s=min(90, int(stage_timeout)),
                        )
                        dt_ms = int((time.perf_counter() - t_plan0) * 1000)
                        if plan_obj is not None:
                            plan_obj, vstats = _normalize_and_validate_plan(root, plan_obj, focus_files=focus_files)
                            try:
                                plan_path.write_text(plan_obj.model_dump_json(indent=2), encoding="utf-8")
                            except Exception:
                                pass
                            emit_progress(
                                root,
                                ProgressEvent(
                                    event="plan_emitted",
                                    ts=_now_iso(),
                                    phase="plan",
                                    stage=stage_name,
                                    role=role,
                                    model=m,
                                    message="early plan available (structured)",
                                    data={
                                        "elapsed_ms": dt_ms,
                                        "focus_files": plan_obj.focus_files[:12],
                                        "hypotheses_to_check": plan_obj.hypotheses_to_check[:12],
                                        "expected_failure_modes": plan_obj.expected_failure_modes[:12],
                                        "intended_evidence": plan_obj.intended_evidence[:12],
                                        "next_actions": (plan_obj.next_actions or [])[:3],
                                        # Flatten validation stats for pretty logs (nested dict truncates).
                                        "plan_actions_in": int(vstats.get("actions_in", 0) or 0),
                                        "plan_actions_kept": int(vstats.get("actions_kept", 0) or 0),
                                        "plan_actions_dropped_out_of_focus": int(
                                            vstats.get("actions_dropped_out_of_focus", 0) or 0
                                        ),
                                        "plan_actions_anchor_missing": int(
                                            vstats.get("actions_anchor_missing", 0) or 0
                                        ),
                                        "notes": plan_obj.notes[:8],
                                    },
                                ),
                            )
                        else:
                            emit_progress(
                                root,
                                ProgressEvent(
                                    event="plan_failed",
                                    ts=_now_iso(),
                                    phase="plan",
                                    stage=stage_name,
                                    role=role,
                                    model=m,
                                    message="plan call returned no parseable JSON (continuing)",
                                    data={"elapsed_ms": dt_ms},
                                ),
                            )

                t0 = time.perf_counter()
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
                dt_ms = int((time.perf_counter() - t0) * 1000)
                emit_progress(
                    root,
                    ProgressEvent(
                        event="model_done",
                        ts=_now_iso(),
                        phase="model",
                        stage=stage_name,
                        role=role,
                        model=m,
                        message="model call completed",
                        data={
                            "elapsed_ms": dt_ms,
                            "top_issues": int(len(rep.top_issues)),
                            "nice_to_have": int(len(rep.nice_to_have)),
                            "future_break": int(len(rep.most_likely_future_break)),
                            "meta": rep.meta[:5],
                        },
                    ),
                )
                # Optional second pass: tighten / de-hallucinate.
                if rounds >= 2:
                    emit_progress(
                        root,
                        ProgressEvent(
                            event="model_refine_start",
                            ts=_now_iso(),
                            phase="model",
                            stage=stage_name,
                            role=role,
                            model=m,
                            round=2,
                            message="starting refine pass",
                        ),
                    )
                    t1 = time.perf_counter()
                    rep2 = await run_one_report(
                        provider=provider,
                        model_id=m,
                        api_key=api_key,
                        base_url=base_url,
                        app_url=site_url,
                        app_title=app_name,
                        system_prompt=sys2,
                        user_prompt=user_prompt + "\n\n" + refine_prompt(prev_json=rep.model_dump_json()),
                        timeout_s=stage_timeout,
                    )
                    dt2_ms = int((time.perf_counter() - t1) * 1000)
                    rep2.meta = list(dict.fromkeys(rep2.meta + ["refined: true"]))[:20]
                    rep = rep2
                    emit_progress(
                        root,
                        ProgressEvent(
                            event="model_refine_done",
                            ts=_now_iso(),
                            phase="model",
                            stage=stage_name,
                            role=role,
                            model=m,
                            round=2,
                            message="refine pass completed",
                            data={
                                "elapsed_ms": dt2_ms,
                                "top_issues": int(len(rep.top_issues)),
                                "meta": rep.meta[:5],
                            },
                        ),
                    )
                if focus_files:
                    rep = apply_sorry_focus_policy(rep, focus_files=focus_files)
                try:
                    cache_path.write_text(rep.model_dump_json(indent=2), encoding="utf-8")
                except Exception:
                    pass
                return (m, rep)
            except Exception as e:
                print(
                    f"llm_review: model_failed model={m} stage={stage_name} role={role}: {type(e).__name__}: {e!r}",
                    file=sys.stderr,
                )
                emit_progress(
                    root,
                    ProgressEvent(
                        event="model_failed",
                        ts=_now_iso(),
                        phase="error",
                        stage=stage_name,
                        role=role,
                        model=m,
                        message="model call failed",
                        data={"error_type": type(e).__name__, "error": repr(e)},
                    ),
                )
                return None

        # One role by default; try models in order.
        role = roles[0] if roles else "default"
        for m in models:
            x = await run_model(m, role)
            if x is not None:
                _, rep = x
                rep.suggested_commands = []
                emit_progress(
                    root,
                    ProgressEvent(
                        event="stage_done",
                        ts=_now_iso(),
                        phase="stage",
                        stage=stage_name,
                        role=role,
                        model=m,
                        message="stage completed (first successful model)",
                        data={"top_issues": int(len(rep.top_issues)), "meta": rep.meta[:5]},
                    ),
                )
                return rep

        emit_progress(
            root,
            ProgressEvent(
                event="stage_failed",
                ts=_now_iso(),
                phase="error",
                stage=stage_name,
                role=role,
                message="all models failed for this stage",
                data={"models": models},
            ),
        )
        return ReviewReport(meta=[f"All models failed for stage={stage_name}."])

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
        final.suggested_commands.extend(r.suggested_commands)
        final.meta.extend(r.meta)

    # De-dup combined issues by (file, snippet prefix).
    combined = aggregate_reports([("combined", ReviewReport(top_issues=final.top_issues, meta=final.meta))])
    combined.nice_to_have = list(dict.fromkeys(final.nice_to_have))[:20]
    combined.most_likely_future_break = list(dict.fromkeys(final.most_likely_future_break))[:10]
    combined.suggested_commands = default_suggested_commands(scope=args.scope)
    combined.meta = list(dict.fromkeys(final.meta))[:20]

    emit_progress(
        root,
        ProgressEvent(
            event="aggregate_done",
            ts=_now_iso(),
            phase="aggregate",
            message="aggregation completed",
            data={
                "top_issues": int(len(combined.top_issues)),
                "nice_to_have": int(len(combined.nice_to_have)),
                "future_break": int(len(combined.most_likely_future_break)),
            },
        ),
    )
    print(format_report(combined))
    emit_progress(
        root,
        ProgressEvent(
            event="done",
            ts=_now_iso(),
            phase="done",
            message="llm review complete",
            data={"elapsed_ms_total": int((time.perf_counter() - t0_all) * 1000)},
        ),
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

