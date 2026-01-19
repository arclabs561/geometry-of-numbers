#!/usr/bin/env -S uv run
# /// script
# requires-python = ">=3.10"
# dependencies = [
#   "aristotlelib",
# ]
# ///

from __future__ import annotations

import argparse
import asyncio
import os
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Sequence


@dataclass(frozen=True)
class Repo:
    root: Path
    lake: Path


@dataclass(frozen=True)
class LeanAideRepo:
    root: Path
    lake: Path


def _find_repo_root(start: Path) -> Path:
    """
    Find the covolume repo root by walking upward until we see `lean-toolchain`
    and a Lake file.
    """
    cur = start.resolve()
    for _ in range(50):
        if (cur / "lean-toolchain").exists() and (
            (cur / "lakefile.lean").exists() or (cur / "lakefile.toml").exists()
        ):
            return cur
        if cur.parent == cur:
            break
        cur = cur.parent
    raise RuntimeError(f"Could not find Lean repo root from {start}")


def _resolve_lake(repo_root: Path) -> Path:
    """
    Use the same policy as `Scripts/check.sh`:
    - respect $LAKE if set
    - otherwise prefer ~/.elan/bin/lake
    - otherwise rely on PATH
    """
    lake_env = os.environ.get("LAKE", "").strip()
    if lake_env:
        return Path(lake_env)
    elan_lake = Path.home() / ".elan" / "bin" / "lake"
    if elan_lake.exists():
        return elan_lake
    return Path("lake")


def _repo(start: Path) -> Repo:
    root = _find_repo_root(start)
    lake = _resolve_lake(root)
    return Repo(root=root, lake=lake)


def _run(cmd: Sequence[str], *, cwd: Path, check: bool = True) -> int:
    proc = subprocess.run(list(cmd), cwd=str(cwd))
    if check and proc.returncode != 0:
        raise SystemExit(proc.returncode)
    return proc.returncode


def cmd_check(args: argparse.Namespace) -> None:
    repo = _repo(Path.cwd())
    script = repo.root / "Scripts" / "check.sh"
    if not script.exists():
        raise RuntimeError(f"Missing {script}")
    cmd = [str(script), args.profile]
    if args.github:
        cmd.append("--github")
    _run(cmd, cwd=repo.root)


def cmd_build(args: argparse.Namespace) -> None:
    repo = _repo(Path.cwd())
    cmd = [str(repo.lake), "build"]
    if args.target:
        cmd.append(args.target)
    _run(cmd, cwd=repo.root)


def cmd_status(args: argparse.Namespace) -> None:
    repo = _repo(Path.cwd())
    _run([str(repo.lake), "exe", "status_report"], cwd=repo.root)


def _leanaide_root(covolume_root: Path) -> Path:
    # Default: a sibling repo next to `covolume/`.
    # Override with `LEANAIDE_REPO_ROOT=/path/to/LeanAide`.
    env = os.environ.get("LEANAIDE_REPO_ROOT", "").strip()
    if env:
        return Path(env).expanduser()
    return (covolume_root.parent / "LeanAide").resolve()


def _leanaide_repo(covolume_root: Path) -> LeanAideRepo:
    root = _leanaide_root(covolume_root)
    lake = _resolve_lake(root)
    return LeanAideRepo(root=root, lake=lake)


def _git_clone(url: str, dest: Path) -> None:
    if dest.exists():
        return
    dest.parent.mkdir(parents=True, exist_ok=True)
    _run(["git", "clone", "--depth", "1", url, str(dest)], cwd=dest.parent)


def cmd_leanaide_setup(args: argparse.Namespace) -> None:
    repo = _repo(Path.cwd())
    la = _leanaide_repo(repo.root)

    _git_clone("https://github.com/siddhartha-gadgil/LeanAide.git", la.root)

    # These are upstream-recommended setup steps. They can be slow and/or require network.
    if args.cache_get:
        _run([str(la.lake), "exe", "cache", "get"], cwd=la.root)
    if args.build_mathlib:
        _run([str(la.lake), "build", "mathlib"], cwd=la.root)
    if args.build:
        _run([str(la.lake), "build"], cwd=la.root)
    if args.fetch_embeddings:
        _run([str(la.lake), "exe", "fetch_embeddings"], cwd=la.root)


def cmd_leanaide_translate(args: argparse.Namespace) -> None:
    repo = _repo(Path.cwd())
    la = _leanaide_repo(repo.root)
    if not la.root.exists():
        raise RuntimeError(
            f"LeanAide repo not found at {la.root}. Run `lean_helper.py leanaide setup` first "
            f"or set LEANAIDE_REPO_ROOT."
        )
    # LeanAide translate typically needs OpenAI credentials by default.
    if not os.environ.get("OPENAI_API_KEY"):
        raise RuntimeError("OPENAI_API_KEY is not set (LeanAide translate typically requires it).")
    _run([str(la.lake), "exe", "translate", args.text], cwd=la.root)


async def _aristotle_prove_file(
    *,
    input_file_path: Path,
    output_file_path: Optional[Path],
    auto_add_imports: bool,
    validate_lean_project: bool,
    wait_for_completion: bool,
    polling_interval_seconds: int,
    max_polling_failures: int,
) -> str:
    # Import inside the function so non-Aristotle subcommands don't pay the import cost.
    from aristotlelib import Project

    # Load local `.env` at repo root (if present) to pick up ARISTOTLE_API_KEY.
    repo = _repo(Path.cwd())
    env_path = repo.root / ".env"
    if env_path.exists():
        for raw in env_path.read_text(encoding="utf-8").splitlines():
            line = raw.strip()
            if not line or line.startswith("#") or "=" not in line:
                continue
            k, v = line.split("=", 1)
            k = k.strip()
            v = v.strip().strip('"').strip("'")
            if k and os.environ.get(k) in (None, ""):
                os.environ[k] = v

    api_key = os.environ.get("ARISTOTLE_API_KEY")
    if not api_key:
        raise RuntimeError("ARISTOTLE_API_KEY is not set.")

    return await Project.prove_from_file(
        input_file_path=str(input_file_path),
        output_file_path=str(output_file_path) if output_file_path else None,
        auto_add_imports=auto_add_imports,
        context_file_paths=None,
        validate_lean_project=validate_lean_project,
        wait_for_completion=wait_for_completion,
        polling_interval_seconds=polling_interval_seconds,
        max_polling_failures=max_polling_failures,
    )


def cmd_aristotle(args: argparse.Namespace) -> None:
    repo = _repo(Path.cwd())
    input_path = (repo.root / args.file).resolve() if not Path(args.file).is_absolute() else Path(args.file)
    if not input_path.exists():
        raise RuntimeError(f"Input file does not exist: {input_path}")

    output_path: Optional[Path]
    if args.output:
        output_path = (repo.root / args.output).resolve() if not Path(args.output).is_absolute() else Path(args.output)
    else:
        output_path = None

    result = asyncio.run(
        _aristotle_prove_file(
            input_file_path=input_path,
            output_file_path=output_path,
            auto_add_imports=args.auto_add_imports,
            validate_lean_project=not args.no_validate_lean_project,
            wait_for_completion=not args.no_wait,
            polling_interval_seconds=args.poll_interval,
            max_polling_failures=args.max_poll_failures,
        )
    )
    print(result)


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="lean_helper.py",
        description="Local Lean helper (lake + status + Aristotle + LeanAide) for covolume.",
    )
    sub = p.add_subparsers(dest="cmd", required=True)

    p_check = sub.add_parser("check", help="Run canonical checks via Scripts/check.sh")
    p_check.add_argument("profile", choices=["pre-commit", "pre-push", "ci"])
    p_check.add_argument("--github", action="store_true")
    p_check.set_defaults(func=cmd_check)

    p_build = sub.add_parser("build", help="Run lake build (optional target)")
    p_build.add_argument("--target", help="Optional lake target, e.g. Covolume.Legendre.Ankeny")
    p_build.set_defaults(func=cmd_build)

    p_status = sub.add_parser("status", help="Run lake exe status_report")
    p_status.set_defaults(func=cmd_status)

    p_la = sub.add_parser("leanaide", help="LeanAide integration (clone/setup + translate)")
    la_sub = p_la.add_subparsers(dest="leanaide_cmd", required=True)

    p_la_setup = la_sub.add_parser("setup", help="Clone LeanAide and optionally run setup steps")
    p_la_setup.add_argument("--cache-get", action="store_true", help="Run `lake exe cache get` in LeanAide")
    p_la_setup.add_argument("--build-mathlib", action="store_true", help="Run `lake build mathlib` in LeanAide")
    p_la_setup.add_argument("--build", action="store_true", help="Run `lake build` in LeanAide")
    p_la_setup.add_argument(
        "--fetch-embeddings", action="store_true", help="Run `lake exe fetch_embeddings` in LeanAide"
    )
    p_la_setup.set_defaults(func=cmd_leanaide_setup)

    p_la_tr = la_sub.add_parser("translate", help="Run LeanAide translate on a natural-language statement")
    p_la_tr.add_argument("text", help='Natural-language theorem/definition, e.g. "There are infinitely many primes"')
    p_la_tr.set_defaults(func=cmd_leanaide_translate)

    p_ar = sub.add_parser("aristotle", help="Run Aristotle on a .lean file (remote service)")
    p_ar.add_argument("file", help="Input .lean file path (relative to repo root or absolute)")
    p_ar.add_argument("--output", help="Optional output file path to write (relative or absolute)")
    p_ar.add_argument("--auto-add-imports", action="store_true", help="Let Aristotle add missing imports")
    p_ar.add_argument("--no-validate-lean-project", action="store_true", help="Skip Lean project validation")
    p_ar.add_argument("--no-wait", action="store_true", help="Return early without waiting for completion")
    p_ar.add_argument("--poll-interval", type=int, default=30)
    p_ar.add_argument("--max-poll-failures", type=int, default=3)
    p_ar.set_defaults(func=cmd_aristotle)

    return p


def main(argv: Sequence[str]) -> None:
    p = build_parser()
    args = p.parse_args(list(argv))
    args.func(args)


if __name__ == "__main__":
    main(sys.argv[1:])

