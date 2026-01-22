#!/usr/bin/env -S uv run
# /// script
# requires-python = ">=3.11"
# ///
"""
Deterministic regen/audit check for Cauchy “medium regime” tables.

Contract:
- Small band shards (`S05..S23`) are generated artifacts and MUST match the generator output.
- The `mge22` generator must succeed and must produce data that satisfies the same *semantic*
  constraints as the committed Lean tables.

Note:
- The committed `GeometryOfNumbers/Cauchy/MediumTablesMge22.lean` is already self-checked by
  `native_decide` specs during `lake build`. Here we treat the generator as an *independent audit*.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Tuple


REPO_ROOT = Path(__file__).resolve().parents[1]


def run(cmd: List[str]) -> None:
    p = subprocess.run(cmd, cwd=REPO_ROOT, stdout=sys.stdout, stderr=sys.stderr)
    if p.returncode != 0:
        raise SystemExit(p.returncode)


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8")


def fail(msg: str) -> None:
    print(f"error: {msg}", file=sys.stderr)
    raise SystemExit(2)


def compare_files(a: Path, b: Path) -> None:
    ta = read_text(a)
    tb = read_text(b)
    if ta != tb:
        fail(f"mismatch: {a.relative_to(REPO_ROOT)} != {b.relative_to(REPO_ROOT)}")


def check_small_shards(out_dir: Path) -> None:
    committed_dir = REPO_ROOT / "GeometryOfNumbers" / "Cauchy" / "MediumTablesSmall"
    generated_dir = out_dir / "GeometryOfNumbers" / "Cauchy" / "MediumTablesSmall"
    for s in range(5, 24):
        fname = f"S{s:02d}.lean"
        compare_files(committed_dir / fname, generated_dir / fname)


def triangular_pred(t: int) -> int:
    return (t * (t - 1)) // 2


def tri_sum4(t: int, u: int, v: int, w: int) -> int:
    return triangular_pred(t) + triangular_pred(u) + triangular_pred(v) + triangular_pred(w)


def validate_mge22_json(json_path: Path) -> None:
    j = json.loads(read_text(json_path))
    if "default" not in j or "special" not in j:
        fail(f"bad mge22 json schema: {json_path.relative_to(REPO_ROOT)}")

    defaults = j["default"]
    specials = j["special"]
    if len(defaults) != 108:
        fail(f"mge22 json defaults has {len(defaults)} entries (expected 108)")

    # Defaults: for each q in 1..108, tri-sum must equal q and 1 <= b <= 22.
    for q in range(1, 109):
        ent = defaults.get(str(q))
        if ent is None:
            fail(f"mge22 json missing default for q={q}")
        b = int(ent["b"])
        t = int(ent["t"])
        u = int(ent["u"])
        v = int(ent["v"])
        w = int(ent["w"])
        if tri_sum4(t, u, v, w) != q:
            fail(f"mge22 default violates tri-sum at q={q}")
        if t + u + v + w != b:
            fail(f"mge22 default violates bsum at q={q}")
        if not (1 <= b <= 22):
            fail(f"mge22 default violates b range at q={q}: b={b}")

    # Specials: key format "q,rem".
    for key, ent in specials.items():
        q_str, rem_str = key.split(",")
        q = int(q_str)
        rem = int(rem_str)
        mode = int(ent["mode"])
        b = int(ent["b"])
        t = int(ent["t"])
        u = int(ent["u"])
        v = int(ent["v"])
        w = int(ent["w"])
        if mode == 0:
            if tri_sum4(t, u, v, w) != q:
                fail(f"mge22 special(mode=0) violates tri-sum at q={q},rem={rem}")
            if not (1 <= b <= rem):
                fail(f"mge22 special(mode=0) violates b range at q={q},rem={rem}: b={b}")
        elif mode == 1:
            if tri_sum4(t, u, v, w) != q - 1:
                fail(f"mge22 special(mode=1) violates tri-sum at q={q},rem={rem}")
            if not (rem + 2 <= b <= rem + 22):
                fail(f"mge22 special(mode=1) violates b range at q={q},rem={rem}: b={b}")
        else:
            fail(f"mge22 special has invalid mode at q={q},rem={rem}: mode={mode}")
        if t + u + v + w != b:
            fail(f"mge22 special violates bsum at q={q},rem={rem}")


def main(argv: List[str]) -> int:
    out_dir = REPO_ROOT / ".generated" / "cauchy_medium_tables_check"
    # Regenerate into a dedicated out dir so this is safe to run.
    run(
        [
            "uv",
            "run",
            "Scripts/generate_medium_tables.py",
            "--only",
            "both",
            "--out-dir",
            str(out_dir.relative_to(REPO_ROOT)),
        ]
    )

    check_small_shards(out_dir)

    mge22_json = out_dir / "mge22" / "mge22_tables.json"
    if not mge22_json.exists():
        fail(f"missing generator output: {mge22_json.relative_to(REPO_ROOT)}")
    validate_mge22_json(mge22_json)

    print("regen-check: ok")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

