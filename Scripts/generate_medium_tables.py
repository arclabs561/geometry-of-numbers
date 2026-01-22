#!/usr/bin/env -S uv run
# /// script
# requires-python = ">=3.11"
# ///
"""
Generate artifacts for the Cauchy “medium regime” (bounded search + certification).

This repo contains generated Lean tables used by `GeometryOfNumbers/Cauchy/Main.lean`:

- Small band (`5 ≤ s ≤ 23`): shards under `GeometryOfNumbers/Cauchy/MediumTablesSmall/S05.lean` … `S23.lean`
- Large-m band (`m := s-2 ≥ 22`): currently *kept as a committed Lean file*.

This script has two goals:

1. **Small band regeneration (Lean)**: rewrite the shard headers and contents deterministically.
2. **Large-m provenance (data)**: regenerate the table *data* for `m ≥ 22` into `.generated/` for audit/diffing,
   without overwriting the committed Lean proof module.

By default we write into `.generated/` so the script is safe to run.

Usage:

  uv run Scripts/generate_medium_tables.py --only small
  uv run Scripts/generate_medium_tables.py --only mge22

To overwrite committed shard files (dangerous; large diffs):

  uv run Scripts/generate_medium_tables.py --only small --write-inplace
"""

from __future__ import annotations

import argparse
import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple


def triangular_pred(t: int) -> int:
    # Matches `cauchyTriPred t := t*(t-1)/2` in Lean.
    return (t * (t - 1)) // 2


def polygonal(s: int, t: int) -> int:
    # Matches `GeometryOfNumbers.polygonal`:
    # polygonal s t = t + ((s-2)*t*(t-1))/2
    return t + (s - 2) * triangular_pred(t)


@dataclass(frozen=True)
class Quad:
    t: int
    u: int
    v: int
    w: int

    @property
    def bsum(self) -> int:
        return self.t + self.u + self.v + self.w


def pair_sums_first(vals: List[int]) -> Dict[int, Tuple[int, int]]:
    """
    Deterministic map: sum -> first (i,j) (lexicographic in i then j).
    """
    out: Dict[int, Tuple[int, int]] = {}
    for i in range(len(vals)):
        for j in range(len(vals)):
            s = vals[i] + vals[j]
            if s not in out:
                out[s] = (i, j)
    return out


def find_sum4_with_r_from_pairs(
    pair_sums: Dict[int, Tuple[int, int]],
    target: int,
    r_max: int,
) -> Optional[Tuple[Quad, int]]:
    """
    Find t,u,v,w and r in [0..r_max] such that vals[t]+vals[u]+vals[v]+vals[w]+r = target.

    Deterministic search order:
    - increasing r
    - increasing pair sum keys (numeric)
    """
    keys = sorted(pair_sums.keys())
    for r in range(r_max + 1):
        want = target - r
        if want < 0:
            continue
        for s_left in keys:
            s_right = want - s_left
            if s_right not in pair_sums:
                continue
            t, u = pair_sums[s_left]
            v, w = pair_sums[s_right]
            return Quad(t, u, v, w), r
    return None


def emit_small_shard(s: int, n_max: int, entries: List[Tuple[int, int, int, int, int]]) -> str:
    assert len(entries) == n_max + 1
    def_name = f"cauchyMediumSmall_s{s}"
    spec_name = f"cauchyMediumSmall_s{s}_spec"

    out: List[str] = []
    out.append("import GeometryOfNumbers.Core.Basic\n")
    out.append("import Mathlib.Tactic.IntervalCases\n\n")
    out.append("namespace GeometryOfNumbers\n\n")
    out.append("-- GENERATED FILE: do not edit by hand.\n")
    out.append("-- Regenerate with:\n")
    out.append("--   uv run Scripts/generate_medium_tables.py --only small --write-inplace\n")
    out.append("\n")
    out.append("set_option linter.unusedVariables false\n")
    out.append("set_option linter.unusedSimpArgs false\n")
    out.append("set_option linter.unnecessarySimpa false\n")
    out.append("set_option linter.unusedTactic false\n")
    out.append("set_option linter.unreachableTactic false\n")
    out.append("set_option autoImplicit false\n")
    out.append("set_option maxRecDepth 20000\n")
    out.append("set_option maxHeartbeats 2000000\n")
    out.append("set_option synthInstance.maxHeartbeats 2000000\n")
    out.append("/-!\n")
    out.append("## Generated: bounded medium regime for small `s`\n\n")
    out.append("Scope: `s ∈ {5..23}` and `n ≤ 108 * (s-2)`.\n")
    out.append("The witnesses are bounded by `t,u,v,w ≤ 20` and `r ≤ s-4`.\n\n")
    out.append("Regenerate with:\n\n")
    out.append("- `uv run Scripts/generate_medium_tables.py --only small --write-inplace`\n")
    out.append("-/\n\n")

    out.append(f"def {def_name} (n : Fin ({n_max} + 1)) : Nat × Nat × Nat × Nat × Nat :=\n")
    out.append("  match n.1 with\n")
    for n, (t, u, v, w, r) in enumerate(entries):
        out.append(f"  | {n} => ({t}, {u}, {v}, {w}, {r})\n")
    out.append("  | _ => (0, 0, 0, 0, 0)\n\n")
    # Important: keep the statement in `∀ ...` form so `native_decide` can introduce binders
    # (older `native_decide` implementations call `introN` unconditionally).
    out.append(f"lemma {spec_name} :\n")
    out.append(f"    ∀ n : Fin ({n_max} + 1), n.1 ≠ 0 → ¬ n.1 ≤ {s} - 3 →\n")
    out.append(f"      (let (t, u, v, w, r) := {def_name} n\n")
    out.append(
        f"      r ≤ {s} - 4 ∧ polygonal {s} t + polygonal {s} u + polygonal {s} v + polygonal {s} w + r = n.1) := by\n"
    )
    # `native_decide` requires a closed goal; `+revert` asks it to revert free variables first.
    out.append("  native_decide +revert\n\n")
    out.append("end GeometryOfNumbers\n")
    return "".join(out)


def generate_small_shards(base_dir: Path, *, t_max: int = 20) -> None:
    shards_dir = base_dir / "GeometryOfNumbers" / "Cauchy" / "MediumTablesSmall"
    shards_dir.mkdir(parents=True, exist_ok=True)

    for s in range(5, 24):
        n_max = 108 * (s - 2)
        r_max = s - 4
        vals = [polygonal(s, t) for t in range(t_max + 1)]
        pairs = pair_sums_first(vals)

        entries: List[Tuple[int, int, int, int, int]] = []
        for n in range(n_max + 1):
            sol = find_sum4_with_r_from_pairs(pairs, n, r_max=r_max)
            if sol is None:
                entries.append((0, 0, 0, 0, 0))
            else:
                quad, r = sol
                entries.append((quad.t, quad.u, quad.v, quad.w, r))

        (shards_dir / f"S{s:02d}.lean").write_text(
            emit_small_shard(s=s, n_max=n_max, entries=entries),
            encoding="utf-8",
        )


def chmod_readonly(path: Path) -> None:
    # Read-only for everyone. (We deliberately do not try to preserve group/ACL semantics.)
    os.chmod(path, 0o444)


def chmod_writable_user(path: Path) -> None:
    # Owner read/write; group/other read. Enough to allow regeneration.
    os.chmod(path, 0o644)


def generate_mge22_data(base_dir: Path, *, t_max: int = 22) -> None:
    """
    Regenerate the *data* used by the `m := s-2 ≥ 22` medium-band discharge.

    We write JSON into `.generated/` for audit; the committed Lean file remains the maintained artifact.
    """
    tri = [triangular_pred(t) for t in range(t_max + 1)]

    # Precompute all pairs of triangular numbers (with witnesses), to speed up sum-of-4 search.
    #
    # IMPORTANT: we must retain *all* witnesses for a given sum, not just the first witness.
    # Some “special” cases (notably involving `q-1 = 0`) require a non-minimal (i,j) witness
    # to satisfy the b-sum constraints.
    pairs: Dict[int, List[Tuple[int, int]]] = {}
    for i in range(len(tri)):
        for j in range(len(tri)):
            s = tri[i] + tri[j]
            pairs.setdefault(s, []).append((i, j))
    pair_keys = sorted(pairs.keys())

    def find_quad_for_q_with_b_range(q_target: int, b_lo: int, b_hi: int) -> Optional[Tuple[int, int, int, int]]:
        # Find t,u,v,w with tri(t)+...=q_target and bsum in range.
        for s_left in pair_keys:
            s_right = q_target - s_left
            if s_right not in pairs:
                continue
            for (t, u) in pairs[s_left]:
                for (v, w) in pairs[s_right]:
                    b = t + u + v + w
                    if b_lo <= b <= b_hi:
                        return (t, u, v, w)
        return None

    default: Dict[int, Dict[str, int]] = {}
    special: Dict[str, Dict[str, int]] = {}

    for q in range(1, 109):
        quad = find_quad_for_q_with_b_range(q, 1, 22)
        if quad is None:
            raise RuntimeError(f"no default quad for q={q}")
        t, u, v, w = quad
        default[q] = {"b": t + u + v + w, "t": t, "u": u, "v": v, "w": w}

    for q in range(1, 109):
        b0 = default[q]["b"]
        for rem in range(0, 22):
            if rem >= b0:
                continue
            # Prefer representing q with b ≤ rem (mode=false).
            quad0 = find_quad_for_q_with_b_range(q, 1, rem) if rem >= 1 else None
            if quad0 is not None:
                t, u, v, w = quad0
                key = f"{q},{rem}"
                special[key] = {"mode": 0, "b": t + u + v + w, "t": t, "u": u, "v": v, "w": w}
                continue
            # Fallback: represent q-1 with rem+2 ≤ b ≤ rem+22 (mode=true).
            quad1 = find_quad_for_q_with_b_range(q - 1, rem + 2, rem + 22)
            if quad1 is None:
                raise RuntimeError(f"no special quad for q={q}, rem={rem}")
            t, u, v, w = quad1
            key = f"{q},{rem}"
            special[key] = {"mode": 1, "b": t + u + v + w, "t": t, "u": u, "v": v, "w": w}

    out = {
        "t_max": t_max,
        "default": default,
        "special": special,
    }
    out_path = base_dir / "mge22_tables.json"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def main(argv: Optional[List[str]] = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--only", choices=["small", "mge22", "both"], default="both")
    p.add_argument("--write-inplace", action="store_true")
    p.add_argument("--out-dir", type=Path, default=Path(".generated/cauchy_medium_tables"))
    p.add_argument("--max-t-small", type=int, default=20)
    p.add_argument("--max-t-mge22", type=int, default=22)
    args = p.parse_args(argv)

    repo_root = Path(__file__).resolve().parents[1]
    base = repo_root if args.write_inplace else repo_root / args.out_dir

    if args.only in ("small", "both"):
        if args.write_inplace:
            # Ensure shards are writable before regeneration (they may be read-only).
            shards_dir = repo_root / "GeometryOfNumbers" / "Cauchy" / "MediumTablesSmall"
            for s in range(5, 24):
                chmod_writable_user(shards_dir / f"S{s:02d}.lean")
        generate_small_shards(base, t_max=args.max_t_small)
        if args.write_inplace:
            # Flip the committed shards back to read-only as a guardrail.
            shards_dir = repo_root / "GeometryOfNumbers" / "Cauchy" / "MediumTablesSmall"
            for s in range(5, 24):
                chmod_readonly(shards_dir / f"S{s:02d}.lean")
    if args.only in ("mge22", "both"):
        # Always write mge22 data into `.generated/` even when `--write-inplace` is set.
        # The committed Lean file is the maintained artifact.
        mge22_base = repo_root / args.out_dir / "mge22"
        generate_mge22_data(mge22_base, t_max=args.max_t_mge22)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())

