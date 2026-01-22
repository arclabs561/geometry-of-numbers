import AnkenyCheck

/-!
# Ankeny check executable (bounded, offline)

Run with:

- `lake exe ankeny_check`

This simply runs the experiment harness from `Experiments/AnkenyCheck.lean` as an executable,
so we can get concrete witnesses without adding `#eval` to `Experiments/` (which would run during
`lake build`).
-/

def main : IO Unit :=
  Experiments.AnkenyCheck.run

