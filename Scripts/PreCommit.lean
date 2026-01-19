import Lean

/-!
`lake exe gon_precommit`

This is a convenience wrapper for humans.

Design constraints:
- DO NOT hook into `lake build` (build should stay deterministic/offline).
- Reuse the repo's single check entrypoint (`./Scripts/check.sh pre-commit`).
- Avoid fancy argument parsing; this is intended to be simple and boring.
-/

open Lean

def main : IO Unit := do
  -- Run from repo root (Lake runs executables from the package root, but be explicit).
  let repoRoot ← IO.currentDir
  let script : System.FilePath := repoRoot / "Scripts" / "check.sh"
  if !(← script.pathExists) then
    throw <| IO.userError s!"gon_precommit: missing {script}"

  let child ← IO.Process.spawn {
    cmd := script.toString
    args := #["pre-commit"]
    -- Preserve environment; `check.sh` already supports opt-outs via env vars.
    cwd := some repoRoot
    stdin := .inherit
    stdout := .inherit
    stderr := .inherit
  }
  let code ← child.wait
  match code with
  | 0 => pure ()
  | n => throw <| IO.userError s!"gon_precommit: failed (exit={n})"

