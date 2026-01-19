import Lean

/-!
`lake exe status_report`

This executable is intentionally **offline** and **text-based**. Instead of hardcoding which lemmas
are missing (which quickly drifts), we scan the local source tree and count `sorry` tokens per file.

This is conservative (it counts `sorry` even in comments), but it stays truthful across refactors.
-/

open Lean

namespace Covolume.Scripts

partial def collectLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for entry in (← System.FilePath.readDir dir) do
    if (← entry.path.isDir) then
      out := out ++ (← collectLeanFiles entry.path)
    else if entry.path.extension == some "lean" then
      out := out.push entry.path
  return out

def countSorryTokens (s : String) : Nat :=
  -- Count the token `sorry` (as an identifier-like word).
  -- Still conservative (counts in comments), but avoids false positives like `"sor"` in other words.
  let sorryTok : List Char := ['s', 'o', 'r', 'r', 'y']
  let isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_'
  let flush (cur : List Char) (count : Nat) : Nat :=
    if cur == sorryTok then count + 1 else count
  let rec go (cs : List Char) (cur : List Char) (count : Nat) : Nat :=
    match cs with
    | [] => flush cur count
    | c :: cs =>
      if isIdentChar c then
        go cs (cur.concat c) count
      else
        go cs [] (flush cur count)
  go s.toList [] 0

def fileSorryCount (p : System.FilePath) : IO Nat := do
  let s ← IO.FS.readFile p
  return countSorryTokens s

def collectSorryCounts (roots : Array System.FilePath) : IO (Array (System.FilePath × Nat)) := do
  let mut out : Array (System.FilePath × Nat) := #[]
  for root in roots do
    if !(← root.pathExists) then
      continue
    let files ← collectLeanFiles root
    for f in files do
      -- Avoid self-counting: this file contains the word `sorry` in prose.
      if f == ("Scripts" / "StatusReport.lean") then
        continue
      let k ← fileSorryCount f
      if k > 0 then
        out := out.push (f, k)
  return out

def sortByCountDesc (xs : Array (System.FilePath × Nat)) : Array (System.FilePath × Nat) :=
  xs.qsort (fun a b => a.2 > b.2)

def printTop (xs : Array (System.FilePath × Nat)) (limit : Nat) : IO Unit := do
  let n := Nat.min limit xs.size
  for i in [:n] do
    let (p, k) := xs[i]!
    IO.println s!"  - {p}: {k}"

end Covolume.Scripts

def main : IO Unit := do
  IO.println "Covolume Project Status"
  IO.println "======================="
  IO.println ""
  IO.println "This is an automated status summary generated from the library source."
  IO.println "Verification state is defined by the success of the 'lake build' process."
  IO.println "Remaining technical gaps are marked with 'sorry' placeholders."
  IO.println ""

  IO.println "## Legendre's Three-Square Theorem"
  IO.println ""
  IO.println "  - Entry point: `Covolume/Legendre/Main.lean`"
  IO.println "  - Support: `Covolume/Legendre/Exceptions.lean`"
  IO.println "  - Recommended: `Covolume/Legendre/Ankeny.lean` (Ankeny 1957)"
  IO.println "  - Alternative: `Covolume/Legendre/Minkowski.lean` (descent scaffold)"
  IO.println ""
  IO.println "  Notes:"
  IO.println "  - Easy direction is proved: sum of three squares ⇒ not a three-square exception."
  IO.println "  - Remaining work is visible below as `sorry` counts per file."
  IO.println ""
  IO.println "## Polygonal Number Theorem"
  IO.println ""
  IO.println "  - Entry point: `Covolume/Cauchy/Main.lean`"
  IO.println "  - Algebra spine: `Covolume/Core/Basic.lean`"
  IO.println ""
  IO.println "  Notes:"
  IO.println "  - 'gauss_triangular' and 'fermat_polygonal' currently contain placeholders."
  IO.println "  - Scripts under `Scripts/` and scratch under `Experiments/` are for checking intuition."
  IO.println ""

  IO.println "## `sorry` summary (top files)"
  IO.println ""
  let roots : Array System.FilePath := #["Covolume", "Experiments", "Scripts", "Archive"]
  let counts ← Covolume.Scripts.collectSorryCounts roots
  let counts := Covolume.Scripts.sortByCountDesc counts
  if counts.isEmpty then
    IO.println "  (no `sorry` tokens found)"
  else
    Covolume.Scripts.printTop counts 15
  IO.println ""

  IO.println "## Dependencies (from Mathlib)"
  IO.println ""
  IO.println "  Nat.sum_four_squares    -- Lagrange's theorem"
  IO.println "  ZMod.sq_add_sq_zmodEq   -- Pigeonhole for squares mod p"
  IO.println ""
  IO.println "## Roadmap pointers"
  IO.println ""
  IO.println "  - `PROOF_ROADMAP.md` is the current dependency graph."
  IO.println "  - `doc/RecordOfProgress.md` and `doc/TechnicalNotes.md` explain pivots/shelved paths."
