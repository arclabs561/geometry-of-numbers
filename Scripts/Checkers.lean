import Lean

/-!
# Project checkers (CI entrypoint)

This is a small “project-owned” checker executable intended for CI.

It is intentionally conservative and text-based:
- fail if `scripts/nolints-style.txt` is non-empty (we want waivers to be explicit and rare)
- fail if we accidentally paste “strikethrough” linter-markup characters into `.lean` files

This is not meant to replace mathlib tooling (`lint-style`, docgen, etc.).
-/

open Lean

namespace GeometryOfNumbers.Scripts

def forbiddenChars : List Char :=
  -- U+0335 COMBINING SHORT STROKE OVERLAY, seen in some linter-rendered outputs.
  ['\u0335']

def hasForbiddenChar (s : String) : Bool :=
  forbiddenChars.any (fun c => s.contains c)

partial def collectLeanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out : Array System.FilePath := #[]
  for entry in (← System.FilePath.readDir dir) do
    if (← entry.path.isDir) then
      out := out ++ (← collectLeanFiles entry.path)
    else if entry.path.extension == some "lean" then
      out := out.push entry.path
  return out

def checkNoStyleWaivers : IO Unit := do
  let p : System.FilePath := "scripts/nolints-style.txt"
  let s ← IO.FS.readFile p
  let badLines :=
    s.splitOn "\n"
    |>.filterMap (fun line =>
      let t := line.trimAscii.toString
      if t.isEmpty then
        none
      else if t.startsWith "#" then
        none
      else
        some t)
  if badLines.isEmpty then
    return ()
  else
    throw <| IO.userError s!"{p}: found non-comment waiver lines:\n{String.intercalate "\n" badLines}"

def checkNoForbiddenCharsInLean : IO Unit := do
  let roots : Array System.FilePath := #["GeometryOfNumbers", "Experiments", "Scripts"]
  for root in roots do
    if !(← root.pathExists) then
      continue
    let files ← collectLeanFiles root
    for f in files do
      let s ← IO.FS.readFile f
      if hasForbiddenChar s then
        throw <| IO.userError s!"{f}: contains forbidden Unicode char(s) (likely pasted linter markup)"

def run : IO Unit := do
  checkNoStyleWaivers
  checkNoForbiddenCharsInLean
  IO.println "gon_checks: ok"

end GeometryOfNumbers.Scripts

def main : IO Unit :=
  GeometryOfNumbers.Scripts.run

