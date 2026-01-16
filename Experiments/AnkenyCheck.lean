import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Ankeny route: quick checks (scratch)

Copied from `../Scripts/AnkenyCheck.lean` so the repo contains the exploration.

This is not a proof. It’s a small “compute the congruence conditions” script for the Ankeny setup.
-/

open Nat
open scoped NumberTheorySymbols

-- Scratch “API probes” for the `exists_ankeny_b` step in `Legendre/Ankeny.lean`.
#check jacobiSym.at_neg_two
#check jacobiSym.quadratic_reciprocity_one_mod_four
#check jacobiSym.mod_left'
#check ZMod.isSquare_of_jacobiSym_eq_one
#check ZMod.chineseRemainder
#check Int.modEq_and_modEq_iff_modEq_mul

def checkAnkenyCondition (n : ℕ) (q : ℕ) : String :=
  if n % 8 != 3 then "n not 3 mod 8"
  else if ¬ q.Prime then "q not prime"
  else if q % (4 * n) != (4 * n - 1) then "q not -1 mod 4n"
  else
    s!"n={n}, q={q}: passes basic congruence checks"

-- Find the first such prime q for a given n
def findAnkenyPrime (n : ℕ) (search_limit : ℕ) : Option ℕ :=
  (List.range search_limit).find? (fun q =>
    q.Prime ∧ q % (4 * n) == (4 * n - 1))

def main : IO Unit := do
  let ns := [3, 11, 19, 27] -- 27 is not squarefree (div by 9), just to check
  for n in ns do
    match findAnkenyPrime n 1000 with
    | some q => IO.println (checkAnkenyCondition n q)
    | none => IO.println s!"No prime found for n={n} within limit"

-- `#eval` is intentionally omitted here; keep this file as a static scratchpad.

