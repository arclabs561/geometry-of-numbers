import Mathlib.Data.Nat.Prime
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Ankeny route: quick checks (scratch)

Copied from `../Scripts/AnkenyCheck.lean` so the repo contains the exploration.

This is not a proof. It’s a small “compute the congruence conditions” script for the Ankeny setup.
-/

open Nat

def checkAnkenyCondition (n : ℕ) (q : ℕ) : String :=
  if ¬ n.Squarefree then "n not squarefree"
  else if n % 8 != 3 then "n not 3 mod 8"
  else if ¬ q.Prime then "q not prime"
  else if q % (4 * n) != (4 * n - 1) then "q not -1 mod 4n"
  else
    let leg_minus_one := LegendreSymbol.legendre (-1 : ℤ) q
    let leg_n := LegendreSymbol.legendre n q
    let leg_minus_n := LegendreSymbol.legendre (-n : ℤ) q
    s!"n={n}, q={q}: (-1/q)={leg_minus_one}, (n/q)={leg_n}, (-n/q)={leg_minus_n}"

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

#eval main

