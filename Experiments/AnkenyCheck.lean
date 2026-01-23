import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Ankeny route: quick checks (scratch)

This is not a proof. It’s a small “compute the congruence conditions” scratchpad for the Ankeny setup.

What we want to mirror (for sanity, on small inputs) is the *prime choice* lemma in the main proof:

- `GeometryOfNumbers.exists_ankeny_prime` (in `GeometryOfNumbers/Legendre/Ankeny.lean`)

That lemma chooses a prime `q` such that:

- `q % 4 = 1`
- `(q : ZMod n) = - (2 : ZMod n)⁻¹`

The second bullet is equivalent to the arithmetic check:

- `2*q ≡ -1 (mod n)`  i.e.  `(2*q + 1) % n = 0`

We also print a couple Jacobi symbols that drive the “square root exists” step:

- `J(q | n)` and `J(-n | q)`
-/

open Nat
open scoped NumberTheorySymbols

namespace Experiments.AnkenyCheck

-- Scratch “API probes” for the `exists_ankeny_b` step in `Legendre/Ankeny.lean`.
private def _probe_jacobi_at_neg_two := @jacobiSym.at_neg_two
private def _probe_jacobi_qr_one_mod_four := @jacobiSym.quadratic_reciprocity_one_mod_four
private def _probe_jacobi_mod_left := @jacobiSym.mod_left'
private def _probe_isSquare_of_jacobi := @ZMod.isSquare_of_jacobiSym_eq_one
private def _probe_chinese_remainder := @ZMod.chineseRemainder
private def _probe_modEq_and_iff_modEq_mul := @Int.modEq_and_modEq_iff_modEq_mul

-- Scratch probes for the `reduction_to_sum_three_squares` step:
-- (We want to reuse Fermat/SumTwoSquares results instead of re-proving them.)
private def _probe_prime_sq_add_sq := @Nat.Prime.sq_add_sq
private def _probe_eq_sq_add_sq_of_isSquare := @Nat.eq_sq_add_sq_of_isSquare_mod_neg_one
private def _probe_eq_sq_add_sq_iff := @Nat.eq_sq_add_sq_iff
private def _probe_eq_sq_add_sq_iff_eq_sq_mul := @Nat.eq_sq_add_sq_iff_eq_sq_mul

-- “Toy” application: if we can show `IsSquare (-1 : ZMod n)`, we get a sum-of-two-squares witness.
example {n : ℕ} (h : IsSquare (-1 : ZMod n)) : ∃ x y : ℕ, n = x ^ 2 + y ^ 2 :=
  Nat.eq_sq_add_sq_of_isSquare_mod_neg_one h

def checkAnkenyCondition (n : ℕ) (q : ℕ) : String :=
  if n = 0 then "n = 0 (skip)"
  else if n % 2 != 1 then "n not odd (2 not invertible mod n)"
  else if ¬ q.Prime then "q not prime"
  else if q % 4 != 1 then "q not 1 mod 4"
  else if (2 * q + 1) % n != 0 then "fails 2*q ≡ -1 (mod n)"
  else
    let jq_n : ℤ := J((q : ℤ) | n)
    let jneg_n_q : ℤ := J(-(n : ℤ) | q)
    s!"n={n}, q={q}: ok; J(q|n)={jq_n}, J(-n|q)={jneg_n_q}"

def ankenyPrimeOk (n q : ℕ) : Bool :=
  (n != 0) &&
  (n % 2 == 1) &&
  (decide q.Prime) &&
  (q % 4 == 1) &&
  ((2 * q + 1) % n == 0)

-- Find the first such prime `q` for a given `n` (bounded search, for experiments only).
def findAnkenyPrime (n : ℕ) (search_limit : ℕ) : Option ℕ :=
  (List.range search_limit).find? (fun q => ankenyPrimeOk n q)

-- Brute-force a square root of `-n` modulo `q` (as a Nat representative in `[0,q)`).
def findB (n q : ℕ) : Option ℕ :=
  (List.range q).find? (fun b => ((b : ZMod q) ^ 2) == (-(n : ZMod q)))

def run : IO Unit := do
  let ns := [3, 11, 19, 27] -- include 27: still 3 mod 8, but not squarefree
  for n in ns do
    match findAnkenyPrime n 20000 with
    | none =>
        IO.println s!"n={n}: no q found within limit"
    | some q =>
        IO.println (checkAnkenyCondition n q)
        if q.Prime then
          match findB n q with
          | none => IO.println "  (no b found with b^2 ≡ -n mod q in [0,q))"
          | some b =>
              IO.println s!"  witness b={b} with (b^2 ≡ -n mod q) [checked by brute force]"
        else
          pure ()

-- `#eval` is intentionally omitted here; keep this file as a static scratchpad.

end Experiments.AnkenyCheck

