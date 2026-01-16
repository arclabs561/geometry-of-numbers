import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import PolygonalNumberTheorem.Legendre.Exceptions
import PolygonalNumberTheorem.Legendre.Minkowski

namespace Nat

/-!
## Legendre's Three-Square Theorem

This file contains the top-level statement of Legendre's three-square theorem:
`n` is a sum of three squares if and only if `n ≠ 4^a(8k+7)`.
-/

/-- Helper: square of an even number is 0 mod 4. -/
lemma even_sq_mod_four (n : ℕ) (h : Even n) : n ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ := h; ring_nf; simp

/-- Helper: square of an odd number is 1 mod 4. -/
lemma odd_sq_mod_four (n : ℕ) (h : Odd n) : n ^ 2 % 4 = 1 := by
  obtain ⟨k, rfl⟩ := h; ring_nf; omega

/-- The "easy" direction: if n is a sum of three squares, it's not a three-square exception. -/
theorem not_exception_of_sum_three_squares (n : ℕ) (h : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) :
    ¬ is_three_square_exception n := by
  intro ⟨a, k, heq⟩
  induction a generalizing n with
  | zero =>
    simp at heq
    sorry
  | succ a' ih =>
    sorry

/-- Auxiliary for the hard direction: strip odd square factors. -/
lemma sum_three_squares_of_square_mul (n m : ℕ) (h : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = m ^ 2 * n := by
  sorry

/-- All odd integers x, y, z such that x^2 + y^2 + z^2 ≡ 3 (mod 8) are odd. -/
lemma all_odd_of_sum_three_squares_eq_three_mod_eight (x y z : ℕ)
    (h : (x ^ 2 + y ^ 2 + z ^ 2) % 8 = 3) :
    Odd x ∧ Odd y ∧ Odd z := by
  sorry

/-- The "hard" direction: if n is not a three-square exception, it's a sum of three squares. -/
theorem sum_three_squares_of_not_exception (n : ℕ) (h : ¬ is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  exact PolygonalNumberTheorem.minkowski_three_squares n h

end Nat
