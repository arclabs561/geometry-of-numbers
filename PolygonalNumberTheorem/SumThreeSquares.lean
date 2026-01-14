import Mathlib.Tactic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Algebra.Ring.Parity

namespace Nat

/-! ## Legendre's Three-Square Theorem (work in progress) -/

lemma sq_mod_eight (n : ℕ) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  sorry

lemma sum_three_squares_not_seven_mod_eight (x y z : ℕ) : (x ^ 2 + y ^ 2 + z ^ 2) % 8 ≠ 7 := by
  sorry

/-- If x² + y² + z² ≡ 3 (mod 8), then x, y, z are all odd. -/
lemma all_odd_of_sum_three_squares_eq_three_mod_eight (x y z : ℕ)
    (h : (x ^ 2 + y ^ 2 + z ^ 2) % 8 = 3) : Odd x ∧ Odd y ∧ Odd z := by
  sorry

def is_three_square_exception (n : ℕ) : Prop :=
  ∃ a k : ℕ, n = 4 ^ a * (8 * k + 7)

lemma sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  sorry

lemma even_of_sq_mod_four_eq_zero (n : ℕ) (h : n ^ 2 % 4 = 0) : 2 ∣ n := by
  sorry

lemma sum_three_squares_zero_mod_four_implies_all_even (x y z : ℕ)
    (h : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0) :
    2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z := by
  sorry

lemma sum_three_squares_div_four (m x y z : ℕ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 * m) :
    ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = m := by
  sorry

theorem not_exception_of_sum_three_squares (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) → ¬ is_three_square_exception n := by
  sorry

lemma sum_three_squares_mul_sq (m k : ℕ) (h : ∃ x y z, x^2 + y^2 + z^2 = m) :
    ∃ x y z, x^2 + y^2 + z^2 = k^2 * m := by
  sorry

lemma is_three_square_exception_mul_odd_sq (m : ℕ) {k : ℕ} (hk : Odd k) :
    is_three_square_exception (k^2 * m) ↔ is_three_square_exception m := by
  sorry

lemma sum_three_squares_reduction (n : ℕ) (h : ¬ is_three_square_exception n)
    (h_sqfree : ∀ m : ℕ, Squarefree m → ¬ is_three_square_exception m → ∃ x y z, x^2 + y^2 + z^2 = m) :
    ∃ x y z, x^2 + y^2 + z^2 = n := by
  sorry

theorem sum_three_squares_of_not_exception (n : ℕ) (h : ¬ is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  sorry

theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ is_three_square_exception n :=
  ⟨not_exception_of_sum_three_squares n, sum_three_squares_of_not_exception n⟩

theorem exists_sq_add_sq_add_one_mod_n (n : ℕ) (hn : Odd n) (hn_pos : 0 < n) :
    ∃ u v : ℤ, u ^ 2 + v ^ 2 + 1 ≡ 0 [ZMOD n] := by
  sorry

end Nat
