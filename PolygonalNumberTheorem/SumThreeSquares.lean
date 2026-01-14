import Mathlib.Tactic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Algebra.Ring.Parity

namespace Nat

/-! ## Legendre's Three-Square Theorem (work in progress) -/

lemma sq_mod_eight (n : ℕ) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  have hkey : n ^ 2 % 8 = (n % 8) ^ 2 % 8 := Nat.pow_mod n 2 8
  rw [hkey]
  have h : n % 8 < 8 := Nat.mod_lt n (by decide : 0 < 8)
  interval_cases (n % 8) <;> decide

lemma sum_three_squares_not_seven_mod_eight (x y z : ℕ) : (x ^ 2 + y ^ 2 + z ^ 2) % 8 ≠ 7 := by
  -- Each square mod 8 is in {0, 1, 4}, so sum mod 8 is in {0,1,2,3,4,5,6}
  obtain h1 | h1 | h1 := sq_mod_eight x
  all_goals obtain h2 | h2 | h2 := sq_mod_eight y
  all_goals obtain h3 | h3 | h3 := sq_mod_eight z
  all_goals omega

/-- Helper: if n² % 8 = 1, then n is odd. -/
lemma odd_of_sq_mod_eight_eq_one (n : ℕ) (h : n ^ 2 % 8 = 1) : Odd n := by
  rw [Nat.odd_iff]
  have hkey : n ^ 2 % 8 = (n % 8) ^ 2 % 8 := Nat.pow_mod n 2 8
  rw [hkey] at h
  have h8 : n % 8 < 8 := Nat.mod_lt n (by decide : 0 < 8)
  have h2 : n % 2 = n % 8 % 2 := (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).symm
  interval_cases (n % 8) <;> simp_all

/-- If x² + y² + z² ≡ 3 (mod 8), then x, y, z are all odd. -/
lemma all_odd_of_sum_three_squares_eq_three_mod_eight (x y z : ℕ)
    (h : (x ^ 2 + y ^ 2 + z ^ 2) % 8 = 3) : Odd x ∧ Odd y ∧ Odd z := by
  -- The only way to get 3 mod 8 from three values in {0,1,4} is 1+1+1=3.
  obtain h1 | h1 | h1 := sq_mod_eight x
  all_goals obtain h2 | h2 | h2 := sq_mod_eight y
  all_goals obtain h3 | h3 | h3 := sq_mod_eight z
  all_goals try omega
  exact ⟨odd_of_sq_mod_eight_eq_one x h1, odd_of_sq_mod_eight_eq_one y h2, odd_of_sq_mod_eight_eq_one z h3⟩

def is_three_square_exception (n : ℕ) : Prop :=
  ∃ a k : ℕ, n = 4 ^ a * (8 * k + 7)

lemma sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have hkey : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := Nat.pow_mod n 2 4
  rw [hkey]
  have h : n % 4 < 4 := Nat.mod_lt n (by decide : 0 < 4)
  interval_cases (n % 4) <;> decide

lemma even_of_sq_mod_four_eq_zero (n : ℕ) (h : n ^ 2 % 4 = 0) : 2 ∣ n := by
  -- If n is odd, then n^2 % 4 = 1, contradiction.
  rw [Nat.dvd_iff_mod_eq_zero]
  have hkey : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := Nat.pow_mod n 2 4
  rw [hkey] at h
  have h4 : n % 4 < 4 := Nat.mod_lt n (by decide : 0 < 4)
  have h2 : n % 2 = n % 4 % 2 := (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)).symm
  interval_cases (n % 4) <;> simp_all

lemma sum_three_squares_zero_mod_four_implies_all_even (x y z : ℕ)
    (h : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0) :
    2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z := by
  -- Squares mod 4 are in {0, 1}. Sum = 0 mod 4 iff each is 0 mod 4.
  obtain h1 | h1 := sq_mod_four x
  all_goals obtain h2 | h2 := sq_mod_four y
  all_goals obtain h3 | h3 := sq_mod_four z
  all_goals try omega
  exact ⟨even_of_sq_mod_four_eq_zero x h1, even_of_sq_mod_four_eq_zero y h2, even_of_sq_mod_four_eq_zero z h3⟩

lemma sum_three_squares_div_four (m x y z : ℕ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 * m) :
    ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = m := by
  have hmod : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0 := by rw [h]; simp
  obtain ⟨hx, hy, hz⟩ := sum_three_squares_zero_mod_four_implies_all_even x y z hmod
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  obtain ⟨z', hz'⟩ := hz
  use x', y', z'
  have : (2 * x') ^ 2 + (2 * y') ^ 2 + (2 * z') ^ 2 = 4 * m := by rw [← hx', ← hy', ← hz']; exact h
  linarith [sq_nonneg x', sq_nonneg y', sq_nonneg z']

theorem not_exception_of_sum_three_squares (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) → ¬ is_three_square_exception n := by
  sorry

lemma sum_three_squares_mul_sq (m k : ℕ) (h : ∃ x y z, x^2 + y^2 + z^2 = m) :
    ∃ x y z, x^2 + y^2 + z^2 = k^2 * m := by
  obtain ⟨x, y, z, hxyz⟩ := h
  use k * x, k * y, k * z
  calc (k * x) ^ 2 + (k * y) ^ 2 + (k * z) ^ 2
      = k ^ 2 * x ^ 2 + k ^ 2 * y ^ 2 + k ^ 2 * z ^ 2 := by ring
    _ = k ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by ring
    _ = k ^ 2 * m := by rw [hxyz]

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
