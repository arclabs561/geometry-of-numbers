import PolygonalNumberTheorem.Core.Basic
import PolygonalNumberTheorem.Legendre.Main
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Int.Cast.Field

open Nat Real
open BigOperators

namespace PolygonalNumberTheorem

/-- If a real interval has length `> 2`, it contains an odd integer. -/
lemma exists_odd_in_interval {L U : ℝ} (hLU : L + 2 < U) :
    ∃ b : ℤ, Odd b ∧ L < (b : ℝ) ∧ (b : ℝ) < U := by
  let k : ℤ := Int.floor L
  let b0 : ℤ := k + 1
  let b1 : ℤ := k + 2
  have hLb0 : L < (b0 : ℝ) := by
    have h := Int.lt_floor_add_one L
    simpa [b0, k] using h
  have hb1_le : (b1 : ℝ) ≤ L + 2 := by
    have h := Int.floor_le L
    have : (b1 : ℝ) = (k : ℝ) + 2 := by simp [b1]
    linarith
  have hb1_ltU : (b1 : ℝ) < U := lt_of_le_of_lt hb1_le (by linarith)
  by_cases hb0_odd : Odd b0
  · use b0, hb0_odd, hLb0
    have : b0 < b1 := by omega
    have : (b0 : ℝ) < (b1 : ℝ) := by exact_mod_cast this
    exact lt_trans this hb1_ltU
  · have hb1_odd : Odd b1 := by
      have : b1 = b0 + 1 := by omega
      rw [this]
      exact Int.not_even_iff_odd.mp (by simpa using hb0_odd)
    use b1, hb1_odd
    have : b0 < b1 := by omega
    have : (b0 : ℝ) < (b1 : ℝ) := by exact_mod_cast this
    exact ⟨lt_trans hLb0 this, hb1_ltU⟩

/-- Nathanson/Cheung lower bound for `b` in terms of `(m,N)`. -/
noncomputable def nath_b_lb (m N : ℕ) : ℝ :=
  (1 / 2 : ℝ) + Real.sqrt (6 * (N : ℝ) / (m : ℝ) - 3)

/-- Nathanson/Cheung upper bound for `b` in terms of `(m,N)`. -/
noncomputable def nath_b_ub (m N : ℕ) : ℝ :=
  (2 / 3 : ℝ) + Real.sqrt (8 * (N : ℝ) / (m : ℝ) - 8)

/-- For `N ≥ 108m`, the Nathanson/Cheung interval has length `> 4`. -/
lemma nath_interval_len_gt_four (m N : ℕ) (hm : 3 ≤ m) (hN : 108 * m ≤ N) :
    nath_b_lb m N + 4 < nath_b_ub m N := by
  sorry

/-- Core “interval + residue coverage” step. -/
lemma exists_odd_b_and_r (m N : ℕ) (hm : 3 ≤ m) (hN : 108 * m ≤ N) :
    ∃ b : ℤ, Odd b ∧ nath_b_lb m N < (b : ℝ) ∧ (b : ℝ) < nath_b_ub m N ∧
      ∃ r : ℕ, r ≤ m - 2 ∧ (N : ℤ) - r ≡ b [ZMOD m] := by
  sorry

/-- 8n + 3 is never of the form 4^a(8k + 7). -/
lemma not_exception_eight_n_add_three (n : ℕ) :
    ¬ Nat.is_three_square_exception (8 * n + 3) := by
  intro ⟨a, k, heq⟩
  cases a with
  | zero => simp at heq; omega
  | succ a' =>
    have hmod : (8 * n + 3) % 4 = 3 := by omega
    have hpow : 4 ^ (a' + 1) * (8 * k + 7) % 4 = 0 := by
      have h4 : 4 ^ (a' + 1) = 4 * 4 ^ a' := by ring
      rw [h4, Nat.mul_assoc, Nat.mul_mod, Nat.mod_self]; simp
    rw [heq] at hmod; omega

/-- Helper: For odd `a` and odd `b` with `b² < 4a`, we have `4a - b² ≡ 3 (mod 8)`. -/
lemma four_a_minus_b_sq_mod_eight (a b : ℕ) (ha : Odd a) (hb : Odd b)
    (hcond : b ^ 2 < 4 * a) : (4 * a - b ^ 2) % 8 = 3 := by
  sorry

/-- 4a - b² is not of the exception form 4^e(8k+7). -/
lemma four_a_minus_b_sq_not_exception (a b : ℕ) (_ha_pos : 1 ≤ a) (_hb_pos : 1 ≤ b)
    (ha_odd : Odd a) (hb_odd : Odd b) (hcond : b ^ 2 < 4 * a) :
    ¬ Nat.is_three_square_exception (4 * a - b ^ 2) := by
  sorry

/-- The main Cauchy's Lemma. -/
theorem four_nonneg_sum_from_cauchy (a b : ℕ) (ha_pos : 1 ≤ a) (hb_pos : 1 ≤ b)
    (ha_odd : Odd a) (hb_odd : Odd b)
    (hcond1 : b ^ 2 < 4 * a) (hcond2 : 3 * a < b ^ 2 + 2 * b + 4) :
    ∃ s t u v : ℕ, a = s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 ∧ b = s + t + u + v := by
  sorry

/-- Existence of b, r for Cauchy's decomposition. -/
lemma exists_cauchy_b_r (m N : ℕ) (hm : 3 ≤ m) (hN : 108 * m ≤ N) :
    ∃ b r : ℕ, Odd b ∧ r ≤ m - 2 ∧ (N : ℤ) - r ≡ b [ZMOD m] ∧
      ∃ a : ℤ, (b : ℤ) ^ 2 < 4 * a ∧ 3 * a < (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4 ∧
      (m : ℤ) * (a - b) = 2 * ((N : ℤ) - b - r) ∧ 1 ≤ b ∧ Odd a.toNat := by
  sorry

/-- Given valid Cauchy conditions, express N in terms of polygonal numbers. -/
theorem cauchy_decomposition (m : ℕ) (hm : 3 ≤ m) (N : ℕ) (hN : 108 * m ≤ N) :
    ∃ p1 p2 p3 p4 : ℕ, ∃ r : ℕ,
      r ≤ m - 2 ∧
      N = polygonal (m + 2) p1 + polygonal (m + 2) p2 +
          polygonal (m + 2) p3 + polygonal (m + 2) p4 + r := by
  sorry

/-- Gauss's Eureka Theorem: every natural number is a sum of three triangular numbers. -/
theorem gauss_eureka (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n := by
  have h_not_exc : ¬ Nat.is_three_square_exception (8 * n + 3) := not_exception_eight_n_add_three n
  obtain ⟨x, y, z, hxyz⟩ := sum_three_squares_of_not_exception (8 * n + 3) h_not_exc
  have hmod : (x ^ 2 + y ^ 2 + z ^ 2) % 8 = 3 := by rw [hxyz]; omega
  obtain ⟨hx_odd, hy_odd, hz_odd⟩ := all_odd_of_sum_three_squares_eq_three_mod_eight x y z hmod
  obtain ⟨a, rfl⟩ := hx_odd; obtain ⟨b, rfl⟩ := hy_odd; obtain ⟨c, rfl⟩ := hz_odd
  use a, b, c
  apply Nat.mul_left_cancel (by decide : 0 < 8)
  have h_tri := odd_sq_eq_eight_triangular_add_one
  calc
    8 * (triangular a + triangular b + triangular c)
        = 8 * triangular a + 8 * triangular b + 8 * triangular c := by ring
    _ = (8 * triangular a + 1) + (8 * triangular b + 1) + (8 * triangular c + 1) - 3 := by
        -- Proof of 8a+8b+8c = (8a+1)+(8b+1)+(8c+1)-3 in Nat is tricky because of -3.
        -- Let's use omega or do it in Int.
        sorry
    _ = (2 * a + 1) ^ 2 + (2 * b + 1) ^ 2 + (2 * c + 1) ^ 2 - 3 := by
        rw [← h_tri, ← h_tri, ← h_tri]
    _ = (8 * n + 3) - 3 := by rw [hxyz]
    _ = 8 * n := by omega

/-- The "small n" case for Fermat's Polygonal Number Theorem. -/
lemma fermat_polygonal_small (s : ℕ) (hs : 3 ≤ s) (n : ℕ) (hn : n < 108 * (s - 2)) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  sorry

/-- Fermat's Polygonal Number Theorem. -/
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  sorry

end PolygonalNumberTheorem
