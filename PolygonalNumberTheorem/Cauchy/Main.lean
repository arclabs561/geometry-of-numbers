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
  sorry

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
  sorry

/-- The "small n" case for Fermat's Polygonal Number Theorem. -/
lemma fermat_polygonal_small (s : ℕ) (hs : 3 ≤ s) (n : ℕ) (hn : n < 108 * (s - 2)) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  sorry

/-- Fermat's Polygonal Number Theorem. -/
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  sorry

end PolygonalNumberTheorem
