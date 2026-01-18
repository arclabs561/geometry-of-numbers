import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Ankeny: constant-side inequalities (experiment)

These are small, stable facts that we repeatedly need in the Minkowski/volume inequality:

- \( \pi > 3 \)
- \( \sqrt 2 > 1 \)
- hence \( \frac{\sqrt 2 \pi}{3} > 1 \)

and a handy algebraic identity:

\[
\frac{8}{\sqrt 2} = 4\sqrt 2.
\]
-/

noncomputable section

namespace Covolume.Experiments

open scoped BigOperators NNReal ENNReal

lemma one_lt_sqrt2_mul_pi_div_three : (1 : ℝ) < Real.sqrt 2 * Real.pi / 3 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hs2 : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  nlinarith

lemma eight_div_sqrt_two : (8 : ℝ) / Real.sqrt 2 = 4 * Real.sqrt 2 := by
  have hs2 : (Real.sqrt 2) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith))
  -- Clear denominators.
  field_simp [hs2]
  -- `√2 * √2 = 2`.
  have : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    simpa [pow_two] using (Real.sq_sqrt (by nlinarith : 0 ≤ (2 : ℝ)))
  nlinarith [this]

lemma one_lt_sqrt2_mul_pi_div_three_ennreal :
    (1 : ℝ≥0∞) < ENNReal.ofReal (Real.sqrt 2 * Real.pi / 3) := by
  -- `ofReal` is strictly monotone on nonnegative reals.
  have hpos : 0 ≤ (Real.sqrt 2 * Real.pi / 3) := by
    have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hpi : 0 ≤ Real.pi := by have := Real.pi_pos; linarith
    nlinarith
  -- Reduce to the real inequality.
  have h : (1 : ℝ) < Real.sqrt 2 * Real.pi / 3 := one_lt_sqrt2_mul_pi_div_three
  -- `ENNReal.ofReal_lt_ofReal_iff` expects nonneg; we supply it and rewrite `ofReal 1 = 1`.
  simpa using (ENNReal.ofReal_lt_ofReal_iff hpos).2 h

lemma mul_lt_mul_sqrt2_mul_pi_div_three_of_pos (a : ℝ) (ha : 0 < a) :
    a < a * (Real.sqrt 2 * Real.pi / 3) := by
  have hc : (1 : ℝ) < (Real.sqrt 2 * Real.pi / 3) := one_lt_sqrt2_mul_pi_div_three
  simpa [mul_assoc] using (mul_lt_mul_of_pos_left hc ha)

end Covolume.Experiments

