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

open scoped BigOperators

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

end Covolume.Experiments

