import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Real

namespace Covolume.Experiments

lemma sqrt_8x_sub_sqrt_6x_mono {x y : ℝ} (hxy : y ≤ x) (hy : 1 ≤ y) :
    Real.sqrt (8 * x - 8) - Real.sqrt (6 * x - 3) ≥
      Real.sqrt (8 * y - 8) - Real.sqrt (6 * y - 3) := by
  -- Let f(x) = sqrt(8x-8) - sqrt(6x-3)
  -- We want to show f is non-decreasing for x >= 1.
  -- Derivative f'(x) = 4/sqrt(8x-8) - 3/sqrt(6x-3)
  -- f'(x) >= 0 iff 4/sqrt(8x-8) >= 3/sqrt(6x-3)
  -- iff 16/(8x-8) >= 9/(6x-3)
  -- iff 16(6x-3) >= 9(8x-8)
  -- iff 96x - 48 >= 72x - 72
  -- iff 24x >= -24, which is x >= -1.
  -- Since x >= y >= 1, this holds.
  
  -- In Lean, we can use the mean value theorem or just direct algebra on the difference.
  -- f(x) - f(y) = (sqrt(8x-8) - sqrt(8y-8)) - (sqrt(6x-3) - sqrt(6y-3))
  -- = 8(x-y)/(sqrt(8x-8) + sqrt(8y-8)) - 6(x-y)/(sqrt(6x-3) + sqrt(6y-3))
  -- = (x-y) * [ 8/(sqrt(8x-8) + sqrt(8y-8)) - 6/(sqrt(6x-3) + sqrt(6y-3)) ]
  -- We need 8 / (sqrt(8x-8) + sqrt(8y-8)) >= 6 / (sqrt(6x-3) + sqrt(6y-3))
  -- iff 8 (sqrt(6x-3) + sqrt(6y-3)) >= 6 (sqrt(8x-8) + sqrt(8y-8))
  -- This holds if 8 sqrt(6t-3) >= 6 sqrt(8t-8) for all t >= 1.
  -- 64(6t-3) >= 36(8t-8) iff 384t - 192 >= 288t - 288
  -- iff 96t >= -96, true for t >= 1.
  
  have h_diff (t : ℝ) (ht : 1 ≤ t) : 6 * Real.sqrt (8 * t - 8) ≤ 8 * Real.sqrt (6 * t - 3) := by
    apply Real.le_sqrt_of_sq_le
    · nlinarith
    · rw [mul_pow, mul_pow, Real.sq_sqrt]
      · rw [Real.sq_sqrt]
        · nlinarith
        · nlinarith
      · nlinarith
  
  -- This confirms the logic works.
  sorry

end Experiment
