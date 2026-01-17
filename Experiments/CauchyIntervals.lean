import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Real

namespace Covolume.Experiments

lemma sqrt_8x_sub_sqrt_6x_mono {x y : ℝ} (hxy : y ≤ x) (hy : 1 ≤ y) :
    Real.sqrt (8 * x - 8) - Real.sqrt (6 * x - 3) ≥
      Real.sqrt (8 * y - 8) - Real.sqrt (6 * y - 3) := by
  -- TODO: This is a real-analysis lemma useful for interval bounds in the Cauchy reduction.
  -- Keep it as a placeholder experiment: the argument should go via monotonicity (or MVT)
  -- after proving the relevant square-root expressions are defined on `[1, ∞)`.
  --
  -- We deliberately keep this file buildable even when the analytic proof is unfinished.
  sorry

end Covolume.Experiments
