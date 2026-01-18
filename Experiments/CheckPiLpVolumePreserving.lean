import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# Check: PiLp/WithLp volume-preserving bridge

Goal: pin down the exact names + types for the measure-preserving equivalences between
`Fin 3 → ℝ` and `EuclideanSpace ℝ (Fin 3)` (which is a `PiLp`/`WithLp` type synonym).

This is meant to avoid “guessing by simp” in the Ankeny Minkowski step.
-/

noncomputable section

namespace Covolume.Experiments

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal BigOperators

abbrev E3 := Fin 3 → ℝ
abbrev E3L2 := EuclideanSpace ℝ (Fin 3)

-- Sanity checks (names and types).
#check PiLp.volume_preserving_toLp
#check PiLp.volume_preserving_ofLp
#check EuclideanSpace.volume_ball_fin_three
#check MeasureTheory.Measure.addHaar_preimage_linearMap

-- `EuclideanSpace ℝ (Fin 3)` is (definitionally) `WithLp 2 (Fin 3 → ℝ)`.
example : E3L2 = WithLp 2 E3 := rfl

-- Smoke: the ball-volume lemma we want to reuse (as-is).
example (r : ℝ) :
    volume (Metric.ball (0 : E3L2) r) =
      (ENNReal.ofReal r) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  simpa using (EuclideanSpace.volume_ball_fin_three (x := (0 : E3L2)) (r := r))

end Covolume.Experiments

