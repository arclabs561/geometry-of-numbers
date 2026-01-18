import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

import Covolume.Core.MinkowskiHelpers

/-!
# Ankeny ellipsoid using the L2 ball (probe)

Goal: build a *correct* ellipsoid volume computation while keeping the lattice ambient type
as `Fin 3 → ℝ`.

Key idea: define the Euclidean ball in `E3 := Fin 3 → ℝ` as a preimage under
`WithLp.toLp 2 : E3 → EuclideanSpace ℝ (Fin 3)`, then reuse:

- `PiLp.volume_preserving_toLp` (measure-preserving bridge)
- `EuclideanSpace.volume_ball_fin_three`
- `Measure.addHaar_preimage_linearMap` (volume scaling under linear maps)

This is the clean path we’ll port into `Covolume/Legendre/Ankeny.lean`.
-/

noncomputable section

namespace Covolume.Experiments

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal BigOperators

abbrev E3 := Fin 3 → ℝ
abbrev E3L2 := EuclideanSpace ℝ (Fin 3)

def l2Ball (r : ℝ) : Set E3 :=
  (WithLp.toLp (2 : ℝ≥0∞)) ⁻¹' Metric.ball (0 : E3L2) r

lemma volume_l2Ball (r : ℝ) :
    volume (l2Ball r) = (ENNReal.ofReal r) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) := by
  -- First: measure-preserving bridge says volume preimage = volume image ball.
  have hpre :
      volume (l2Ball r) = volume (Metric.ball (0 : E3L2) r) := by
    simpa [l2Ball] using
      (PiLp.volume_preserving_toLp (ι := Fin 3)).measure_preimage measurableSet_ball.nullMeasurableSet
  -- Second: explicit 3-ball volume.
  have hball :
      volume (Metric.ball (0 : E3L2) r) =
        (ENNReal.ofReal r) ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) :=
    EuclideanSpace.volume_ball_fin_three (x := (0 : E3L2)) (r := r)
  simpa [hpre, hball]

def ankenyEllipsoidL2 (n q : ℝ) : Set E3 :=
  Covolume.Minkowski.ankenyDiagMap n q ⁻¹' l2Ball (Covolume.Minkowski.ankenyBallRadius n q)

lemma volume_ankenyEllipsoidL2 (n q : ℝ) :
    volume (ankenyEllipsoidL2 n q) =
      ENNReal.ofReal |(LinearMap.det (Covolume.Minkowski.ankenyDiagMap n q))⁻¹| *
        ((ENNReal.ofReal (Covolume.Minkowski.ankenyBallRadius n q)) ^ 3 *
          ENNReal.ofReal (Real.pi * 4 / 3)) := by
  -- This is the clean formula we use in the main proof (where `det ≠ 0` is easy from positivity).
  -- In this experiment file we keep it as a scaffold to avoid dealing with the degenerate `det = 0` case.
  by_cases hdet_ne0 : LinearMap.det (Covolume.Minkowski.ankenyDiagMap n q) ≠ 0
  · have hpre :
        volume (ankenyEllipsoidL2 n q) =
          ENNReal.ofReal |(LinearMap.det (Covolume.Minkowski.ankenyDiagMap n q))⁻¹| *
            volume (l2Ball (Covolume.Minkowski.ankenyBallRadius n q)) := by
      simpa [ankenyEllipsoidL2] using
        (MeasureTheory.Measure.addHaar_preimage_linearMap
          (μ := (volume : Measure E3))
          (f := Covolume.Minkowski.ankenyDiagMap n q)
          hdet_ne0
          (l2Ball (Covolume.Minkowski.ankenyBallRadius n q)))
    simp [hpre, volume_l2Ball]
  · -- Degenerate case: we do not need it for Ankeny; keep as a marked placeholder.
    sorry

end Covolume.Experiments

