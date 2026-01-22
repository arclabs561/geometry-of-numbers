import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Minkowski / ellipsoid helpers (shared)

This file is the shared **definition layer** for the “diagonal map / ellipsoid as preimage of a
ball” normalization used in geometry-of-numbers arguments.

We intentionally keep this file *light* (definitions only). Proof-heavy facts (volume computations,
Minkowski inequalities, etc.) are developed in proof-specific files (e.g. Ankeny or experiments).
-/

noncomputable section

namespace GeometryOfNumbers.Minkowski

abbrev E3 := Fin 3 → ℝ

/-!
## Ankeny ellipsoid normalization

For Ankeny’s quadratic form

$$
Q(x,y,z) = 2q x^2 + y^2 + n z^2,
$$

the ellipsoid `Q(x) < (2*sqrt(n*q))^2` is the preimage of `ball 0 (2*sqrt(n*q))` under the diagonal
map `diag( sqrt(2q), 1, sqrt(n) )`.
-/

def ankenyDiagMap (n q : ℝ) : E3 →ₗ[ℝ] E3 :=
  Matrix.toLin' (Matrix.diagonal ![Real.sqrt (2 * q), (1 : ℝ), Real.sqrt n])

def ankenyBallRadius (n q : ℝ) : ℝ :=
  2 * Real.sqrt (n * q)

def ankenyEllipsoidAsPreimage (n q : ℝ) : Set E3 :=
  ankenyDiagMap n q ⁻¹' Metric.ball (0 : E3) (ankenyBallRadius n q)
end GeometryOfNumbers.Minkowski

