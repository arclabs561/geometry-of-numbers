import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic

/-!
# Fun detour: ball preimage → weighted sum of squares

This is a tiny “geometry glue” lemma we keep as an experiment:
turning `T ⁻¹' ball 0 R` into an explicit weighted sum-of-squares inequality for a diagonal `T`.

This is exactly the kind of rewriting needed in the Ankeny Minkowski step to go from
“point is inside ellipsoid” to “quadratic form value is bounded”.
-/

noncomputable section

namespace Covolume.Experiments

abbrev E3 := Fin 3 → ℝ

def ankenyDiagMap (n q : ℝ) : E3 →ₗ[ℝ] E3 :=
  Matrix.toLin' (Matrix.diagonal ![Real.sqrt (2 * q), (1 : ℝ), Real.sqrt n])

def ankenyBallRadius (n q : ℝ) : ℝ :=
  2 * Real.sqrt (n * q)

def ankenyEllipsoidAsPreimage (n q : ℝ) : Set E3 :=
  ankenyDiagMap n q ⁻¹' Metric.ball (0 : E3) (ankenyBallRadius n q)

/-- Ball preimage gives the expected weighted inequality.

Note: we assume `0 ≤ n` and `0 ≤ q` so we can use `Real.sq_sqrt`.
-/
lemma mem_ankenyEllipsoidAsPreimage_iff (n q : ℝ) (hn : 0 ≤ n) (hq : 0 ≤ q) (x : E3) :
    x ∈ ankenyEllipsoidAsPreimage n q ↔
      (2 * q) * (x 0) ^ 2 + (x 1) ^ 2 + n * (x 2) ^ 2 < (ankenyBallRadius n q) ^ 2 := by
  /-
  Detour note: proving this cleanly in the `Fin 3 → ℝ` presentation runs into the `WithLp`/`PiLp`
  spelling (`x.ofLp i` vs `x i`) when using `EuclideanSpace.ball_zero_eq`.

  The right fix is to either:
  - work in `EuclideanSpace ℝ (Fin 3)` directly (a type synonym), or
  - explicitly rewrite using `WithLp.ofLp_toLp` / `WithLp.toLp_ofLp` to normalize coordinates.

  This lemma isn’t a blocker (the main proof is currently developed in `CheckMinkowski.lean`);
  we keep it here as a “future cleanup” target.
  -/
  sorry

end Covolume.Experiments

