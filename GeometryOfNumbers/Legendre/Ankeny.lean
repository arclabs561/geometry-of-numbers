import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Countable
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import GeometryOfNumbers.Legendre.Exceptions
import GeometryOfNumbers.Legendre.AnkenyLemmas
import GeometryOfNumbers.Core.MinkowskiHelpers
import GeometryOfNumbers.Core.MinkowskiEngine
import GeometryOfNumbers.NumberTheory.Utils

-- This file is long and currently has a number of `simpa` calls that the linter considers
-- replaceable by `simp`. That warning is low-signal during active development, so we disable it
-- to keep `lake lint` output actionable.
set_option linter.unnecessarySimpa false

namespace GeometryOfNumbers
open MeasureTheory MeasureTheory.Measure Set Module Matrix
open scoped NNReal ENNReal BigOperators Matrix
open scoped NumberTheorySymbols

/-! We work in `ℝ^3` as `Fin 3 → ℝ`, which matches Mathlib’s `volume` conventions. -/
abbrev E3 := (Fin 3 → ℝ)

/-!
## Ankeny’s ellipsoid (L2-ball presentation)

We keep the *ambient type* as `E3 := Fin 3 → ℝ` (matching `volume` conventions), but we want an L2-ball.
The clean trick is to define the ball as a preimage under `WithLp.toLp 2`, landing in
`EuclideanSpace ℝ (Fin 3)`.

This is the exact setup used in `Experiments/AnkenyL2Ellipsoid.lean`, but here we keep it in the main file
because it is load-bearing for Minkowski.
-/

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
  GeometryOfNumbers.Minkowski.ankenyDiagMap n q ⁻¹' l2Ball (GeometryOfNumbers.Minkowski.ankenyBallRadius n q)

lemma det_ankenyDiagMap (n q : ℝ) :
    LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)
      = Real.sqrt (2 * q) * (1 : ℝ) * Real.sqrt n := by
  simp [GeometryOfNumbers.Minkowski.ankenyDiagMap, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_three]

lemma ankenyBallRadius_pow_three (n q : ℝ) (hnq : 0 ≤ n * q) :
    (GeometryOfNumbers.Minkowski.ankenyBallRadius n q) ^ 3 = 8 * (n * q) * Real.sqrt (n * q) := by
  -- `r = 2 * sqrt(n*q)` and `(2 * a)^3 = 8 * a^3`,
  -- then `a^3 = (a^2) * a = (n*q) * sqrt(n*q)` for `a = sqrt(n*q)`.
  have hsq : (Real.sqrt (n * q)) ^ 2 = n * q := by
    simpa [pow_two] using (Real.sq_sqrt hnq)
  calc
    (GeometryOfNumbers.Minkowski.ankenyBallRadius n q) ^ 3
        = (2 * Real.sqrt (n * q)) ^ 3 := by
            simp [GeometryOfNumbers.Minkowski.ankenyBallRadius]
    _ = 8 * (Real.sqrt (n * q) ^ 3) := by
          -- `(2*a)^3 = 8*a^3`
          ring
    _ = 8 * ((Real.sqrt (n * q) ^ 2) * Real.sqrt (n * q)) := by
          simp [pow_succ, mul_assoc]
    _ = 8 * ((n * q) * Real.sqrt (n * q)) := by
          simp [hsq]
    _ = 8 * (n * q) * Real.sqrt (n * q) := by ring


lemma one_lt_sqrt2_mul_pi_div_three : (1 : ℝ) < Real.sqrt 2 * Real.pi / 3 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hs2 : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  nlinarith

lemma volume_ankenyEllipsoidL2_eq (n q : ℝ) (hn : 0 < n) (hq : 0 < q) :
    volume (ankenyEllipsoidL2 n q) =
      ENNReal.ofReal ((16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3)) := by
  have hdet_pos : 0 < LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) := by
    have hsq2 : 0 < Real.sqrt (2 * q) := Real.sqrt_pos.2 (by nlinarith)
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by nlinarith)
    have h1 : (0 : ℝ) < 1 := by norm_num
    simpa [det_ankenyDiagMap, mul_assoc, mul_left_comm, mul_comm] using mul_pos (mul_pos hsq2 h1) hsn
  have hdet_ne0 : LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) ≠ 0 := ne_of_gt hdet_pos

  have hr_pos : 0 < GeometryOfNumbers.Minkowski.ankenyBallRadius n q := by
    have hs : 0 < Real.sqrt (n * q) := Real.sqrt_pos.2 (by nlinarith)
    have h2 : (0 : ℝ) < 2 := by norm_num
    simpa [GeometryOfNumbers.Minkowski.ankenyBallRadius] using mul_pos h2 hs

  have hpre :
      volume (ankenyEllipsoidL2 n q) =
        ENNReal.ofReal |(LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹| *
          volume (l2Ball (GeometryOfNumbers.Minkowski.ankenyBallRadius n q)) := by
    simpa [ankenyEllipsoidL2] using
      (MeasureTheory.Measure.addHaar_preimage_linearMap
        (μ := (volume : Measure E3))
        (f := GeometryOfNumbers.Minkowski.ankenyDiagMap n q)
        hdet_ne0
        (l2Ball (GeometryOfNumbers.Minkowski.ankenyBallRadius n q)))

  have hdet_abs_inv :
      ENNReal.ofReal |LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)|⁻¹
        = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) := by
    -- `|det| = det` since `det > 0`, hence `|det|⁻¹ = det⁻¹`.
    have habs : |LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)| =
        LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) := abs_of_pos hdet_pos
    simp [habs]

  -- Reduce to a real identity under `ENNReal.ofReal`.
  calc
    volume (ankenyEllipsoidL2 n q)
        = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
            volume (l2Ball (GeometryOfNumbers.Minkowski.ankenyBallRadius n q)) := by
            -- `|(det)⁻¹| = |det|⁻¹` and `|det| = det` by positivity.
            simpa [hpre, abs_inv, hdet_abs_inv]
    _ = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
          ((ENNReal.ofReal (GeometryOfNumbers.Minkowski.ankenyBallRadius n q)) ^ 3 *
            ENNReal.ofReal (Real.pi * 4 / 3)) := by
          simp [volume_l2Ball]
    _ = ENNReal.ofReal (
            ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
              ((GeometryOfNumbers.Minkowski.ankenyBallRadius n q) ^ 3) *
              (Real.pi * 4 / 3)
          ) := by
          have hdet_nn : 0 ≤ (LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹ :=
            le_of_lt (inv_pos.2 hdet_pos)
          have hr_nn : 0 ≤ (GeometryOfNumbers.Minkowski.ankenyBallRadius n q) := le_of_lt hr_pos
          have hpi_nn : 0 ≤ (Real.pi * 4 / 3 : ℝ) := by
            have : 0 < (Real.pi : ℝ) := Real.pi_pos
            nlinarith
          simp [ENNReal.ofReal_mul, hr_nn, hpi_nn, mul_assoc, mul_comm]
    _ = ENNReal.ofReal ((16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3)) := by
          have hdet :
              LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) =
                Real.sqrt (2 * q) * Real.sqrt n := by
            simpa [mul_assoc] using det_ankenyDiagMap n q
          have hr3 :
              (GeometryOfNumbers.Minkowski.ankenyBallRadius n q) ^ 3 =
                8 * (n * q) * Real.sqrt (n * q) := ankenyBallRadius_pow_three n q (by nlinarith : 0 ≤ n * q)
          have hsq_mul : Real.sqrt (n * q) = Real.sqrt n * Real.sqrt q := by
            have hn_nn : 0 ≤ n := le_of_lt hn
            simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.sqrt_mul hn_nn q)
          have hsq2q : Real.sqrt (2 * q) = Real.sqrt 2 * Real.sqrt q := by
            have h2_nn : 0 ≤ (2 : ℝ) := by nlinarith
            simpa [mul_comm, mul_left_comm, mul_assoc] using (Real.sqrt_mul h2_nn q)
          have hsqn_ne0 : Real.sqrt n ≠ 0 := by
            exact ne_of_gt (Real.sqrt_pos.2 (by linarith))
          have hsqrtq_ne0 : Real.sqrt q ≠ 0 := by
            exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith))
          have hsq2q_ne0 : Real.sqrt (2 * q) ≠ 0 := by
            exact ne_of_gt (Real.sqrt_pos.2 (by nlinarith))
          have : ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
              ((GeometryOfNumbers.Minkowski.ankenyBallRadius n q) ^ 3) * (Real.pi * 4 / 3)
                = (16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3) := by
            -- Substitute closed forms and cancel square roots (as in the experiment file).
            simp [hdet, hr3, hsq_mul, mul_assoc, mul_left_comm, mul_comm] at *
            -- `field_simp` clears denominators and may leave a side-condition goal.
            field_simp [hsqn_ne0, hsq2q_ne0]
            ring_nf
            -- Side condition from `field_simp` (guarded denominators / clearing).
            left
            left
            have hs : (Real.sqrt (2 : ℝ)) ^ 2 = (2 : ℝ) := by
              -- `2 ≥ 0`, so `sqrt(2)^2 = 2`.
              simpa [pow_two] using (Real.sq_sqrt (zero_le_two : (0 : ℝ) ≤ (2 : ℝ)))
            -- `32 = 2 * 16 = sqrt(2)^2 * 16`
            nlinarith
          simpa [this]

lemma volume_ankenyEllipsoidL2_gt (n q : ℝ) (hn : 0 < n) (hq : 0 < q) :
    ENNReal.ofReal (16 * (n * q)) < volume (ankenyEllipsoidL2 n q) := by
  have ha : 0 < (16 * (n * q) : ℝ) := by nlinarith
  have hc : (1 : ℝ) < Real.sqrt 2 * Real.pi / 3 := one_lt_sqrt2_mul_pi_div_three
  have hconst : (16 * (n * q) : ℝ) < (16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3) := by
    simpa [mul_assoc] using (mul_lt_mul_of_pos_left hc ha)
  have hpos : 0 < (16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3 : ℝ) := by
    have hcp : 0 < (Real.sqrt 2 * Real.pi / 3 : ℝ) := by
      have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by nlinarith)
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith
    exact mul_pos ha hcp
  have hof :
      ENNReal.ofReal (16 * (n * q) : ℝ) <
        ENNReal.ofReal ((16 * (n * q)) * (Real.sqrt 2 * Real.pi / 3) : ℝ) := by
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 hconst
  simpa [volume_ankenyEllipsoidL2_eq n q hn hq] using hof

lemma volume_ankenyEllipsoidL2_gt_nat (n q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    (16 * n * q : ℝ≥0∞) < volume (ankenyEllipsoidL2 (n : ℝ) (q : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have h :=
    volume_ankenyEllipsoidL2_gt (n := (n : ℝ)) (q := (q : ℝ)) hnR hqR
  -- `ENNReal.ofReal (16*(n*q))` is definitionally the same as the `ℝ≥0∞` nat-cast here.
  -- (The casts and `ofReal` normalizations are handled by `simp`.)
  simpa [mul_assoc, mul_left_comm, mul_comm] using h

/-!
## The “computable covolume” kernel for the Ankeny lattice

In Ankeny’s proof we want a full-rank ℤ-lattice inside `E3` with *explicitly computable covolume*.

Rather than trying to compute the covolume of the congruence-defined lattice `ankeny_lattice` directly,
we build an explicit ℤ-span lattice from a concrete ℝ-basis and compute the fundamental-domain volume via
`ZSpan.volume_fundamentalDomain` (determinant).
-/

/-- A concrete ℝ-basis whose ℤ-span has covolume `2*n*q`.

The associated matrix (with basis vectors as columns) is:

```text
⎡ n    2q   b ⎤
⎢ 0    2q   b ⎥
⎣ 0     0   1 ⎦
```

so `det = 2*n*q`. -/
noncomputable def ankeny_span_matrix (n q : ℕ) (b : ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(n : ℝ), (2 * q : ℝ), (b : ℝ);
    0, (2 * q : ℝ), (b : ℝ);
    0, 0, (1 : ℝ)]

noncomputable def ankeny_span_basis (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Module.Basis (Fin 3) ℝ E3 :=
  let b0 : Module.Basis (Fin 3) ℝ E3 := Pi.basisFun ℝ (Fin 3)
  let A : Matrix (Fin 3) (Fin 3) ℝ := ankeny_span_matrix n q b
  have hdet : A.det ≠ 0 := by
    -- The matrix is upper triangular with diagonal entries `n`, `2q`, `1`.
    -- (The `b`-entries do not affect the determinant.)
    have hA : A.det = (2 * n * q : ℝ) := by
      -- Explicit 3×3 determinant expansion.
      simp [A, ankeny_span_matrix, Matrix.det_fin_three]
      ring_nf
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    -- Show `2 * (n : ℝ) * (q : ℝ) ≠ 0` by contradiction.
    intro hzero
    have hmul : (2 : ℝ) * (n : ℝ) * (q : ℝ) = 0 := by
      -- rewrite the goal `A.det = 0` into `2*n*q = 0`
      -- (and normalize the multiplication order/associativity).
      have : (2 * n * q : ℝ) = 0 := by simpa [hA] using hzero
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have h' : (2 : ℝ) * (n : ℝ) = 0 ∨ (q : ℝ) = 0 := by
      -- reassociate to apply `mul_eq_zero`.
      have : ((2 : ℝ) * (n : ℝ)) * (q : ℝ) = 0 := by simpa [mul_assoc] using hmul
      exact mul_eq_zero.mp this
    cases h' with
    | inl h2n =>
        have : (2 : ℝ) = 0 ∨ (n : ℝ) = 0 := mul_eq_zero.mp h2n
        cases this with
        | inl h2 =>
            have : (2 : ℝ) ≠ 0 := by norm_num
            exact (this h2).elim
        | inr hn' => exact hn0 hn'
    | inr hq' =>
        exact hq0 hq'
  b0.map (Matrix.toLinearEquiv b0 A (isUnit_iff_ne_zero.mpr hdet))

lemma ankeny_span_basis_matrixOf (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Matrix.of (ankeny_span_basis n q b hn hq) = (ankeny_span_matrix n q b)ᵀ := by
  classical
  ext i j
  -- `Matrix.of` sees the basis vectors as rows (index first), hence the transpose here.
  simp [ankeny_span_basis, ankeny_span_matrix, Module.Basis.map_apply, Matrix.toLinearEquiv, Matrix.of_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Pi.basisFun_apply,
    Matrix.transpose_apply]

lemma ankeny_span_basis_apply (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) (i j : Fin 3) :
    ankeny_span_basis n q b hn hq i j = ankeny_span_matrix n q b j i := by
  have hM := ankeny_span_basis_matrixOf n q b hn hq
  have := congrArg (fun M => M i j) hM
  simpa [Matrix.of_apply, Matrix.transpose_apply] using this

/-- The explicit ℤ-span lattice used for the covolume computation. -/
noncomputable def ankeny_span_lattice (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    AddSubgroup E3 :=
  (Submodule.span ℤ (Set.range (ankeny_span_basis n q b hn hq))).toAddSubgroup

/-- A canonical fundamental domain for the span lattice. -/
noncomputable def ankeny_span_fundamentalDomain (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Set E3 :=
  ZSpan.fundamentalDomain (ankeny_span_basis n q b hn hq)

lemma ankeny_span_isAddFundamentalDomain (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    IsAddFundamentalDomain (ankeny_span_lattice n q b hn hq)
      (ankeny_span_fundamentalDomain n q b hn hq) volume := by
  simpa [ankeny_span_lattice, ankeny_span_fundamentalDomain] using
    (ZSpan.isAddFundamentalDomain' (ankeny_span_basis n q b hn hq) volume)

lemma ankeny_span_volume_fundamentalDomain (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    volume (ankeny_span_fundamentalDomain n q b hn hq) = (2 * n * q : ℝ≥0∞) := by
  classical
  let B : Module.Basis (Fin 3) ℝ E3 := ankeny_span_basis n q b hn hq
  let A : Matrix (Fin 3) (Fin 3) ℝ := ankeny_span_matrix n q b
  have hvol :
      volume (ankeny_span_fundamentalDomain n q b hn hq) =
        ENNReal.ofReal |(Matrix.of B).det| := by
    simpa [ankeny_span_fundamentalDomain, B] using (ZSpan.volume_fundamentalDomain B)
  have hB : Matrix.of B = Aᵀ := by
    simpa [A, B] using (ankeny_span_basis_matrixOf n q b hn hq)
  have hdetA : A.det = (2 * n * q : ℝ) := by
    simp [A, ankeny_span_matrix, Matrix.det_fin_three]
    ring_nf
  have hdetB : (Matrix.of B).det = (2 * n * q : ℝ) := by
    calc
      (Matrix.of B).det = (Aᵀ).det := by simp [hB]
      _ = A.det := by simpa using (Matrix.det_transpose A)
      _ = (2 * n * q : ℝ) := hdetA
  have hnonneg : 0 ≤ (2 * n * q : ℝ) := by
    nlinarith
  -- Convert `ENNReal.ofReal |det|` to an `ℝ≥0∞` nat-cast.
  calc
    volume (ankeny_span_fundamentalDomain n q b hn hq)
        = ENNReal.ofReal |(Matrix.of B).det| := hvol
    _ = ENNReal.ofReal (2 * n * q : ℝ) := by simp [hdetB, abs_of_nonneg hnonneg]
    _ = (2 * n * q : ℝ≥0∞) := by simp [ENNReal.ofReal_natCast]

/-!
### Q₁-variant explicit covolume kernel (modulus `q`, covolume `n*q`)

For the `Q₁ = qx² + y² + nz²` route we want the same “explicit span lattice” trick, but with
the `2q` column replaced by `q`. The determinant becomes `n*q`.
-/

/-- Q₁-variant span matrix (replace `2q` by `q`), with `det = n*q`. -/
noncomputable def ankeny_span_matrix_q1 (n q : ℕ) (b : ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(n : ℝ), (q : ℝ), (b : ℝ);
    0, (q : ℝ), (b : ℝ);
    0, 0, (1 : ℝ)]

noncomputable def ankeny_span_basis_q1 (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Module.Basis (Fin 3) ℝ E3 :=
  let b0 : Module.Basis (Fin 3) ℝ E3 := Pi.basisFun ℝ (Fin 3)
  let A : Matrix (Fin 3) (Fin 3) ℝ := ankeny_span_matrix_q1 n q b
  have hdet : A.det ≠ 0 := by
    have hA : A.det = (n * q : ℝ) := by
      simp [A, ankeny_span_matrix_q1, Matrix.det_fin_three]
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    intro hzero
    have : (n * q : ℝ) = 0 := by simpa [hA] using hzero
    have hmul : (n : ℝ) = 0 ∨ (q : ℝ) = 0 := mul_eq_zero.mp this
    cases hmul with
    | inl hn' => exact hn0 hn'
    | inr hq' => exact hq0 hq'
  b0.map (Matrix.toLinearEquiv b0 A (isUnit_iff_ne_zero.mpr hdet))

lemma ankeny_span_basis_q1_matrixOf (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Matrix.of (ankeny_span_basis_q1 n q b hn hq) = (ankeny_span_matrix_q1 n q b)ᵀ := by
  classical
  ext i j
  simp [ankeny_span_basis_q1, ankeny_span_matrix_q1, Module.Basis.map_apply, Matrix.toLinearEquiv, Matrix.of_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Pi.basisFun_apply,
    Matrix.transpose_apply]

lemma ankeny_span_basis_q1_apply (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) (i j : Fin 3) :
    ankeny_span_basis_q1 n q b hn hq i j = ankeny_span_matrix_q1 n q b j i := by
  have hM := ankeny_span_basis_q1_matrixOf n q b hn hq
  have := congrArg (fun M => M i j) hM
  simpa [Matrix.of_apply, Matrix.transpose_apply] using this

noncomputable def ankeny_span_lattice_q1 (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    AddSubgroup E3 :=
  (Submodule.span ℤ (Set.range (ankeny_span_basis_q1 n q b hn hq))).toAddSubgroup

noncomputable def ankeny_span_fundamentalDomain_q1 (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Set E3 :=
  ZSpan.fundamentalDomain (ankeny_span_basis_q1 n q b hn hq)

lemma ankeny_span_isAddFundamentalDomain_q1 (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    IsAddFundamentalDomain (ankeny_span_lattice_q1 n q b hn hq)
      (ankeny_span_fundamentalDomain_q1 n q b hn hq) volume := by
  simpa [ankeny_span_lattice_q1, ankeny_span_fundamentalDomain_q1] using
    (ZSpan.isAddFundamentalDomain' (ankeny_span_basis_q1 n q b hn hq) volume)

lemma ankeny_span_volume_fundamentalDomain_q1 (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    volume (ankeny_span_fundamentalDomain_q1 n q b hn hq) = (n * q : ℝ≥0∞) := by
  classical
  let B : Module.Basis (Fin 3) ℝ E3 := ankeny_span_basis_q1 n q b hn hq
  let A : Matrix (Fin 3) (Fin 3) ℝ := ankeny_span_matrix_q1 n q b
  have hvol :
      volume (ankeny_span_fundamentalDomain_q1 n q b hn hq) =
        ENNReal.ofReal |(Matrix.of B).det| := by
    simpa [ankeny_span_fundamentalDomain_q1, B] using (ZSpan.volume_fundamentalDomain B)
  have hB : Matrix.of B = Aᵀ := by
    simpa [A, B] using (ankeny_span_basis_q1_matrixOf n q b hn hq)
  have hdetA : A.det = (n * q : ℝ) := by
    simp [A, ankeny_span_matrix_q1, Matrix.det_fin_three]
  have hdetB : (Matrix.of B).det = (n * q : ℝ) := by
    calc
      (Matrix.of B).det = (Aᵀ).det := by simp [hB]
      _ = A.det := by simpa using (Matrix.det_transpose A)
      _ = (n * q : ℝ) := hdetA
  have hnonneg : 0 ≤ (n * q : ℝ) := by
    have : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.zero_le q)
    nlinarith
  calc
    volume (ankeny_span_fundamentalDomain_q1 n q b hn hq)
        = ENNReal.ofReal |(Matrix.of B).det| := hvol
    _ = ENNReal.ofReal (n * q : ℝ) := by simp [hdetB, abs_of_nonneg hnonneg]
    _ = (n * q : ℝ≥0∞) := by simp [ENNReal.ofReal_natCast]

/-!
## Q₁ Minkowski setup (smaller radius, same diagonal map)

For the Q₁ route we keep the same diagonal map `diag(√(2q), 1, √n)` but shrink the ball radius to
\[
r = \sqrt{2 n q},
\]
so that membership gives the *stronger* upper bound `2q x^2 + y^2 + n z^2 < 2 n q`.

This is the key trick that lets us pin down a multiple of `n*q` to be *exactly* `n*q`.
-/

private noncomputable def ankenyBallRadius_q1 (n q : ℝ) : ℝ :=
  Real.sqrt (2 * (n * q))

private noncomputable def ankenyEllipsoidL2_q1 (n q : ℝ) : Set E3 :=
  GeometryOfNumbers.Minkowski.ankenyDiagMap n q ⁻¹' l2Ball (ankenyBallRadius_q1 n q)

private lemma one_lt_pi_div_three : (1 : ℝ) < Real.pi / 3 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  -- divide by 3>0
  have h3 : (0 : ℝ) < 3 := by norm_num
  have : (3 : ℝ) / 3 < Real.pi / 3 := (div_lt_div_of_pos_right hpi h3)
  simpa using this

private lemma volume_ankenyEllipsoidL2_q1_eq (n q : ℝ) (hn : 0 < n) (hq : 0 < q) :
    volume (ankenyEllipsoidL2_q1 n q) =
      ENNReal.ofReal (8 * (n * q) * (Real.pi / 3)) := by
  -- Copy the structure of `volume_ankenyEllipsoidL2_eq`, but with radius `sqrt(2*n*q)`.
  have hdet_pos : 0 < LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) := by
    have hsq2 : 0 < Real.sqrt (2 * q) := Real.sqrt_pos.2 (by nlinarith)
    have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by nlinarith)
    have h1 : (0 : ℝ) < 1 := by norm_num
    simpa [det_ankenyDiagMap, mul_assoc, mul_left_comm, mul_comm] using mul_pos (mul_pos hsq2 h1) hsn
  have hdet_ne0 : LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) ≠ 0 := ne_of_gt hdet_pos

  have hr_pos : 0 < ankenyBallRadius_q1 n q := by
    have : 0 < 2 * (n * q) := by nlinarith
    simpa [ankenyBallRadius_q1] using Real.sqrt_pos.2 this

  have hpre :
      volume (ankenyEllipsoidL2_q1 n q) =
        ENNReal.ofReal |(LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹| *
          volume (l2Ball (ankenyBallRadius_q1 n q)) := by
    simpa [ankenyEllipsoidL2_q1] using
      (MeasureTheory.Measure.addHaar_preimage_linearMap
        (μ := (volume : Measure E3))
        (f := GeometryOfNumbers.Minkowski.ankenyDiagMap n q)
        hdet_ne0
        (l2Ball (ankenyBallRadius_q1 n q)))

  have hdet_abs_inv :
      ENNReal.ofReal |LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)|⁻¹
        = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) := by
    have habs : |LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)| =
        LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) := abs_of_pos hdet_pos
    simp [habs]

  have hr_nn : 0 ≤ ankenyBallRadius_q1 n q := le_of_lt hr_pos
  have hdet_nn : 0 ≤ (LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹ :=
    le_of_lt (inv_pos.2 hdet_pos)
  have hpi_nn : 0 ≤ (Real.pi * 4 / 3 : ℝ) := by
    have : 0 < (Real.pi : ℝ) := Real.pi_pos
    nlinarith

  -- Determinant simplification: in this regime, `det = sqrt(2*n*q)` equals the chosen radius.
  have hdet_eq_r :
      LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) = ankenyBallRadius_q1 n q := by
    have hnq_nn : (0 : ℝ) ≤ n * q := by nlinarith [le_of_lt hn, le_of_lt hq]
    have h2_nn : (0 : ℝ) ≤ (2 : ℝ) := by nlinarith
    have hr : ankenyBallRadius_q1 n q = Real.sqrt 2 * Real.sqrt (n * q) := by
      -- `sqrt(2*(n*q)) = sqrt 2 * sqrt(n*q)`
      simpa [ankenyBallRadius_q1, mul_assoc] using (Real.sqrt_mul h2_nn (n * q))
    have hn_nn : (0 : ℝ) ≤ n := le_of_lt hn
    have hq_nn : (0 : ℝ) ≤ q := le_of_lt hq
    have hsq : Real.sqrt (n * q) = Real.sqrt n * Real.sqrt q := by
      simpa [mul_comm] using (Real.sqrt_mul hn_nn q)
    -- `det = sqrt(2q) * sqrt(n) = sqrt 2 * sqrt(q) * sqrt(n)`
    have hdet' : LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q) = Real.sqrt 2 * Real.sqrt q * Real.sqrt n := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using det_ankenyDiagMap n q
    -- rewrite both sides to the same commutative product
    calc
      LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q)
          = Real.sqrt 2 * (Real.sqrt n * Real.sqrt q) := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using hdet'
      _ = Real.sqrt 2 * Real.sqrt (n * q) := by
              simpa [hsq, mul_assoc, mul_left_comm, mul_comm]
      _ = ankenyBallRadius_q1 n q := by simpa [hr, mul_assoc, mul_left_comm, mul_comm]

  -- Radius square: `r^2 = 2*(n*q)`.
  have hr2 : (ankenyBallRadius_q1 n q) ^ 2 = 2 * (n * q) := by
    have hnq_nn : 0 ≤ 2 * (n * q) := by nlinarith [le_of_lt hn, le_of_lt hq]
    -- use `sq_sqrt` directly to avoid rewriting `sqrt(2*(n*q))` into products of square roots
    simpa [ankenyBallRadius_q1] using (Real.sq_sqrt hnq_nn)

  -- Now combine.
  calc
    volume (ankenyEllipsoidL2_q1 n q)
        = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
            volume (l2Ball (ankenyBallRadius_q1 n q)) := by
            simpa [hpre, abs_inv, hdet_abs_inv]
    _ = ENNReal.ofReal ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
          ((ENNReal.ofReal (ankenyBallRadius_q1 n q)) ^ 3 *
            ENNReal.ofReal (Real.pi * 4 / 3)) := by
          simp [volume_l2Ball]
    _ = ENNReal.ofReal (
            ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
              ((ankenyBallRadius_q1 n q) ^ 3) *
              (Real.pi * 4 / 3)
          ) := by
          simp [ENNReal.ofReal_mul, hr_nn, hpi_nn, mul_assoc, mul_comm]
    _ = ENNReal.ofReal (8 * (n * q) * (Real.pi / 3)) := by
          -- core: det^{-1} * r^3 = 2*(n*q)
          have hs_pos : 0 < ankenyBallRadius_q1 n q := hr_pos
          have hs_ne0 : ankenyBallRadius_q1 n q ≠ 0 := ne_of_gt hs_pos
          have hcore :
              (LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹ * ((ankenyBallRadius_q1 n q) ^ 3)
                = 2 * (n * q) := by
            -- Since `det = r`, this is `r⁻¹ * r^3 = r^2`.
            calc
              (LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹ * ((ankenyBallRadius_q1 n q) ^ 3)
                  = (ankenyBallRadius_q1 n q)⁻¹ * ((ankenyBallRadius_q1 n q) ^ 3) := by
                      simp [hdet_eq_r]
              _ = (ankenyBallRadius_q1 n q) ^ 2 := by
                      -- `r⁻¹ * r^3 = (r⁻¹*r) * r^2 = r^2`
                      calc
                        (ankenyBallRadius_q1 n q)⁻¹ * ((ankenyBallRadius_q1 n q) ^ 3)
                            = (ankenyBallRadius_q1 n q)⁻¹ * ((ankenyBallRadius_q1 n q) ^ 2 * ankenyBallRadius_q1 n q) := by
                                  simp [pow_succ, mul_assoc]
                        _ = ((ankenyBallRadius_q1 n q)⁻¹ * ankenyBallRadius_q1 n q) * ((ankenyBallRadius_q1 n q) ^ 2) := by
                                  simp [mul_assoc, mul_left_comm, mul_comm]
                        _ = (ankenyBallRadius_q1 n q) ^ 2 := by
                                  simp [hs_ne0]
              _ = 2 * (n * q) := by simpa [hr2]
          -- multiply by `pi*4/3`
          have : ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
              ((ankenyBallRadius_q1 n q) ^ 3) * (Real.pi * 4 / 3)
              = 8 * (n * q) * (Real.pi / 3) := by
            calc
              ((LinearMap.det (GeometryOfNumbers.Minkowski.ankenyDiagMap n q))⁻¹) *
                  ((ankenyBallRadius_q1 n q) ^ 3) * (Real.pi * 4 / 3)
                  = (2 * (n * q)) * (Real.pi * 4 / 3) := by simpa [hcore]
              _ = 8 * (n * q) * (Real.pi / 3) := by ring
          simpa [mul_assoc, mul_left_comm, mul_comm] using congrArg ENNReal.ofReal this

private lemma volume_ankenyEllipsoidL2_q1_gt_nat (n q : ℕ) (hn : 0 < n) (hq : 0 < q) :
    (8 * n * q : ℝ≥0∞) < volume (ankenyEllipsoidL2_q1 (n : ℝ) (q : ℝ)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hvol := volume_ankenyEllipsoidL2_q1_eq (n := (n : ℝ)) (q := (q : ℝ)) hnR hqR
  have hpi : (1 : ℝ) < Real.pi / 3 := one_lt_pi_div_three
  have ha : 0 < (8 * ((n : ℝ) * (q : ℝ)) : ℝ) := by nlinarith
  have hmul : (8 * ((n : ℝ) * (q : ℝ)) : ℝ) < (8 * ((n : ℝ) * (q : ℝ))) * (Real.pi / 3) := by
    simpa [mul_assoc] using (mul_lt_mul_of_pos_left hpi ha)
  have hpos : 0 < (8 * ((n : ℝ) * (q : ℝ))) * (Real.pi / 3 : ℝ) := by
    have : 0 < (Real.pi / 3 : ℝ) := lt_trans (by norm_num) hpi
    exact mul_pos ha this
  have hof :
      ENNReal.ofReal (8 * ((n : ℝ) * (q : ℝ)) : ℝ) <
        ENNReal.ofReal ((8 * ((n : ℝ) * (q : ℝ))) * (Real.pi / 3 : ℝ)) := by
    exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 hmul
  -- rewrite LHS as nat-cast `8*n*q` and RHS as `volume ...`
  have : (8 * n * q : ℝ≥0∞) < volume (ankenyEllipsoidL2_q1 (n : ℝ) (q : ℝ)) := by
    -- `simp` bridges nat casts and `ofReal`.
    simpa [hvol, mul_assoc, mul_left_comm, mul_comm] using hof
  simpa using this

/-- Generalized “Dirichlet prime in a CRT class” lemma used by Ankeny:

Given `Odd n` and a coefficient `r` that is a unit in `ZMod n`, there exists a prime `q`
such that `q % 4 = 1` and
\[
  q \equiv -(r)^{-1} \pmod n.
\]

This is the right abstraction boundary: the Jacobi-symbol computation only needs the
congruence `r*q ≡ -1 (mod n)`, which follows from `q = -(r)⁻¹` in `ZMod n`. -/
lemma exists_prime_one_mod_four_and_eq_neg_inv
    (n r : ℕ) (hn : Odd n) (hr : IsUnit (r : ZMod n)) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ (q : ZMod n) = - (r : ZMod n)⁻¹ := by
  classical
  have hn0 : n ≠ 0 := by
    intro h0; subst h0
    simpa using hn

  -- Combine the two congruence conditions into a single residue class modulo `4*n`.
  have hcop2 : Nat.Coprime 2 n := Nat.coprime_two_left.2 hn
  have hcop4 : Nat.Coprime 4 n := by
    have : Nat.Coprime (2 ^ 2) n :=
      (Nat.coprime_pow_left_iff (n := 2) (by decide : 0 < 2) 2 n).2 hcop2
    simpa using this

  let a0 : ZMod n := - (r : ZMod n)⁻¹
  let e : ZMod (4 * n) ≃+* ZMod 4 × ZMod n := ZMod.chineseRemainder hcop4
  let a : ZMod (4 * n) := e.symm (1, a0)

  have ha0 : IsUnit a0 := by
    -- `r` unit ⇒ `r⁻¹` unit ⇒ `-(r⁻¹)` unit
    rcases hr with ⟨u, hu⟩
    have hinv : IsUnit ((r : ZMod n)⁻¹) := by
      refine ⟨u⁻¹, ?_⟩
      -- `↑(u⁻¹) = (↑u)⁻¹`
      have : ((↑(u⁻¹) : ZMod n)) = ((u : (ZMod n)ˣ) : ZMod n)⁻¹ := by simp
      simpa [hu] using this
    simpa [a0] using hinv.neg

  have ha_pair : IsUnit ((1 : ZMod 4), a0) := by
    rcases ha0 with ⟨u0, hu0⟩
    refine ⟨
      { val := ((1 : ZMod 4), (u0 : ZMod n))
        inv := ((1 : ZMod 4), (↑(u0⁻¹) : ZMod n))
        val_inv := by ext <;> simp
        inv_val := by ext <;> simp }, ?_⟩
    simpa [hu0]

  have ha : IsUnit a := by
    simpa [a] using (e.symm.toRingHom.isUnit_map ha_pair)

  -- Apply Dirichlet: infinitely many primes in the residue class `a (mod 4*n)`.
  have hQ0 : (4 * n) ≠ 0 := Nat.mul_ne_zero (by decide) hn0
  haveI : NeZero (4 * n) := ⟨hQ0⟩
  obtain ⟨q, _hq_gt, hq_prime, hq_eq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * n) (a := a) ha 0

  -- Project back to `ZMod 4` and `ZMod n` to read off the two conditions.
  have hpair : e (q : ZMod (4 * n)) = ((1 : ZMod 4), a0) := by
    have := congrArg e hq_eq
    simpa [a] using this

  have hq_mod4 : (q : ZMod 4) = 1 := by
    have := congrArg Prod.fst hpair
    simpa [e] using this
  have hq_modn : (q : ZMod n) = a0 := by
    have := congrArg Prod.snd hpair
    simpa [e] using this

  have hq_mod4_nat : q % 4 = 1 := by
    have : (q : ZMod 4).val = (1 : ZMod 4).val := congrArg ZMod.val hq_mod4
    simpa [ZMod.val_natCast] using this

  refine ⟨q, hq_prime, hq_mod4_nat, ?_⟩
  simpa [a0] using hq_modn

/-- Existence of the Ankeny prime `q`. -/
lemma exists_ankeny_prime (n : ℕ) (hn : n % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ (q : ZMod n) = - (2 : ZMod n)⁻¹ := by
  classical
  have hn_odd : Odd n := GeometryOfNumbers.NumberTheory.odd_of_mod8_eq3 hn
  have h2 : IsUnit (2 : ZMod n) := GeometryOfNumbers.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
  simpa using exists_prime_one_mod_four_and_eq_neg_inv n 2 hn_odd h2

lemma exists_ankeny_prime_one_mod_eight (n : ℕ) (hn : n % 8 = 1) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ (q : ZMod n) = - (2 : ZMod n)⁻¹ := by
  classical
  have hn_odd : Odd n := by
    have : n % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have h2 : IsUnit (2 : ZMod n) := GeometryOfNumbers.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
  simpa using exists_prime_one_mod_four_and_eq_neg_inv n 2 hn_odd h2

/-- Variant of the Dirichlet/CRT prime choice for the *even* reduced residue classes.

For `n % 8 ∈ {2,6}`, write `n = 2*s` with `s` odd. We want an odd prime `q` such that
- `q ≡ -1 (mod s)` (so also `q ≡ -1 (mod n)`), and
- `q % 8` is a specific value (`1` or `5`) so that the Jacobi-symbol computation forces
  `J(-n | q) = 1`, hence `-n` is a square modulo `q`.

This lemma packages only the prime existence step: it does *not* compute Jacobi symbols. -/
lemma exists_prime_mod_eight_and_eq_neg_one
    (s : ℕ) (hs : Odd s) (a8 : ℕ) (ha8 : a8 = 1 ∨ a8 = 5) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 8 = a8 ∧ (q : ZMod s) = (-1 : ZMod s) := by
  classical
  have hs0 : s ≠ 0 := by
    intro h0; subst h0
    simpa using hs

  -- CRT between `ZMod 8` and `ZMod s` (since `s` is odd).
  have hcop2 : Nat.Coprime 2 s := Nat.coprime_two_left.2 hs
  have hcop8 : Nat.Coprime 8 s := by
    -- `8 = 2^3`
    simpa [pow_succ] using (hcop2.pow_left 3)
  let e : ZMod (8 * s) ≃+* ZMod 8 × ZMod s := ZMod.chineseRemainder hcop8

  let a : ZMod (8 * s) := e.symm (a8, (-1 : ZMod s))

  have ha_unit8 : IsUnit (a8 : ZMod 8) := by
    rcases ha8 with rfl | rfl
    · simpa using (isUnit_one : IsUnit (1 : ZMod 8))
    · -- `5` is a unit modulo `8`.
      -- (This is a finite-ring fact; `decide` can discharge it.)
      have : IsUnit (5 : ZMod 8) := by decide
      simpa using this

  have ha_pair : IsUnit ((a8 : ZMod 8), (-1 : ZMod s)) := by
    -- `IsUnit` in a product ring is componentwise.
    have hneg1 : IsUnit (-1 : ZMod s) := by simpa using (isUnit_neg (1 : ZMod s))
    exact (Prod.isUnit_iff).2 ⟨ha_unit8, hneg1⟩

  have ha_unit : IsUnit a := by
    simpa [a] using (e.symm.toRingHom.isUnit_map ha_pair)

  -- Apply Dirichlet: there exist primes in the residue class `a (mod 8*s)`.
  have hQ0 : (8 * s) ≠ 0 := Nat.mul_ne_zero (by decide) hs0
  haveI : NeZero (8 * s) := ⟨hQ0⟩
  obtain ⟨q, _hq_gt, hq_prime, hq_eq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 8 * s) (a := a) ha_unit 0

  -- Project back to `ZMod 8` and `ZMod s`.
  have hpair : e (q : ZMod (8 * s)) = ((a8 : ZMod 8), (-1 : ZMod s)) := by
    have := congrArg e hq_eq
    simpa [a] using this

  have hq_mod8 : (q : ZMod 8) = a8 := by
    have := congrArg Prod.fst hpair
    simpa [e] using this
  have hq_mods : (q : ZMod s) = (-1 : ZMod s) := by
    have := congrArg Prod.snd hpair
    simpa [e] using this

  have hq_mod8_nat : q % 8 = a8 := by
    have : (q : ZMod 8).val = (a8 : ZMod 8).val := congrArg ZMod.val hq_mod8
    -- `a8` is already < 8 (since we restrict to 1 or 5).
    rcases ha8 with rfl | rfl
    · simpa [ZMod.val_natCast] using this
    · simpa [ZMod.val_natCast] using this

  exact ⟨q, hq_prime, hq_mod8_nat, hq_mods⟩

/-!
### Even squarefree residues (`2` and `6` mod `8`)

For the Q₁ route (`q*x^2 + y^2 + n*z^2 = n*q`) we need:
- an odd prime `q` with `q ≡ -1 (mod n)`, and
- a square root `b` of `-n` modulo `q` (i.e. `b^2 ≡ -n [ZMOD q]`).

When `n` is squarefree and even, we write `n = 2*s` with `s` odd. The prime choice lemma
`exists_prime_mod_eight_and_eq_neg_one` gives `q ≡ -1 (mod s)` and a controlled residue `q % 8`.

The Jacobi-symbol computation is then a short invariant:
\[
J(n \mid q) = J(2 \mid q)\,J(s \mid q),
\]
and `J(s|q)` is controlled via reciprocity from `q ≡ -1 (mod s)` (so `J(q|s)=J(-1|s)`).

Choosing `q % 8 = 1` (resp. `5`) makes `J(2|q)` equal `1` (resp. `-1`), which cancels the
`J(-1|s)` value when `s % 4 = 1` (resp. `3`). This forces `J(-n|q)=1`, hence `-n` is a square mod `q`.
-/

private lemma exists_b_sq_congr_neg_mod_q_of_jacobi
    (n q : ℕ) (hq : Nat.Prime q) (hJ : J(-(n : ℤ) | q) = 1) :
    ∃ b : ℤ, b ^ 2 ≡ - (n : ℤ) [ZMOD (q : ℤ)] := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hsq_q : IsSquare (-(n : ZMod q)) := by
    simpa [Int.cast_neg, Int.cast_natCast] using
      (ZMod.isSquare_of_jacobiSym_eq_one (p := q) (a := (-(n : ℤ))) hJ)
  rcases hsq_q with ⟨r, hr⟩
  rcases ZMod.intCast_surjective r with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  have hr' : ((b : ZMod q) ^ 2) = (-(n : ℤ) : ZMod q) := by
    -- `IsSquare` for `ZMod q` yields `-(n) = r*r`; rewrite into a `^2` statement.
    have : (r ^ 2) = (-(n : ZMod q)) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hr.symm
    simpa [hb, Int.cast_neg, Int.cast_natCast] using this
  exact (ZMod.intCast_eq_intCast_iff (b ^ 2) (-(n : ℤ)) q).1 (by
    simpa [Int.cast_pow, pow_two] using hr')

private lemma zmod_neg_one_of_mod_two_and_mod_s
    (s q : ℕ) (hs : Odd s) (hqodd : Odd q) (hq_mods : (q : ZMod s) = (-1 : ZMod s)) :
    (q : ZMod (2 * s)) = (-1 : ZMod (2 * s)) := by
  classical
  have hcop : Nat.Coprime 2 s := Nat.coprime_two_left.2 hs
  let e : ZMod (2 * s) ≃+* ZMod 2 × ZMod s := ZMod.chineseRemainder hcop
  apply e.injective
  ext
  · -- mod 2 component: `Odd q` ⇒ `q = 1` in `ZMod 2`, and `-1 = 1` in `ZMod 2`.
    have hqZ2 : (q : ZMod 2) = (1 : ZMod 2) := by
      have : q % 2 = 1 := by
        exact Nat.odd_iff.1 hqodd
      -- `q ≡ 1 [MOD 2]` gives equality in `ZMod 2`.
      have : q ≡ 1 [MOD 2] := by
        dsimp [Nat.ModEq]
        simpa [this]
      exact (ZMod.natCast_eq_natCast_iff q 1 2).2 this
    -- `e`'s `fst` projection is definitionally the reduction mod 2.
    simpa [hqZ2]
  · -- mod `s` component: given.
    simpa [hq_mods]

lemma exists_even_q1_data_two_mod_eight
    (n : ℕ) (hn2 : n % 8 = 2) (_hn_sq : Squarefree n) :
    ∃ q : ℕ, ∃ b : ℤ,
      Nat.Prime q ∧ q % 4 = 1 ∧ Nat.Coprime n q ∧
      (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)] ∧
      b ^ 2 ≡ - (n : ℤ) [ZMOD (q : ℤ)] := by
  classical
  -- write `n = 2*s` with `s` odd (forced by `n % 8 = 2`)
  have hn_even : n % 2 = 0 := by omega
  have hs_odd : Odd (n / 2) := by
    have : (n / 2) % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have hs4 : (n / 2) % 4 = 1 := by omega

  obtain ⟨q, hq_prime, hq8, hq_mods⟩ :=
    exists_prime_mod_eight_and_eq_neg_one (s := (n / 2)) hs_odd 1 (Or.inl rfl)
  have hq1 : q % 4 = 1 := by omega
  have hq_odd : Odd q := by
    have : q % 2 = 1 := by omega
    exact Nat.odd_iff.2 this

  -- lift `q ≡ -1 (mod n/2)` to `q ≡ -1 (mod n)`.
  have hq_modZMod : (q : ZMod n) = (-1 : ZMod n) := by
    -- Avoid rewriting the modulus by equality (which is brittle for `ZMod`).
    -- Instead show `n ∣ q+1`, which is equivalent to `q = -1` in `ZMod n`.
    have hn_eq : n = 2 * (n / 2) :=
      (Nat.two_mul_div_two_of_even (Nat.even_iff.2 hn_even)).symm
    have hs_dvd : (n / 2) ∣ q + 1 := by
      have : (q : ZMod (n / 2)) + 1 = 0 := by
        rw [hq_mods]
        simp
      have : ((q + 1 : ℕ) : ZMod (n / 2)) = 0 := by
        simpa [Nat.cast_add, Nat.cast_one] using this
      exact (ZMod.natCast_eq_zero_iff (q + 1) (n / 2)).1 this
    have h2_dvd : 2 ∣ q + 1 := by
      have : (q + 1) % 2 = 0 := by omega
      exact Nat.dvd_iff_mod_eq_zero.mpr this
    have hcop : Nat.Coprime 2 (n / 2) := Nat.coprime_two_left.2 hs_odd
    have hn_dvd : n ∣ q + 1 := by
      -- `2*(n/2) ∣ q+1` and `n = 2*(n/2)`.
      have hmul : 2 * (n / 2) ∣ q + 1 := hcop.mul_dvd_of_dvd_of_dvd h2_dvd hs_dvd
      exact hn_eq.symm ▸ hmul
    -- turn `n ∣ q+1` into equality in `ZMod n`
    have : ((q + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff (q + 1) n).2 hn_dvd
    -- `q + 1 = 0` ⇒ `q = -1`
    have : (q : ZMod n) = (-1 : ZMod n) := by
      -- From `(q+1)=0`, add `(-1)` to both sides.
      have h1 : (q : ZMod n) + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_one] using this
      have := congrArg (fun t : ZMod n => t + (-1)) h1
      -- `(q+1)+(-1) = q` and `0+(-1) = -1`
      simpa [add_assoc] using this
    simpa using this

  have hqunit : IsUnit (q : ZMod n) := by
    -- `q = -1` in `ZMod n`, and `-1` is a unit.
    simpa [hq_modZMod] using (isUnit_neg (1 : ZMod n))
  have hnq : Nat.Coprime n q :=
    (ZMod.isUnit_iff_coprime q n).1 (by simpa using hqunit) |> Nat.coprime_comm.1

  have hq_mod : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)] := by
    -- convert the `ZMod` equality into an `Int.ModEq`.
    have : ((q : ℤ) : ZMod n) = ((-1 : ℤ) : ZMod n) := by
      -- `(-1 : ZMod n)` is definitional `(((-1:ℤ)) : ZMod n)`.
      simpa using hq_modZMod
    exact (ZMod.intCast_eq_intCast_iff (q : ℤ) (-1 : ℤ) n).1 this

  -- Jacobi bookkeeping to show `J(-n|q)=1`.
  have hJ2 : J(2 | q) = (1 : ℤ) := by
    calc
      J(2 | q) = ZMod.χ₈ q := jacobiSym.at_two hq_odd
      _ = (1 : ℤ) := by
        have hred : ZMod.χ₈ q = ZMod.χ₈ (q % 8 : ℕ) := by
          simpa using (ZMod.χ₈_nat_mod_eight q)
        have hval : ZMod.χ₈ (1 : ℕ) = (1 : ℤ) := by decide
        simpa [hred, hq8] using hval

  have hJq_s : J((q : ℤ) | (n / 2)) = (1 : ℤ) := by
    have hs_odd' : Odd (n / 2) := hs_odd
    have hq_mod_sZ : (q : ℤ) ≡ (-1 : ℤ) [ZMOD ((n / 2 : ℕ) : ℤ)] := by
      have : ((q : ℤ) : ZMod (n / 2)) = ((-1 : ℤ) : ZMod (n / 2)) := by
        simpa using hq_mods
      exact (ZMod.intCast_eq_intCast_iff (q : ℤ) (-1 : ℤ) (n / 2)).1 this
    have : J((q : ℤ) | (n / 2)) = J(-1 | (n / 2)) := by
      refine jacobiSym.mod_left' (a₁ := (q : ℤ)) (a₂ := (-1 : ℤ)) (b := (n / 2)) ?_
      simpa using hq_mod_sZ.eq
    have hJ_neg_one : J(-1 | (n / 2)) = (1 : ℤ) := by
      calc
        J(-1 | (n / 2)) = ZMod.χ₄ (n / 2 : ℕ) := jacobiSym.at_neg_one hs_odd'
        _ = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hs4
    simpa [hJ_neg_one] using this

  have hJs_q : J(((n / 2 : ℕ) : ℤ) | q) = (1 : ℤ) := by
    have hs_odd' : Odd (n / 2) := hs_odd
    have := jacobiSym.quadratic_reciprocity_one_mod_four (a := q) (b := (n / 2)) hq1 hs_odd'
    simpa using (this ▸ hJq_s)

  have hJ_nq : J((n : ℤ) | q) = (1 : ℤ) := by
    have hn2Z : (n : ℤ) = (2 : ℤ) * ((n / 2 : ℕ) : ℤ) := by
      have hn2n : n = 2 * (n / 2) := (Nat.two_mul_div_two_of_even (Nat.even_iff.2 hn_even)).symm
      exact_mod_cast hn2n
    have hmul :
        J((2 : ℤ) * ((n / 2 : ℕ) : ℤ) | q) = J(2 | q) * J(((n / 2 : ℕ) : ℤ) | q) :=
      jacobiSym.mul_left (2 : ℤ) ((n / 2 : ℕ) : ℤ) q
    calc
      J((n : ℤ) | q) = J((2 : ℤ) * ((n / 2 : ℕ) : ℤ) | q) := by
        rw [hn2Z]
      _ = J(2 | q) * J(((n / 2 : ℕ) : ℤ) | q) := by simpa using hmul
      _ = 1 := by
        -- Avoid `simp` rewriting `↑(n/2)` into `↑n/2` (Int division).
        rw [hJ2, hJs_q]
        simp

  have hJ_negn : J(-(n : ℤ) | q) = 1 := by
    have hχ4 : ZMod.χ₄ q = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hq1
    calc
      J(-(n : ℤ) | q) = ZMod.χ₄ q * J((n : ℤ) | q) := jacobiSym.neg (a := (n : ℤ)) (hb := hq_odd)
      _ = 1 := by simp [hχ4, hJ_nq]

  obtain ⟨b, hb⟩ := exists_b_sq_congr_neg_mod_q_of_jacobi n q hq_prime hJ_negn
  exact ⟨q, b, hq_prime, hq1, hnq, hq_mod, hb⟩

lemma exists_even_q1_data_six_mod_eight
    (n : ℕ) (hn6 : n % 8 = 6) (_hn_sq : Squarefree n) :
    ∃ q : ℕ, ∃ b : ℤ,
      Nat.Prime q ∧ q % 4 = 1 ∧ Nat.Coprime n q ∧
      (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)] ∧
      b ^ 2 ≡ - (n : ℤ) [ZMOD (q : ℤ)] := by
  classical
  have hn_even : n % 2 = 0 := by omega
  have hs_odd : Odd (n / 2) := by
    have : (n / 2) % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have hs4 : (n / 2) % 4 = 3 := by omega

  obtain ⟨q, hq_prime, hq8, hq_mods⟩ :=
    exists_prime_mod_eight_and_eq_neg_one (s := (n / 2)) hs_odd 5 (Or.inr rfl)
  have hq1 : q % 4 = 1 := by omega
  have hq_odd : Odd q := by
    have : q % 2 = 1 := by omega
    exact Nat.odd_iff.2 this

  have hq_modZMod : (q : ZMod n) = (-1 : ZMod n) := by
    have hn_eq : n = 2 * (n / 2) :=
      (Nat.two_mul_div_two_of_even (Nat.even_iff.2 hn_even)).symm
    have hs_dvd : (n / 2) ∣ q + 1 := by
      have : (q : ZMod (n / 2)) + 1 = 0 := by
        rw [hq_mods]
        simp
      have : ((q + 1 : ℕ) : ZMod (n / 2)) = 0 := by
        simpa [Nat.cast_add, Nat.cast_one] using this
      exact (ZMod.natCast_eq_zero_iff (q + 1) (n / 2)).1 this
    have h2_dvd : 2 ∣ q + 1 := by
      have : (q + 1) % 2 = 0 := by omega
      exact Nat.dvd_iff_mod_eq_zero.mpr this
    have hcop : Nat.Coprime 2 (n / 2) := Nat.coprime_two_left.2 hs_odd
    have hn_dvd : n ∣ q + 1 := by
      have hmul : 2 * (n / 2) ∣ q + 1 := hcop.mul_dvd_of_dvd_of_dvd h2_dvd hs_dvd
      exact hn_eq.symm ▸ hmul
    have : ((q + 1 : ℕ) : ZMod n) = 0 := (ZMod.natCast_eq_zero_iff (q + 1) n).2 hn_dvd
    have : (q : ZMod n) = (-1 : ZMod n) := by
      have h1 : (q : ZMod n) + 1 = 0 := by
        simpa [Nat.cast_add, Nat.cast_one] using this
      have := congrArg (fun t : ZMod n => t + (-1)) h1
      simpa [add_assoc] using this
    simpa using this

  have hqunit : IsUnit (q : ZMod n) := by
    simpa [hq_modZMod] using (isUnit_neg (1 : ZMod n))
  have hnq : Nat.Coprime n q :=
    (ZMod.isUnit_iff_coprime q n).1 (by simpa using hqunit) |> Nat.coprime_comm.1

  have hq_mod : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)] := by
    have : ((q : ℤ) : ZMod n) = ((-1 : ℤ) : ZMod n) := by simpa using hq_modZMod
    exact (ZMod.intCast_eq_intCast_iff (q : ℤ) (-1 : ℤ) n).1 this

  have hJ2 : J(2 | q) = (-1 : ℤ) := by
    calc
      J(2 | q) = ZMod.χ₈ q := jacobiSym.at_two hq_odd
      _ = (-1 : ℤ) := by
        have hred : ZMod.χ₈ q = ZMod.χ₈ (q % 8 : ℕ) := by
          simpa using (ZMod.χ₈_nat_mod_eight q)
        have hval : ZMod.χ₈ (5 : ℕ) = (-1 : ℤ) := by decide
        simpa [hred, hq8] using hval

  have hJq_s : J((q : ℤ) | (n / 2)) = (-1 : ℤ) := by
    have hq_mod_sZ : (q : ℤ) ≡ (-1 : ℤ) [ZMOD ((n / 2 : ℕ) : ℤ)] := by
      have : ((q : ℤ) : ZMod (n / 2)) = ((-1 : ℤ) : ZMod (n / 2)) := by
        simpa using hq_mods
      exact (ZMod.intCast_eq_intCast_iff (q : ℤ) (-1 : ℤ) (n / 2)).1 this
    have : J((q : ℤ) | (n / 2)) = J(-1 | (n / 2)) := by
      refine jacobiSym.mod_left' (a₁ := (q : ℤ)) (a₂ := (-1 : ℤ)) (b := (n / 2)) ?_
      simpa using hq_mod_sZ.eq
    have hJ_neg_one : J(-1 | (n / 2)) = (-1 : ℤ) := by
      calc
        J(-1 | (n / 2)) = ZMod.χ₄ (n / 2 : ℕ) := jacobiSym.at_neg_one hs_odd
        _ = (-1 : ℤ) := ZMod.χ₄_nat_three_mod_four hs4
    simpa [hJ_neg_one] using this

  have hJs_q : J(((n / 2 : ℕ) : ℤ) | q) = (-1 : ℤ) := by
    have := jacobiSym.quadratic_reciprocity_one_mod_four (a := q) (b := (n / 2)) hq1 hs_odd
    simpa using (this ▸ hJq_s)

  have hJ_nq : J((n : ℤ) | q) = (1 : ℤ) := by
    have hn2Z : (n : ℤ) = (2 : ℤ) * ((n / 2 : ℕ) : ℤ) := by
      have hn2n : n = 2 * (n / 2) := (Nat.two_mul_div_two_of_even (Nat.even_iff.2 hn_even)).symm
      exact_mod_cast hn2n
    have hmul :
        J((2 : ℤ) * ((n / 2 : ℕ) : ℤ) | q) = J(2 | q) * J(((n / 2 : ℕ) : ℤ) | q) :=
      jacobiSym.mul_left (2 : ℤ) ((n / 2 : ℕ) : ℤ) q
    -- `(-1) * (-1) = 1`
    calc
      J((n : ℤ) | q) = J((2 : ℤ) * ((n / 2 : ℕ) : ℤ) | q) := by
        rw [hn2Z]
      _ = J(2 | q) * J(((n / 2 : ℕ) : ℤ) | q) := by simpa using hmul
      _ = 1 := by
        rw [hJ2, hJs_q]
        simp

  have hJ_negn : J(-(n : ℤ) | q) = 1 := by
    have hχ4 : ZMod.χ₄ q = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hq1
    calc
      J(-(n : ℤ) | q) = ZMod.χ₄ q * J((n : ℤ) | q) := jacobiSym.neg (a := (n : ℤ)) (hb := hq_odd)
      _ = 1 := by simp [hχ4, hJ_nq]

  obtain ⟨b, hb⟩ := exists_b_sq_congr_neg_mod_q_of_jacobi n q hq_prime hJ_negn
  exact ⟨q, b, hq_prime, hq1, hnq, hq_mod, hb⟩

/-- “Back half” of `exists_ankeny_b`: once you know `J(q | n) = 1`, build the congruence
`b^2 ≡ -n [ZMOD 2q]`.

This lemma is intentionally parameterized by *only* the Jacobi-symbol fact `J(q|n)=1` plus
the standard side conditions (`n` odd, `q` prime, `q ≡ 1 (mod 4)`).

Why this is useful for end-to-end progress:
- For the current `n % 8 = 3` branch, we obtain `J(q|n)=1` from the congruence
  `2q ≡ -1 (mod n)` (the existing Ankeny choice).
- For future branches (`n % 8 = 1` and `5`, i.e. `n % 4 = 1`) we can instead arrange
  `q ≡ -1 (mod n)` (an `r=1` choice) and *still* reduce to this lemma.

So this is the “bridge point” between (A) choosing primes via Dirichlet + Jacobi algebra and
(B) producing the modulus `2q` square root needed by the Minkowski/lattice layer. -/
lemma exists_b_sq_congr_neg_of_jacobi_q_eq_one
    (n q : ℕ) (hn : Odd n) (hq : Nat.Prime q) (hq1 : q % 4 = 1)
    (hJ_q : J((q : ℤ) | n) = (1 : ℤ)) :
    ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (2 * q)] := by
  classical

  have hq_odd : Odd q := by
    -- `q % 4 = 1` rules out `q = 2`, hence `q` is odd.
    have hq_ne2 : q ≠ 2 := by
      intro hq2; subst hq2
      simp at hq1
    exact hq.odd_of_ne_two hq_ne2

  have hcop2q : Nat.Coprime 2 q := Nat.coprime_two_left.2 hq_odd

  -- Step 1: Reciprocity transfers `J(q|n)=1` to `J(n|q)=1` since `q % 4 = 1`.
  have hJ_nq : J((n : ℤ) | q) = (1 : ℤ) := by
    have := jacobiSym.quadratic_reciprocity_one_mod_four (a := q) (b := n) hq1 hn
    -- `this : J(q|n) = J(n|q)`
    simpa using (this ▸ hJ_q)

  -- Step 2: Turn `J(-n | q) = 1` into an actual square root in `ZMod q`.
  haveI : Fact q.Prime := ⟨hq⟩
  have hJ_negn : J(-(n : ℤ) | q) = 1 := by
    -- `J(-n|q) = χ₄ q * J(n|q)`; for `q % 4 = 1`, `χ₄ q = 1`.
    have hχ4 : ZMod.χ₄ q = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hq1
    calc
      J(-(n : ℤ) | q) = ZMod.χ₄ q * J((n : ℤ) | q) := jacobiSym.neg (a := (n : ℤ)) (hb := hq_odd)
      _ = 1 := by simp [hχ4, hJ_nq]

  have hsq_q : IsSquare (-(n : ZMod q)) := by
    -- `ZMod.isSquare_of_jacobiSym_eq_one` returns `IsSquare ((-(n:ℤ)) : ZMod q)`;
    -- rewrite the integer cast using `Int.cast_neg` / `Int.cast_natCast`.
    simpa [Int.cast_neg, Int.cast_natCast] using
      (ZMod.isSquare_of_jacobiSym_eq_one (p := q) (a := (-(n : ℤ))) hJ_negn)
  rcases hsq_q with ⟨r, hr⟩

  -- Step 3: Lift the square root mod `q` to a square root mod `2*q` via CRT.
  have hnZ2 : (n : ZMod 2) = (1 : ZMod 2) := by
    have : n % 2 = 1 := by
      -- `Odd n` forces `n % 2 = 1`.
      exact (Nat.odd_iff.1 hn)
    have : n ≡ 1 [MOD 2] := by
      dsimp [Nat.ModEq]
      simpa [this]
    exact (ZMod.natCast_eq_natCast_iff n 1 2).2 this

  have hmod2 : ((1 : ZMod 2) ^ 2) = (-(n : ZMod 2)) := by
    -- In `ZMod 2`, `n = 1` and `-1 = 1`.
    simp [hnZ2]

  let e : ZMod (2 * q) ≃+* ZMod 2 × ZMod q := ZMod.chineseRemainder hcop2q
  let bZ : ZMod (2 * q) := e.symm ((1 : ZMod 2), r)

  have hbZ : bZ ^ 2 = (-(n : ℤ) : ZMod (2 * q)) := by
    apply e.injective
    ext
    · -- mod 2 component
      have : ((1 : ZMod 2) ^ 2) = (-(n : ZMod 2)) := hmod2
      simpa [bZ] using this
    · -- mod q component
      -- `hr : -(n : ZMod q) = r*r`.
      have : (r ^ 2) = (-(n : ZMod q)) := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hr.symm
      -- cast `-(n : ZMod q)` as `((-(n : ℤ)) : ZMod q)` to match `e`'s component.
      simpa [bZ, Int.cast_neg, Int.cast_natCast] using this

  -- Convert the equality in `ZMod (2*q)` into an `Int.ModEq` witness.
  rcases ZMod.intCast_surjective bZ with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  have hbZ' : ((b : ZMod (2 * q)) ^ 2) = (-(n : ℤ) : ZMod (2 * q)) := by simpa [hb] using hbZ
  exact (ZMod.intCast_eq_intCast_iff (b ^ 2) (-(n : ℤ)) (2 * q)).1 (by
    simpa [Int.cast_pow, pow_two] using hbZ')

/-- A “next unlocked piece” for `n % 4 = 1` (so `n % 8 = 1` or `5`):

Pick a prime `q ≡ 1 (mod 4)` with `q ≡ -1 (mod n)` (i.e. `q = -1` in `ZMod n`).
Then `J(q|n) = J(-1|n) = 1`, so the back-half lemma produces `b^2 ≡ -n [ZMOD 2q]`.

This does *not* finish the `t % 8 = 1,5` cases on its own (the Minkowski layer is still
specialized to `2q` in the quadratic form), but it gives us a clean interface:

- “front half”: pick `q` in a residue class (Dirichlet),
- “Jacobi half”: conclude `J(q|n)=1`,
- “back half”: produce the `b` congruence we need for a lattice construction. -/
lemma exists_b_sq_congr_neg_of_mod_four_eq_one
    (n : ℕ) (hn4 : n % 4 = 1) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (2 * q)] := by
  classical
  have hn_odd : Odd n := by
    -- `n % 4 = 1` implies `n` odd.
    have : n % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  -- We want this with the same elaboration as `(r : ZMod n)` when `r = 1`.
  have h1 : IsUnit ((1 : ℕ) : ZMod n) := by
    simpa using (isUnit_one : IsUnit (1 : ZMod n))
  obtain ⟨q, hqp, hq1, hq_mod⟩ := exists_prime_one_mod_four_and_eq_neg_inv n 1 hn_odd h1
  -- Show `J(q|n) = 1` by reducing to `J(-1|n)`.
  have hq_modEq : ((q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] := by
    -- With `r = 1`, `1*q ≡ -1 (mod n)`.
    have : ((1 : ℤ) * (q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] :=
      GeometryOfNumbers.NumberTheory.mul_int_modEq_neg_one_of_q_eq_neg_inv n 1 q (by simpa using h1) (by simpa using hq_mod)
    simpa using this
  have hJ_q : J((q : ℤ) | n) = (1 : ℤ) := by
    have : J((q : ℤ) | n) = J(-1 | n) := by
      refine jacobiSym.mod_left' (a₁ := (q : ℤ)) (a₂ := (-1 : ℤ)) (b := n) ?_
      simpa using hq_modEq.eq
    have hJ_neg_one : J(-1 | n) = (1 : ℤ) := by
      calc
        J(-1 | n) = ZMod.χ₄ n := jacobiSym.at_neg_one hn_odd
        _ = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hn4
    simpa [hJ_neg_one] using this
  have := exists_b_sq_congr_neg_of_jacobi_q_eq_one n q hn_odd hqp hq1 hJ_q
  exact ⟨q, hqp, hq1, this⟩

/-- A packaging lemma for the `n % 8 = 5` (“`n % 4 = 1`”) branch:

We can pick a prime `q ≡ 1 (mod 4)` with `q ≡ -1 (mod n)`, and produce a square root of `-n` modulo `q`.

This is exactly the congruence interface needed for the `Q₁ = qx² + y² + nz²` variant:
- the `q ≡ -1 (mod n)` part is the `mod n` cancellation under `x ≡ y`,
- the `b² ≡ -n (mod q)` part is the `mod q` cancellation under `y ≡ b z`.
-/
lemma exists_prime_one_mod_four_and_modEq_neg_one_and_b_sq_congr_neg_mod_q
    (n : ℕ) (hn4 : n % 4 = 1) :
    ∃ q : ℕ,
      Nat.Prime q ∧
      q % 4 = 1 ∧
      ((q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] ∧
      ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (q : ℤ)] := by
  classical
  have hn_odd : Odd n := by
    have : n % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have h1 : IsUnit ((1 : ℕ) : ZMod n) := by
    simpa using (isUnit_one : IsUnit (1 : ZMod n))
  obtain ⟨q, hqp, hq1, hq_mod⟩ := exists_prime_one_mod_four_and_eq_neg_inv n 1 hn_odd h1
  have hq_modEq : ((q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] := by
    have : ((1 : ℤ) * (q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] :=
      GeometryOfNumbers.NumberTheory.mul_int_modEq_neg_one_of_q_eq_neg_inv n 1 q (by simpa using h1) (by simpa using hq_mod)
    simpa using this
  have hJ_q : J((q : ℤ) | n) = (1 : ℤ) := by
    have : J((q : ℤ) | n) = J(-1 | n) := by
      refine jacobiSym.mod_left' (a₁ := (q : ℤ)) (a₂ := (-1 : ℤ)) (b := n) ?_
      simpa using hq_modEq.eq
    have hJ_neg_one : J(-1 | n) = (1 : ℤ) := by
      calc
        J(-1 | n) = ZMod.χ₄ n := jacobiSym.at_neg_one hn_odd
        _ = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hn4
    simpa [hJ_neg_one] using this
  obtain ⟨b, hb2⟩ := exists_b_sq_congr_neg_of_jacobi_q_eq_one n q hn_odd hqp hq1 hJ_q
  -- Reduce modulo `q` (from the stronger statement modulo `2*q`).
  have hq_dvd_2q : (q : ℤ) ∣ (2 * q : ℤ) := by
    simpa [mul_comm] using (dvd_mul_left (q : ℤ) (2 : ℤ))
  have hbq : b ^ 2 ≡ - (n : ℤ) [ZMOD (q : ℤ)] := Int.ModEq.of_dvd hq_dvd_2q hb2
  exact ⟨q, hqp, hq1, hq_modEq, ⟨b, hbq⟩⟩

/-- Existence of `b` such that `b² ≡ -n (mod 2q)` (Ankeny, `n % 8 = 3` specialization). -/
lemma exists_ankeny_b (n q : ℕ) (hn : n % 8 = 3) (hq : Nat.Prime q) (hq1 : q % 4 = 1)
    (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) :
    ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (2 * q)] := by
  classical
  have hn_odd : Odd n := GeometryOfNumbers.NumberTheory.odd_of_mod8_eq3 hn
  have hn0 : n ≠ 0 := by
    intro h0; subst h0
    simp at hn

  have hq_odd : Odd q := by
    -- `q % 4 = 1` rules out `q = 2`, hence `q` is odd.
    have hq_ne2 : q ≠ 2 := by
      intro hq2; subst hq2
      simp at hq1
    exact hq.odd_of_ne_two hq_ne2

  have hcop2q : Nat.Coprime 2 q := Nat.coprime_two_left.2 hq_odd

  -- Step 1: compute `J(q | n)` from the congruence `2*q ≡ -1 (mod n)`.
  have h2unit : IsUnit (2 : ZMod n) := GeometryOfNumbers.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
  have h2q_mod_n : (2 * (q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] :=
    GeometryOfNumbers.NumberTheory.mul_int_modEq_neg_one_of_q_eq_neg_inv n 2 q h2unit (by simpa using hq_mod)

  have hJ_2q : J(2 * (q : ℤ) | n) = J(-1 | n) := by
    -- Jacobi symbol depends only on the numerator mod `n`.
    refine jacobiSym.mod_left' (a₁ := (2 * (q : ℤ))) (a₂ := (-1 : ℤ)) (b := n) ?_
    simpa using h2q_mod_n.eq

  have hn4 : n % 4 = 3 := by omega

  have hJ_neg_one : J(-1 | n) = (-1 : ℤ) := by
    -- `J(-1 | n) = χ₄ n = -1` since `n % 4 = 3`.
    calc
      J(-1 | n) = ZMod.χ₄ n := jacobiSym.at_neg_one hn_odd
      _ = (-1 : ℤ) := ZMod.χ₄_nat_three_mod_four hn4

  have hJ_two : J(2 | n) = (-1 : ℤ) := by
    -- `J(2 | n) = χ₈ n = -1` since `n % 8 = 3`.
    calc
      J(2 | n) = ZMod.χ₈ n := jacobiSym.at_two hn_odd
      _ = (-1 : ℤ) := by
        -- Reduce to the explicit value at `n % 8 = 3`.
        have hred : ZMod.χ₈ n = ZMod.χ₈ (n % 8 : ℕ) := by
          simpa using (ZMod.χ₈_nat_mod_eight n)
        -- `χ₈ 3 = -1` by the definition of `χ₈ : MulChar (ZMod 8) ℤ`.
        have hval : ZMod.χ₈ (3 : ℕ) = (-1 : ℤ) := by decide
        simpa [hred, hn] using hval

  have hJ_q : J((q : ℤ) | n) = (1 : ℤ) := by
    -- From `J(2*q|n) = J(2|n)*J(q|n)` and the computed values, solve for `J(q|n)`.
    have hmul : J((2 : ℤ) * (q : ℤ) | n) = J(2 | n) * J((q : ℤ) | n) := jacobiSym.mul_left 2 q n
    have : J(2 | n) * J((q : ℤ) | n) = (-1 : ℤ) := by
      -- rewrite the LHS as `J(2*q|n)` then use the mod-`n` identification.
      have : J((2 : ℤ) * (q : ℤ) | n) = (-1 : ℤ) := by simpa [mul_assoc] using (hJ_2q.trans hJ_neg_one)
      simpa [hmul] using this
    -- `(-1) * J(q|n) = (-1)` implies `J(q|n) = 1`.
    -- We use the computed value `J(2|n) = -1`.
    have : (-1 : ℤ) * J((q : ℤ) | n) = (-1 : ℤ) := by simpa [hJ_two] using this
    -- cancel `(-1)`
    simpa using (mul_left_cancel₀ (by decide : (-1 : ℤ) ≠ 0) this)

  -- Step 2+: the remaining work is residue-agnostic once `J(q|n)=1` is known.
  exact exists_b_sq_congr_neg_of_jacobi_q_eq_one n q hn_odd hq hq1 hJ_q

/-- Existence of `b` such that `b² ≡ -n (mod 2q)` (Ankeny, `n % 8 = 1` specialization).

This uses the *same* “Ankeny prime” congruence `2q ≡ -1 (mod n)` as the `3 mod 8` branch.
The only difference is the Jacobi-symbol computation:
- when `n % 8 = 3` we have `J(2|n) = -1` and `J(-1|n) = -1`,
- when `n % 8 = 1` we have `J(2|n) = 1` and `J(-1|n) = 1`,
so in both cases we can solve `J(q|n) = 1` from `J(2q|n) = J(-1|n)`. -/
lemma exists_ankeny_b_one_mod_eight (n q : ℕ) (hn : n % 8 = 1) (hq : Nat.Prime q)
    (hq1 : q % 4 = 1) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) :
    ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (2 * q)] := by
  classical
  have hn_odd : Odd n := by
    have : n % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have hn0 : n ≠ 0 := by
    intro h0; subst h0
    simp at hn

  have hq_odd : Odd q := by
    -- `q % 4 = 1` rules out `q = 2`, hence `q` is odd.
    have hq_ne2 : q ≠ 2 := by
      intro hq2; subst hq2
      simp at hq1
    exact hq.odd_of_ne_two hq_ne2

  -- Step 1: compute `J(q | n)` from the congruence `2*q ≡ -1 (mod n)`.
  have h2unit : IsUnit (2 : ZMod n) := GeometryOfNumbers.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
  have h2q_mod_n : (2 * (q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] :=
    GeometryOfNumbers.NumberTheory.mul_int_modEq_neg_one_of_q_eq_neg_inv n 2 q h2unit (by simpa using hq_mod)

  have hJ_2q : J(2 * (q : ℤ) | n) = J(-1 | n) := by
    -- Jacobi symbol depends only on the numerator mod `n`.
    refine jacobiSym.mod_left' (a₁ := (2 * (q : ℤ))) (a₂ := (-1 : ℤ)) (b := n) ?_
    simpa using h2q_mod_n.eq

  have hn4 : n % 4 = 1 := by omega

  have hJ_neg_one : J(-1 | n) = (1 : ℤ) := by
    -- `J(-1 | n) = χ₄ n = 1` since `n % 4 = 1`.
    calc
      J(-1 | n) = ZMod.χ₄ n := jacobiSym.at_neg_one hn_odd
      _ = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hn4

  have hJ_two : J(2 | n) = (1 : ℤ) := by
    -- `J(2 | n) = χ₈ n = 1` since `n % 8 = 1`.
    calc
      J(2 | n) = ZMod.χ₈ n := jacobiSym.at_two hn_odd
      _ = (1 : ℤ) := by
        have hred : ZMod.χ₈ n = ZMod.χ₈ (n % 8 : ℕ) := by
          simpa using (ZMod.χ₈_nat_mod_eight n)
        have hval : ZMod.χ₈ (1 : ℕ) = (1 : ℤ) := by decide
        simpa [hred, hn] using hval

  have hJ_q : J((q : ℤ) | n) = (1 : ℤ) := by
    -- From `J(2*q|n) = J(2|n)*J(q|n)` and the computed values, solve for `J(q|n)`.
    have hmul : J((2 : ℤ) * (q : ℤ) | n) = J(2 | n) * J((q : ℤ) | n) := jacobiSym.mul_left 2 q n
    have : J(2 | n) * J((q : ℤ) | n) = (1 : ℤ) := by
      have : J((2 : ℤ) * (q : ℤ) | n) = (1 : ℤ) := by
        simpa [mul_assoc] using (hJ_2q.trans hJ_neg_one)
      simpa [hmul] using this
    have : (1 : ℤ) * J((q : ℤ) | n) = (1 : ℤ) := by simpa [hJ_two] using this
    simpa using this

  -- Step 2+: the remaining work is residue-agnostic once `J(q|n)=1` is known.
  exact exists_b_sq_congr_neg_of_jacobi_q_eq_one n q hn_odd hq hq1 hJ_q

/-- The Ankeny lattice `L = { (x,y,z) : x ≡ y (mod n), y ≡ bz (mod 2q) }`. -/
def ankeny_lattice (n q : ℕ) (b : ℤ) : AddSubgroup (Fin 3 → ℝ) where
  carrier := { p | ∃ x y z : ℤ, p 0 = x ∧ p 1 = y ∧ p 2 = z ∧ x ≡ y [ZMOD n] ∧ y ≡ b * z [ZMOD (2 * q)] }
  add_mem' := by
    intro a a' ⟨x1, y1, z1, hx1, hy1, hz1, hxy1, hybz1⟩ ⟨x2, y2, z2, hx2, hy2, hz2, hxy2, hybz2⟩
    refine ⟨x1 + x2, y1 + y2, z1 + z2, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hx1, hx2]
    · simp [hy1, hy2]
    · simp [hz1, hz2]
    · exact hxy1.add hxy2
    · calc (y1 + y2 : ℤ) ≡ b * z1 + b * z2 [ZMOD (2 * q)] := hybz1.add hybz2
        _ = b * (z1 + z2) := by ring
  zero_mem' := by
    refine ⟨0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Int.ModEq.refl]
  neg_mem' := by
    intro a ⟨x, y, z, hx, hy, hz, hxy, hybz⟩
    use -x, -y, -z
    constructor; simp [hx]
    constructor; simp [hy]
    constructor; simp [hz]
    constructor; exact hxy.neg
    calc (-y : ℤ) ≡ -(b * z) [ZMOD (2 * q)] := hybz.neg
      _ = b * (-z) := by ring

/-!
### A `q`-modulus variant lattice (for the `Q₁ = qx² + y² + nz²` route)

This is the congruence-defined lattice one would use with the `q ≡ -1 (mod n)` setup:
- `x ≡ y (mod n)` (same as Ankeny),
- `y ≡ b*z (mod q)` (note: modulus is `q`, not `2*q`).

This section defines the additive subgroup and the basic “arithmetic glue” lemmas (span-lattice inclusion
and the `Q₁` modular identity). The corresponding Minkowski step is implemented elsewhere in this file
as `exists_ankeny_representation_q1`, which produces a nontrivial triple satisfying
`q*x^2 + y^2 + n*z^2 = n*q` under the usual congruence hypotheses.
-/

/-- Variant lattice for the `Q₁` route: `x ≡ y (mod n)` and `y ≡ b*z (mod q)`. -/
def ankeny_lattice_q1 (n q : ℕ) (b : ℤ) : AddSubgroup (Fin 3 → ℝ) where
  carrier := { p | ∃ x y z : ℤ, p 0 = x ∧ p 1 = y ∧ p 2 = z ∧ x ≡ y [ZMOD n] ∧ y ≡ b * z [ZMOD q] }
  add_mem' := by
    intro a a' ⟨x1, y1, z1, hx1, hy1, hz1, hxy1, hybz1⟩ ⟨x2, y2, z2, hx2, hy2, hz2, hxy2, hybz2⟩
    refine ⟨x1 + x2, y1 + y2, z1 + z2, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hx1, hx2]
    · simp [hy1, hy2]
    · simp [hz1, hz2]
    · exact hxy1.add hxy2
    · calc (y1 + y2 : ℤ) ≡ b * z1 + b * z2 [ZMOD q] := hybz1.add hybz2
        _ = b * (z1 + z2) := by ring
  zero_mem' := by
    refine ⟨0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Int.ModEq.refl]
  neg_mem' := by
    intro a ⟨x, y, z, hx, hy, hz, hxy, hybz⟩
    use -x, -y, -z
    constructor; simp [hx]
    constructor; simp [hy]
    constructor; simp [hz]
    constructor; exact hxy.neg
    calc (-y : ℤ) ≡ -(b * z) [ZMOD q] := hybz.neg
      _ = b * (-z) := by ring

/-- Arithmetic glue: the explicit covolume lattice is a sublattice of the congruence-defined Ankeny lattice. -/
lemma ankeny_span_lattice_subset_ankeny_lattice (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    (ankeny_span_lattice n q b hn hq : Set E3) ⊆ ankeny_lattice n q b := by
  classical
  intro p hp
  -- Work in the underlying ℤ-submodule `span ℤ (range basis)`.
  let B : Module.Basis (Fin 3) ℝ E3 := ankeny_span_basis n q b hn hq
  have hp' : p ∈ (Submodule.span ℤ (Set.range B) : Set E3) := by
    simpa [ankeny_span_lattice, B] using hp
  -- It suffices to show `span ℤ (range B) ≤ (ankeny_lattice ...).toIntSubmodule`.
  have hle :
      (Submodule.span ℤ (Set.range B)) ≤ (ankeny_lattice n q b).toIntSubmodule := by
    refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨i, rfl⟩
    -- Show each basis vector satisfies the defining congruences.
    fin_cases i
    · -- i = 0: vector `(n, 0, 0)`
      have hx0 : (B 0) 0 = (n : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (0 : Fin 3) 0)
      have hx1 : (B 0) 1 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (0 : Fin 3) 1)
      have hx2 : (B 0) 2 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (0 : Fin 3) 2)
      have hxy : (n : ℤ) ≡ (0 : ℤ) [ZMOD n] := by
        refine (Int.modEq_iff_dvd).2 ?_
        simp
      have hybz : (0 : ℤ) ≡ b * (0 : ℤ) [ZMOD (2 * q)] := by
        simpa using (Int.ModEq.refl (0 : ℤ))
      have : (B 0) ∈ ankeny_lattice n q b := by
        refine ⟨(n : ℤ), 0, 0, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
    · -- i = 1: vector `(2q, 2q, 0)`
      have hx0 : (B 1) 0 = (2 * q : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (1 : Fin 3) 0)
      have hx1 : (B 1) 1 = (2 * q : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (1 : Fin 3) 1)
      have hx2 : (B 1) 2 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (1 : Fin 3) 2)
      have hxy : (2 * q : ℤ) ≡ (2 * q : ℤ) [ZMOD n] := by
        simpa using (Int.ModEq.refl (2 * q : ℤ))
      have hybz : (2 * q : ℤ) ≡ b * (0 : ℤ) [ZMOD (2 * q)] := by
        -- `2q ≡ 0 (mod 2q)`
        refine (Int.modEq_iff_dvd).2 ?_
        simp
      have : (B 1) ∈ ankeny_lattice n q b := by
        refine ⟨(2 * q : ℤ), (2 * q : ℤ), 0, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
    · -- i = 2: vector `(b, b, 1)`
      have hx0 : (B 2) 0 = (b : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (2 : Fin 3) 0)
      have hx1 : (B 2) 1 = (b : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (2 : Fin 3) 1)
      have hx2 : (B 2) 2 = (1 : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (2 : Fin 3) 2)
      have hxy : b ≡ b [ZMOD n] := by
        simpa using (Int.ModEq.refl b)
      have hybz : b ≡ b * (1 : ℤ) [ZMOD (2 * q)] := by
        simpa using (Int.ModEq.refl b)
      have : (B 2) ∈ ankeny_lattice n q b := by
        refine ⟨b, b, 1, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
  -- Conclude from `hle` and `hp'`.
  have : p ∈ (ankeny_lattice n q b).toIntSubmodule := hle hp'
  -- Convert `toIntSubmodule` membership back to set membership.
  simpa [AddSubgroup.coe_toIntSubmodule] using this

/-- Q₁-variant inclusion: the explicit span lattice (covolume `n*q`) sits inside the congruence lattice
`ankeny_lattice_q1` (`x ≡ y [ZMOD n]`, `y ≡ b*z [ZMOD q]`). -/
lemma ankeny_span_lattice_q1_subset_ankeny_lattice_q1 (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    (ankeny_span_lattice_q1 n q b hn hq : Set E3) ⊆ ankeny_lattice_q1 n q b := by
  classical
  intro p hp
  let B : Module.Basis (Fin 3) ℝ E3 := ankeny_span_basis_q1 n q b hn hq
  have hp' : p ∈ (Submodule.span ℤ (Set.range B) : Set E3) := by
    simpa [ankeny_span_lattice_q1, B] using hp
  have hle :
      (Submodule.span ℤ (Set.range B)) ≤ (ankeny_lattice_q1 n q b).toIntSubmodule := by
    refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i
    · -- i = 0: vector `(n, 0, 0)`
      have hx0 : (B 0) 0 = (n : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (0 : Fin 3) 0)
      have hx1 : (B 0) 1 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (0 : Fin 3) 1)
      have hx2 : (B 0) 2 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (0 : Fin 3) 2)
      have hxy : (n : ℤ) ≡ (0 : ℤ) [ZMOD n] := by
        refine (Int.modEq_iff_dvd).2 ?_
        simp
      have hybz : (0 : ℤ) ≡ b * (0 : ℤ) [ZMOD q] := by
        simpa using (Int.ModEq.refl (0 : ℤ))
      have : (B 0) ∈ ankeny_lattice_q1 n q b := by
        refine ⟨(n : ℤ), 0, 0, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
    · -- i = 1: vector `(q, q, 0)`
      have hx0 : (B 1) 0 = (q : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (1 : Fin 3) 0)
      have hx1 : (B 1) 1 = (q : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (1 : Fin 3) 1)
      have hx2 : (B 1) 2 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (1 : Fin 3) 2)
      have hxy : (q : ℤ) ≡ (q : ℤ) [ZMOD n] := by
        simpa using (Int.ModEq.refl (q : ℤ))
      have hybz : (q : ℤ) ≡ b * (0 : ℤ) [ZMOD q] := by
        -- `q ≡ 0 (mod q)`
        refine (Int.modEq_iff_dvd).2 ?_
        simp
      have : (B 1) ∈ ankeny_lattice_q1 n q b := by
        refine ⟨(q : ℤ), (q : ℤ), 0, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
    · -- i = 2: vector `(b, b, 1)`
      have hx0 : (B 2) 0 = (b : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (2 : Fin 3) 0)
      have hx1 : (B 2) 1 = (b : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (2 : Fin 3) 1)
      have hx2 : (B 2) 2 = (1 : ℝ) := by
        simpa [B, ankeny_span_matrix_q1] using (ankeny_span_basis_q1_apply n q b hn hq (2 : Fin 3) 2)
      have hxy : b ≡ b [ZMOD n] := by
        simpa using (Int.ModEq.refl b)
      have hybz : b ≡ b * (1 : ℤ) [ZMOD q] := by
        simpa using (Int.ModEq.refl b)
      have : (B 2) ∈ ankeny_lattice_q1 n q b := by
        refine ⟨b, b, 1, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
  have : p ∈ (ankeny_lattice_q1 n q b).toIntSubmodule := hle hp'
  simpa [AddSubgroup.coe_toIntSubmodule] using this

/-- A convenient full-rank ℤ-lattice for Ankeny has covolume `2nq`. -/
lemma ankeny_lattice_covolume (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    ∃ (L : AddSubgroup (Fin 3 → ℝ)) (F : Set (Fin 3 → ℝ)),
      IsAddFundamentalDomain L F volume ∧
      volume F = (2 * n * q : ℝ≥0∞) ∧
      (L : Set (Fin 3 → ℝ)).Countable ∧
      (L : Set (Fin 3 → ℝ)) ⊆ ankeny_lattice n q b := by
  classical
  let L : AddSubgroup E3 := ankeny_span_lattice n q b hn hq
  let F : Set E3 := ankeny_span_fundamentalDomain n q b hn hq
  refine ⟨L, F, ?_, ?_, ?_, ?_⟩
  · simpa [L, F] using ankeny_span_isAddFundamentalDomain n q b hn hq
  · simpa [F] using ankeny_span_volume_fundamentalDomain n q b hn hq
  · -- Countability of the ℤ-span lattice.
    have : Countable (↥L) := by
      -- `L` is a `Submodule.span ℤ` of a finite `Set.range`, hence countable.
      change Countable (Submodule.span ℤ (Set.range (ankeny_span_basis n q b hn hq)))
      infer_instance
    -- Convert subtype-countability into set-countability.
    have hrange : (Set.range (fun x : (↥L) => (x : E3))) = (L : Set E3) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    simpa [hrange] using (Set.countable_range (fun x : (↥L) => (x : E3)))
  · -- Inclusion into the congruence-defined lattice is the arithmetic glue step.
    simpa [L] using ankeny_span_lattice_subset_ankeny_lattice n q b hn hq

/-- The quadratic form `Q = 2qx² + y² + nz²`. -/
def ankeny_Q (n q : ℕ) (x y z : ℤ) : ℤ := 2 * q * x^2 + y^2 + n * z^2

/-!
### A `q ≡ -1 (mod n)` arithmetic glue lemma

For the remaining reduced residue class `n % 8 = 5`, the same *shape* of argument is plausible,
but with a different modulus choice: take `q ≡ -1 (mod n)` and use
\[
  Q_1(x,y,z) = qx^2 + y^2 + nz^2.
\]

This section only extracts the modular-arithmetic glue (no geometry yet).
-/

/-- The quadratic form `Q₁ = qx² + y² + nz²` (integer-valued). -/
def ankeny_Q1 (n q : ℕ) (x y z : ℤ) : ℤ := q * x^2 + y^2 + n * z^2

/-- If
- `q ≡ -1 [ZMOD n]`,
- `x ≡ y [ZMOD n]`,
- `y ≡ b*z [ZMOD q]`, and
- `b^2 ≡ -n [ZMOD q]`,

then `Q₁(x,y,z) ≡ 0 [ZMOD n*q]` (CRT, assuming `gcd(n,q)=1`).

This is the arithmetic interface needed for a future `n % 8 = 5` lattice. -/
lemma ankeny_Q1_mod (n q : ℕ) (b x y z : ℤ)
    (hnq : Nat.Coprime n q)
    (hq : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)])
    (hxy : x ≡ y [ZMOD (n : ℤ)])
    (hybz : y ≡ b * z [ZMOD (q : ℤ)])
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (q : ℤ)]) :
    ankeny_Q1 n q x y z ≡ 0 [ZMOD (n : ℤ) * (q : ℤ)] := by
  -- Part 1: mod `q`.
  have hQ_mod_q : ankeny_Q1 n q x y z ≡ 0 [ZMOD (q : ℤ)] := by
    have hy2 : y ^ 2 ≡ (b * z) ^ 2 [ZMOD (q : ℤ)] := hybz.pow 2
    have hy2' : y ^ 2 ≡ b ^ 2 * z ^ 2 [ZMOD (q : ℤ)] := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy2
    have hb_mul : b ^ 2 * z ^ 2 ≡ (-(n : ℤ)) * z ^ 2 [ZMOD (q : ℤ)] :=
      Int.ModEq.mul_right (z ^ 2) hb
    have hy_nz : y ^ 2 + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (q : ℤ)] := by
      have h1 :
          y ^ 2 + (n : ℤ) * z ^ 2 ≡ b ^ 2 * z ^ 2 + (n : ℤ) * z ^ 2 [ZMOD (q : ℤ)] :=
        hy2'.add (Int.ModEq.refl _)
      have h2 :
          b ^ 2 * z ^ 2 + (n : ℤ) * z ^ 2 ≡ (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 [ZMOD (q : ℤ)] :=
        hb_mul.add (Int.ModEq.refl _)
      have h3 : (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 = 0 := by ring
      exact h1.trans (h2.trans (by simpa [h3] using (Int.ModEq.refl (0 : ℤ))))
    have hqxx : (q : ℤ) * x ^ 2 ≡ 0 [ZMOD (q : ℤ)] := by
      refine (Int.modEq_zero_iff_dvd).2 ?_
      exact dvd_mul_right (q : ℤ) (x ^ 2)
    have : (q : ℤ) * x ^ 2 + (y ^ 2 + (n : ℤ) * z ^ 2) ≡ 0 [ZMOD (q : ℤ)] := by
      simpa [add_assoc, add_comm, add_left_comm] using (hqxx.add hy_nz)
    simpa [ankeny_Q1, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this

  -- Part 2: mod `n`.
  have hQ_mod_n : ankeny_Q1 n q x y z ≡ 0 [ZMOD (n : ℤ)] := by
    have hx2 : x ^ 2 ≡ y ^ 2 [ZMOD (n : ℤ)] := hxy.pow 2
    have hmul : (q : ℤ) * x ^ 2 ≡ (q : ℤ) * y ^ 2 [ZMOD (n : ℤ)] :=
      Int.ModEq.mul_left (q : ℤ) hx2
    have hq1 : (q : ℤ) + 1 ≡ 0 [ZMOD (n : ℤ)] := by
      -- add 1 to `q ≡ -1`.
      simpa [add_assoc, add_left_comm, add_comm] using (hq.add_right 1)
    have hq1y : ((q : ℤ) + 1) * (y ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      -- `mul_right` yields `((q+1)*y^2) ≡ (0*y^2)`; normalize the RHS.
      simpa using (Int.ModEq.mul_right (y ^ 2) hq1)
    have hqy : (q : ℤ) * (y ^ 2) + (y ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      have : (q : ℤ) * (y ^ 2) + (y ^ 2) = ((q : ℤ) + 1) * (y ^ 2) := by ring
      simpa [this] using hq1y
    have hnz : (n : ℤ) * (z ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      refine (Int.modEq_zero_iff_dvd).2 ?_
      exact dvd_mul_right (n : ℤ) (z ^ 2)
    have hsum : (q : ℤ) * x ^ 2 + (y ^ 2) + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (n : ℤ)] := by
      -- replace `q*x^2` by `q*y^2`, then use `(q+1)*y^2 ≡ 0`.
      have h1 : (q : ℤ) * x ^ 2 + y ^ 2 ≡ (q : ℤ) * y ^ 2 + y ^ 2 [ZMOD (n : ℤ)] :=
        hmul.add (Int.ModEq.refl _)
      have h2 : (q : ℤ) * y ^ 2 + y ^ 2 + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (n : ℤ)] := by
        simpa [add_assoc] using (hqy.add hnz)
      exact (h1.add (Int.ModEq.refl _)).trans (by
        simpa [add_assoc, add_left_comm, add_comm] using h2)
    simpa [ankeny_Q1, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hsum

  -- CRT combine.
  have hmn : (n : ℤ).natAbs.Coprime (q : ℤ).natAbs := by
    simpa using hnq
  exact (Int.modEq_and_modEq_iff_modEq_mul (a := ankeny_Q1 n q x y z) (b := 0) (m := (n : ℤ))
    (n := (q : ℤ)) hmn).1 ⟨hQ_mod_n, hQ_mod_q⟩

/-- Any point in the Ankeny lattice satisfies `Q ≡ 0 (mod 2nq)`. -/
lemma ankeny_Q_mod (n q : ℕ) (b : ℤ) (x y z : ℤ)
    (hn_odd : Odd n)
    (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (hxy : x ≡ y [ZMOD n])
    (hybz : y ≡ b * z [ZMOD (2 * q)])
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (2 * q)]) :
    ankeny_Q n q x y z ≡ 0 [ZMOD (2 * n * q)] := by
  -- This lemma is the “algebraic glue” used after the Minkowski step:
  --
  -- - mod `n`: use `x ≡ y` and `2q ≡ -1` (from `hq_mod`)
  -- - mod `2q`: use `y ≡ b z` and `b^2 ≡ -n` (from `hb`)
  -- - combine by CRT (since `gcd(n,2q)=1` in the Ankeny setup)
  --
  -- We start by proving the mod-`2q` part, since it is self-contained.
  have hQ_mod_2q : ankeny_Q n q x y z ≡ 0 [ZMOD (2 * q : ℤ)] := by
    have hy2 : y ^ 2 ≡ (b * z) ^ 2 [ZMOD (2 * q : ℤ)] := hybz.pow 2
    have hy2' : y ^ 2 ≡ b ^ 2 * z ^ 2 [ZMOD (2 * q : ℤ)] := by
      -- `(b*z)^2 = b^2 * z^2`
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy2
    have hb_mul : b ^ 2 * z ^ 2 ≡ (-(n : ℤ)) * z ^ 2 [ZMOD (2 * q : ℤ)] :=
      Int.ModEq.mul_right (z ^ 2) hb
    have hsum_cancel : (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 = 0 := by ring
    have hy_nz : y ^ 2 + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (2 * q : ℤ)] := by
      have h1 : y ^ 2 + (n : ℤ) * z ^ 2 ≡ b ^ 2 * z ^ 2 + (n : ℤ) * z ^ 2 [ZMOD (2 * q : ℤ)] :=
        (hy2'.add (Int.ModEq.refl _))
      have h2 : b ^ 2 * z ^ 2 + (n : ℤ) * z ^ 2 ≡ (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 [ZMOD (2 * q : ℤ)] :=
        (hb_mul.add (Int.ModEq.refl _))
      have h3 : (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (2 * q : ℤ)] := by
        simpa [hsum_cancel] using (Int.ModEq.refl (0 : ℤ))
      exact h1.trans (h2.trans h3)
    -- The `2q*x^2` term is 0 modulo `2q`.
    have h2qxx : (2 * (q : ℤ)) * x ^ 2 ≡ 0 [ZMOD (2 * q : ℤ)] := by
      refine (Int.modEq_zero_iff_dvd).2 ?_
      exact dvd_mul_right (2 * (q : ℤ)) (x ^ 2)
    -- Assemble.
    have : (2 * (q : ℤ)) * x ^ 2 + (y ^ 2 + (n : ℤ) * z ^ 2) ≡ 0 [ZMOD (2 * q : ℤ)] := by
      simpa [add_assoc, add_comm, add_left_comm] using (h2qxx.add hy_nz)
    simpa [ankeny_Q, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this

  -- Step 2: the mod-`n` part. This is where `hq_mod` is used to derive `2q ≡ -1 (mod n)`.
  have h2unit : IsUnit (2 : ZMod n) := GeometryOfNumbers.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
  have hqunit : IsUnit (q : ZMod n) := by
    have h2inv : IsUnit ((2 : ZMod n)⁻¹) := by
      -- `ZMod.isUnit_inv` is the correct lemma here (since `ZMod n` is not a division monoid).
      simpa using (ZMod.isUnit_inv (m := n) (n := (2 : ℤ)) (by simpa using h2unit))
    have : IsUnit (-( (2 : ZMod n)⁻¹)) := IsUnit.neg h2inv
    simpa [hq_mod] using this
  have hnq : Nat.Coprime q n :=
    (ZMod.isUnit_iff_coprime q n).1 (by simpa using hqunit)
  have hncoprime : Nat.Coprime n (2 * q) := by
    have hn2 : Nat.Coprime n 2 := (Nat.coprime_two_right.2 hn_odd)
    have hnq' : Nat.Coprime n q := (Nat.coprime_comm.1 hnq)
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (hn2.mul_right hnq')
  have hmn : (n : ℤ).natAbs.Coprime (2 * q : ℤ).natAbs := by
    simpa using hncoprime

  have h2q_add_one_dvd : (n : ℤ) ∣ (2 * (q : ℤ) + 1) := by
    -- In `ZMod n`, `2*q + 1 = 0`.
    have hZ : ((2 * (q : ℤ) + 1 : ℤ) : ZMod n) = 0 := by
      -- `q = -(2)⁻¹` ⇒ `2*q = -1` ⇒ `2*q + 1 = 0`
      have h2q : (2 : ZMod n) * (q : ZMod n) = (-1 : ZMod n) := by
        calc
          (2 : ZMod n) * (q : ZMod n)
              = (2 : ZMod n) * (-(2 : ZMod n)⁻¹) := by simpa [hq_mod]
          _ = -((2 : ZMod n) * (2 : ZMod n)⁻¹) := by ring
          _ = (-1 : ZMod n) := by
            have h : (2 : ZMod n) * (2 : ZMod n)⁻¹ = (1 : ZMod n) :=
              ZMod.mul_inv_of_unit (2 : ZMod n) h2unit
            simpa [h]
      -- Convert `2*q = -1` to `2*q + 1 = 0`.
      have : (2 : ZMod n) * (q : ZMod n) + 1 = 0 := by
        calc
          (2 : ZMod n) * (q : ZMod n) + 1 = (-1 : ZMod n) + 1 := by simpa [h2q]
          _ = 0 := by simp
      -- Rewrite into the exact `ℤ`-cast form used below.
      simpa [two_mul, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (q : ℤ) + 1) n).1 hZ

  have hQ_mod_n : ankeny_Q n q x y z ≡ 0 [ZMOD (n : ℤ)] := by
    have hx2 : x ^ 2 ≡ y ^ 2 [ZMOD (n : ℤ)] := hxy.pow 2
    have hmul : (2 * (q : ℤ)) * (x ^ 2) ≡ (2 * (q : ℤ)) * (y ^ 2) [ZMOD (n : ℤ)] :=
      Int.ModEq.mul_left _ hx2
    have hQ' :
        ankeny_Q n q x y z ≡ (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2) [ZMOD (n : ℤ)] := by
      have hadd :
          (2 * (q : ℤ)) * (x ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2)
            ≡ (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2) [ZMOD (n : ℤ)] :=
        (hmul.add (Int.ModEq.refl _)).add (Int.ModEq.refl _)
      simpa [ankeny_Q, pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hadd
    have h2q1 : (2 * (q : ℤ) + 1) ≡ 0 [ZMOD (n : ℤ)] :=
      (Int.modEq_zero_iff_dvd).2 h2q_add_one_dvd
    have hnz : (n : ℤ) * (z ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      refine (Int.modEq_zero_iff_dvd).2 ?_
      exact dvd_mul_right (n : ℤ) (z ^ 2)
    have hlin : (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) = (2 * (q : ℤ) + 1) * (y ^ 2) := by ring
    have hfirst : (2 * (q : ℤ) + 1) * (y ^ 2) ≡ 0 [ZMOD (n : ℤ)] :=
      by
        simpa using (Int.ModEq.mul_right (y ^ 2) h2q1)
    have : (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      simpa [hlin] using (hfirst.add hnz)
    exact hQ'.trans this

  -- Step 3: combine the mod-`n` and mod-`2q` statements.
  have hcrt : ankeny_Q n q x y z ≡ 0 [ZMOD (n : ℤ) * (2 * q : ℤ)] :=
    (Int.modEq_and_modEq_iff_modEq_mul hmn).1 ⟨hQ_mod_n, hQ_mod_2q⟩
  -- Normalize the modulus `(n : ℤ) * (2*q : ℤ)` to `2*n*q`.
  have hmul_nat : (n : ℤ) * (2 * q : ℤ) = (2 * n * q : ℤ) := by ring
  simpa [hmul_nat] using hcrt

/-- Minkowski application: there exists a representation `2qx² + y² + nz² = 2nq`. -/
lemma exists_ankeny_representation (n q : ℕ) (b : ℤ) (hn_pos : 0 < n) (hn_odd : Odd n) (hq : Nat.Prime q)
    (_hq1 : q % 4 = 1) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (2 * q)]) :
    ∃ x y z : ℤ,
      2 * q * x^2 + y^2 + n * z^2 = 2 * n * q ∧
      (x, y, z) ≠ (0, 0, 0) ∧
      x ≡ y [ZMOD (n : ℤ)] ∧
      y ≡ b * z [ZMOD (2 * q : ℤ)] := by
  classical
  -- The Ankeny ellipsoid in `E3`, expressed via an L2-ball preimage.
  let ell (nR qR : ℝ) : Set E3 := ankenyEllipsoidL2 nR qR

  have hq_pos : 0 < q := hq.pos

  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos

  -- Lattice + fundamental domain: use the explicit span lattice so `Countable ↥L` is available.
  let L : AddSubgroup E3 := ankeny_span_lattice n q b hn_pos hq_pos
  let F : Set E3 := ankeny_span_fundamentalDomain n q b hn_pos hq_pos

  -- Provide the `Countable ↥L` instance required by Minkowski.
  letI : Countable (↥L) := by
    -- `L` is (definitionally) a `Submodule.span ℤ` of a finite set, hence countable.
    change Countable (Submodule.span ℤ (Set.range (ankeny_span_basis n q b hn_pos hq_pos)))
    infer_instance

  have hfund : IsAddFundamentalDomain L F volume := by
    simpa [L, F] using ankeny_span_isAddFundamentalDomain n q b hn_pos hq_pos

  have hvolF : volume F = (2 * n * q : ℝ≥0∞) := by
    simpa [F] using ankeny_span_volume_fundamentalDomain n q b hn_pos hq_pos

  -- Symmetry: `x ∈ ell → -x ∈ ell`.
  have hsymm : ∀ x ∈ ell (n : ℝ) (q : ℝ), -x ∈ ell (n : ℝ) (q : ℝ) := by
    intro x hx
    dsimp [ell, ankenyEllipsoidL2, l2Ball] at hx ⊢
    -- `toLp` and `ankenyDiagMap` commute with negation, and the ball around `0` is symmetric.
    simpa [Metric.mem_ball, map_neg, dist_eq_norm, norm_neg] using hx

  -- Convexity: preimage of a convex ball under an affine map.
  have hconv : Convex ℝ (ell (n : ℝ) (q : ℝ)) := by
    -- Use the linear-equivalence spelling of `toLp` to build an affine map.
    let toLpLin : E3 →ₗ[ℝ] E3L2 :=
      (WithLp.linearEquiv (2 : ℝ≥0∞) ℝ E3).symm.toLinearMap
    let f : E3 →ᵃ[ℝ] E3L2 :=
      toLpLin.toAffineMap.comp (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ)).toAffineMap
    have hs :
        ell (n : ℝ) (q : ℝ) =
          f ⁻¹' Metric.ball (0 : E3L2) (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) := by
      ext x
      rfl
    simpa [hs, ell, l2Ball, f, toLpLin] using
      (Convex.affine_preimage
        (f := f)
        (s := Metric.ball (0 : E3L2) (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)))
        (convex_ball (0 : E3L2) (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ))))

  -- Left side simplification: `finrank E3 = 3`.
  have hrank : Module.finrank ℝ E3 = 3 := by simp [E3]

  -- Use the explicit volume formula and a coarse lower bound.
  have hineq :
      volume F * 2 ^ (Module.finrank ℝ E3) < volume (ell (n : ℝ) (q : ℝ)) := by
    have hL : volume F * 2 ^ (Module.finrank ℝ E3) = (16 * n * q : ℝ≥0∞) := by
      simp [hvolF, hrank, pow_succ, mul_left_comm, mul_comm]
      ring
    have hR : (16 * n * q : ℝ≥0∞) < volume (ell (n : ℝ) (q : ℝ)) := by
      simpa [ell] using volume_ankenyEllipsoidL2_gt_nat (n := n) (q := q) hn_pos hq_pos
    calc
      volume F * 2 ^ (Module.finrank ℝ E3) = (16 * n * q : ℝ≥0∞) := hL
      _ < volume (ell (n : ℝ) (q : ℝ)) := hR

  rcases
      GeometryOfNumbers.minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt
        (μ := volume) (L := L) (F := F) (s := ell (n : ℝ) (q : ℝ))
        hfund hsymm hconv hineq
    with ⟨p, hp0, hp_mem⟩

  -- Step 4: convert `p ∈ L` into explicit integer coordinates via the congruence-defined lattice.
  have hpL : ((p : E3) ∈ L) := p.property
  have hp_ank : (p : E3) ∈ ankeny_lattice n q b := by
    -- `L = ankeny_span_lattice ...` by definition, and we have an inclusion lemma.
    have hsub := ankeny_span_lattice_subset_ankeny_lattice n q b hn_pos hq_pos
    exact hsub (by simpa [L] using hpL)

  rcases hp_ank with ⟨x, y, z, hx0, hx1, hx2, hxy, hybz⟩

  have hxyz_ne : (x, y, z) ≠ (0, 0, 0) := by
    intro hxyz
    have hx' : x = 0 := by simpa using congrArg (fun t : ℤ × ℤ × ℤ => t.1) hxyz
    have hy' : y = 0 := by simpa using congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) hxyz
    have hz' : z = 0 := by simpa using congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) hxyz
    have hpz : (p : E3) = 0 := by
      funext i
      fin_cases i
      · simpa [hx0, hx']
      · simpa [hx1, hy']
      · simpa [hx2, hz']
    have : p = 0 := by
      -- ext on the underlying function
      ext i
      simpa [hpz]
    exact hp0 this

  -- Step 5: the arithmetic pin-down `Q = 2*n*q` from:
  -- - divisibility `Q ≡ 0 (mod 2*n*q)` (CRT glue), and
  -- - strict bound `0 < Q < 4*n*q` (ellipsoid membership).

  -- (a) Divisibility of `Q` by `2*n*q`.
  have hQmod : ankeny_Q n q x y z ≡ 0 [ZMOD (2 * n * q : ℤ)] := by
    simpa using ankeny_Q_mod n q b x y z hn_odd hq_mod hxy hybz hb
  have hdivQ : (2 * n * q : ℤ) ∣ ankeny_Q n q x y z :=
    (Int.modEq_zero_iff_dvd).1 hQmod

  -- (b) Strict upper bound from ellipsoid membership.
  have hp_diag_mem :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3)
        ∈ l2Ball (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) := by
    -- `p ∈ diagMap⁻¹' l2Ball ...`
    simpa [ell, ankenyEllipsoidL2] using hp_mem

  have hr_nonneg :
      0 ≤ GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ) := by
    -- `2 * sqrt(n*q) ≥ 0`.
    have hs : 0 ≤ Real.sqrt ((n : ℝ) * (q : ℝ)) := Real.sqrt_nonneg _
    have h2 : 0 ≤ (2 : ℝ) := by norm_num
    simpa [GeometryOfNumbers.Minkowski.ankenyBallRadius, mul_assoc] using mul_nonneg h2 hs

  have hsum_sq_lt :
      (∑ i : Fin 3,
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) i) ^ 2)
        < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
    -- Unfold `l2Ball` (preimage of a Euclidean ball) and use the standard `ball_zero_eq` characterization.
    have hp_ball :
        WithLp.toLp (2 : ℝ≥0∞)
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3))
          ∈ Metric.ball (0 : E3L2) (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) := by
      simpa [l2Ball] using hp_diag_mem
    have :
        WithLp.toLp (2 : ℝ≥0∞)
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3))
          ∈ {w : E3L2 |
                ∑ i : Fin 3, (w i) ^ 2
                  < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2} := by
      simpa [EuclideanSpace.ball_zero_eq (n := Fin 3)
              (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) hr_nonneg]
        using hp_ball
    -- `toLp` is the identity on coordinates, so we can drop it.
    simpa [WithLp.ofLp_toLp] using this

  -- Expand the diagonal map coordinatewise.
  have h0 :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 0
        = Real.sqrt (2 * (q : ℝ)) * ((p : E3) 0) := by
    simp [GeometryOfNumbers.Minkowski.ankenyDiagMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have h1 :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 1 = ((p : E3) 1) := by
    simp [GeometryOfNumbers.Minkowski.ankenyDiagMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have h2 :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 2
        = Real.sqrt (n : ℝ) * ((p : E3) 2) := by
    simp [GeometryOfNumbers.Minkowski.ankenyDiagMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

  have hQ_lt_real :
      (ankeny_Q n q x y z : ℝ) < 4 * (n : ℝ) * (q : ℝ) := by
    -- First rewrite the sum into three coordinates and apply `hsum_sq_lt`.
    have hsum3 :
        (Real.sqrt (2 * (q : ℝ)) * ((p : E3) 0)) ^ 2
          + ((p : E3) 1) ^ 2
          + (Real.sqrt (n : ℝ) * ((p : E3) 2)) ^ 2
          < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
      have : (∑ i : Fin 3, (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) i) ^ 2)
            =
          (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 0) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 1) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 2) ^ 2 := by
        simpa [Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      have hsum3' :
          (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 0) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 1) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 2) ^ 2
            < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
        -- rewrite the sum and use the bound
        simpa [this] using hsum_sq_lt
      simpa [h0, h1, h2] using hsum3'

    -- Convert the radius square to `4*n*q` and replace `p` coordinates by `(x,y,z)`.
    have hnq_nonneg : 0 ≤ (n : ℝ) * (q : ℝ) := by nlinarith
    have hr2 : (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 = 4 * (n : ℝ) * (q : ℝ) := by
      -- Avoid `simp` here (it can open irrelevant side goals). Do it by hand.
      set s : ℝ := Real.sqrt ((n : ℝ) * (q : ℝ))
      calc
        (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2
            = (2 * s) ^ 2 := by simp [GeometryOfNumbers.Minkowski.ankenyBallRadius, s]
        _ = 4 * (s ^ 2) := by
          simp [pow_two]
          ring
        _ = 4 * ((n : ℝ) * (q : ℝ)) := by
          -- `s^2 = n*q`
          simpa [s] using congrArg (fun t : ℝ => (4 : ℝ) * t) (Real.sq_sqrt hnq_nonneg)
        _ = 4 * (n : ℝ) * (q : ℝ) := by ring

    -- Now: LHS = `Q` as a real number.
    have hn_nonneg : 0 ≤ (n : ℝ) := by nlinarith
    have hq_nonneg : 0 ≤ (q : ℝ) := by nlinarith
    have h2_nonneg : 0 ≤ (2 : ℝ) := by norm_num
    have hx_term :
        (Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) * ((x : ℤ) : ℝ)) ^ 2
          = (2 * (q : ℝ)) * (((x : ℤ) : ℝ) ^ 2) := by
      -- `(√2 * √q * x)^2 = 2*q*x^2`
      simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
    have hz_term :
        (Real.sqrt (n : ℝ) * ((z : ℤ) : ℝ)) ^ 2 = (n : ℝ) * (((z : ℤ) : ℝ) ^ 2) := by
      simp [pow_two, mul_assoc, mul_left_comm, mul_comm]

    -- Rewrite `hsum3` into the exact inequality on `Q`.
    have : (ankeny_Q n q x y z : ℝ) < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
      -- substitute `p 0 = x`, `p 1 = y`, `p 2 = z`
      have hsum3_xyz :
          (Real.sqrt (2 * (q : ℝ)) * ((x : ℤ) : ℝ)) ^ 2
            + ((y : ℤ) : ℝ) ^ 2
            + (Real.sqrt (n : ℝ) * ((z : ℤ) : ℝ)) ^ 2
            < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hx0, hx1, hx2] using hsum3

      -- Rewrite the `x`-term into the split-sqrt form expected by our `hx_term`.
      have hsqrt2q :
          Real.sqrt (2 * (q : ℝ)) * ((x : ℤ) : ℝ) =
            Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) * ((x : ℤ) : ℝ) := by
        have : Real.sqrt (2 * (q : ℝ)) = Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) := by
          simpa using (Real.sqrt_mul (x := (2 : ℝ)) (y := (q : ℝ)) (zero_le_two : (0 : ℝ) ≤ (2 : ℝ)) hq_nonneg)
        simpa [this, mul_assoc, mul_left_comm, mul_comm]

      have hsum3_xyz' :
          (Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) * ((x : ℤ) : ℝ)) ^ 2
            + ((y : ℤ) : ℝ) ^ 2
            + (Real.sqrt (n : ℝ) * ((z : ℤ) : ℝ)) ^ 2
            < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hsqrt2q, add_assoc, add_left_comm, add_comm] using hsum3_xyz

      -- Turn LHS into `ankeny_Q` (as ℝ).
      have : (2 * (q : ℝ)) * (((x : ℤ) : ℝ) ^ 2) + ((y : ℤ) : ℝ) ^ 2 + (n : ℝ) * (((z : ℤ) : ℝ) ^ 2)
            < (GeometryOfNumbers.Minkowski.ankenyBallRadius (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hx_term, hz_term, add_assoc, add_left_comm, add_comm] using hsum3_xyz'

      simpa [ankeny_Q, pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this
    -- replace RHS by `4*n*q`
    simpa [hr2] using this

  have hQ_lt : ankeny_Q n q x y z < (4 * n * q : ℤ) := by
    exact_mod_cast hQ_lt_real

  have hQ_pos : 0 < ankeny_Q n q x y z := by
    -- `Q = 0` would force `x=y=z=0`, contradicting `hxyz_ne`.
    have hQ_nonneg : 0 ≤ ankeny_Q n q x y z := by
      dsimp [ankeny_Q]
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hQ_ne0 : ankeny_Q n q x y z ≠ 0 := by
      intro h0
      have hn' : (0 : ℤ) < n := by exact_mod_cast hn_pos
      have h2q_ne0 : (2 * (q : ℤ)) ≠ 0 := by
        have h2q_pos_nat : 0 < 2 * q := Nat.mul_pos (by decide : 0 < (2 : ℕ)) hq_pos
        exact ne_of_gt (by exact_mod_cast h2q_pos_nat)
      have hn_ne0 : (n : ℤ) ≠ 0 := ne_of_gt hn'
      -- from `Q=0` and nonnegativity of terms, force each square to be zero
      have hx_sq : x ^ 2 = 0 := by
        have : (2 * (q : ℤ)) * x ^ 2 = 0 := by
          dsimp [ankeny_Q] at h0
          nlinarith
        exact (mul_eq_zero.mp this).resolve_left h2q_ne0
      have hy_sq : y ^ 2 = 0 := by
        dsimp [ankeny_Q] at h0
        nlinarith
      have hz_sq : z ^ 2 = 0 := by
        have : (n : ℤ) * z ^ 2 = 0 := by
          dsimp [ankeny_Q] at h0
          nlinarith
        exact (mul_eq_zero.mp this).resolve_left hn_ne0
      have hx0' : x = 0 := sq_eq_zero_iff.mp hx_sq
      have hy0' : y = 0 := sq_eq_zero_iff.mp hy_sq
      have hz0' : z = 0 := sq_eq_zero_iff.mp hz_sq
      exact hxyz_ne (by simpa [hx0', hy0', hz0'])
    exact lt_of_le_of_ne' hQ_nonneg hQ_ne0

  -- (d) `Q` is a positive multiple of `2*n*q`, but also `Q < 2*(2*n*q)`, hence `Q = 2*n*q`.
  have hQ_eq : ankeny_Q n q x y z = (2 * n * q : ℤ) := by
    rcases hdivQ with ⟨t, ht⟩
    have hm_pos : 0 < (2 * n * q : ℤ) := by
      have h2n : 0 < 2 * n := Nat.mul_pos (by decide : 0 < (2 : ℕ)) hn_pos
      have h2nq : 0 < (2 * n) * q := Nat.mul_pos h2n hq_pos
      -- normalize to `2*n*q`
      have : 0 < 2 * n * q := by simpa [Nat.mul_assoc] using h2nq
      exact_mod_cast this
    have ht_pos : 0 < t := by
      have : 0 < (2 * n * q : ℤ) * t := by simpa [ht] using hQ_pos
      exact pos_of_mul_pos_right this (le_of_lt hm_pos)
    have ht_lt2 : t < 2 := by
      have hbound : ankeny_Q n q x y z < (2 * n * q : ℤ) * 2 := by
        have : (4 * n * q : ℤ) = (2 * n * q : ℤ) * 2 := by ring
        simpa [this] using hQ_lt
      have hmul : (2 * n * q : ℤ) * t < (2 * n * q : ℤ) * 2 := by
        -- avoid `simp` here; a `calc` with `ht.symm` is much cheaper
        calc
          (2 * n * q : ℤ) * t = ankeny_Q n q x y z := ht.symm
          _ < (2 * n * q : ℤ) * 2 := hbound
      exact lt_of_mul_lt_mul_left hmul hm_pos.le
    have ht_eq1 : t = 1 := by omega
    -- fold `t = 1` into the divisibility witness
    have ht' : ankeny_Q n q x y z = (2 * n * q : ℤ) * 1 := by
      simpa [ht_eq1] using ht
    simpa [mul_one] using ht'

  refine ⟨x, y, z, ?_, hxyz_ne, ?_, ?_⟩
  -- Unfold `Q` back into the target equation.
  simpa [ankeny_Q] using hQ_eq
  · -- `x ≡ y [ZMOD n]` from lattice membership.
    simpa using hxy
  · -- `y ≡ b*z [ZMOD 2q]` from lattice membership.
    -- `hybz : y ≡ b*z [ZMOD 2*q]` already has the right modulus.
    simpa [mul_assoc] using hybz

set_option maxHeartbeats 1200000 in
/-- Minkowski application (Q₁ route): there exists a representation
`q x^2 + y^2 + n z^2 = n*q` under the `q ≡ -1 (mod n)` arithmetic interface. -/
lemma exists_ankeny_representation_q1 (n q : ℕ) (b : ℤ)
    (hn_pos : 0 < n) (hq : Nat.Prime q)
    (hnq : Nat.Coprime n q)
    (_hq1 : q % 4 = 1)
    (hq_mod : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)])
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (q : ℤ)]) :
    ∃ x y z : ℤ,
      ankeny_Q1 n q x y z = n * q ∧
      (x, y, z) ≠ (0, 0, 0) ∧
      x ≡ y [ZMOD (n : ℤ)] ∧
      y ≡ b * z [ZMOD (q : ℤ)] := by
  classical
  -- The same diagonal-map ellipsoid, but with smaller radius `sqrt(2*n*q)`.
  let ell (nR qR : ℝ) : Set E3 := ankenyEllipsoidL2_q1 nR qR

  have hq_pos : 0 < q := hq.pos

  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos

  -- Lattice + fundamental domain: use the explicit span lattice so `Countable ↥L` is available.
  let L : AddSubgroup E3 := ankeny_span_lattice_q1 n q b hn_pos hq_pos
  let F : Set E3 := ankeny_span_fundamentalDomain_q1 n q b hn_pos hq_pos

  letI : Countable (↥L) := by
    change Countable (Submodule.span ℤ (Set.range (ankeny_span_basis_q1 n q b hn_pos hq_pos)))
    infer_instance

  have hfund : IsAddFundamentalDomain L F volume := by
    simpa [L, F] using ankeny_span_isAddFundamentalDomain_q1 n q b hn_pos hq_pos

  have hvolF : volume F = (n * q : ℝ≥0∞) := by
    simpa [F] using ankeny_span_volume_fundamentalDomain_q1 n q b hn_pos hq_pos

  -- Symmetry: `x ∈ ell → -x ∈ ell`.
  have hsymm : ∀ x ∈ ell (n : ℝ) (q : ℝ), -x ∈ ell (n : ℝ) (q : ℝ) := by
    intro x hx
    dsimp [ell, ankenyEllipsoidL2_q1, l2Ball] at hx ⊢
    simpa [Metric.mem_ball, map_neg, dist_eq_norm, norm_neg] using hx

  -- Convexity: preimage of a convex ball under an affine map.
  have hconv : Convex ℝ (ell (n : ℝ) (q : ℝ)) := by
    let toLpLin : E3 →ₗ[ℝ] E3L2 :=
      (WithLp.linearEquiv (2 : ℝ≥0∞) ℝ E3).symm.toLinearMap
    let f : E3 →ᵃ[ℝ] E3L2 :=
      toLpLin.toAffineMap.comp (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ)).toAffineMap
    have hs :
        ell (n : ℝ) (q : ℝ) =
          f ⁻¹' Metric.ball (0 : E3L2) (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) := by
      ext x
      rfl
    simpa [hs, ell, ankenyEllipsoidL2_q1, l2Ball, f, toLpLin] using
      (Convex.affine_preimage
        (f := f)
        (s := Metric.ball (0 : E3L2) (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)))
        (convex_ball (0 : E3L2) (ankenyBallRadius_q1 (n : ℝ) (q : ℝ))))

  -- `finrank E3 = 3`.
  have hrank : Module.finrank ℝ E3 = 3 := by simp [E3]

  have hineq :
      volume F * 2 ^ (Module.finrank ℝ E3) < volume (ell (n : ℝ) (q : ℝ)) := by
    have hL : volume F * 2 ^ (Module.finrank ℝ E3) = (8 * n * q : ℝ≥0∞) := by
      simp [hvolF, hrank, pow_succ, mul_left_comm, mul_comm]
      ring
    have hR : (8 * n * q : ℝ≥0∞) < volume (ell (n : ℝ) (q : ℝ)) := by
      simpa [ell] using volume_ankenyEllipsoidL2_q1_gt_nat (n := n) (q := q) hn_pos hq_pos
    calc
      volume F * 2 ^ (Module.finrank ℝ E3) = (8 * n * q : ℝ≥0∞) := hL
      _ < volume (ell (n : ℝ) (q : ℝ)) := hR

  rcases
      GeometryOfNumbers.minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt
        (μ := volume) (L := L) (F := F) (s := ell (n : ℝ) (q : ℝ))
        hfund hsymm hconv hineq
    with ⟨p, hp0, hp_mem⟩

  -- Convert `p ∈ L` into explicit integer coordinates via the congruence-defined lattice.
  have hpL : ((p : E3) ∈ L) := p.property
  have hp_ank : (p : E3) ∈ ankeny_lattice_q1 n q b := by
    have hsub := ankeny_span_lattice_q1_subset_ankeny_lattice_q1 n q b hn_pos hq_pos
    exact hsub (by simpa [L] using hpL)

  rcases hp_ank with ⟨x, y, z, hx0, hx1, hx2, hxy, hybz⟩

  have hxyz_ne : (x, y, z) ≠ (0, 0, 0) := by
    intro hxyz
    have hx' : x = 0 := by simpa using congrArg (fun t : ℤ × ℤ × ℤ => t.1) hxyz
    have hy' : y = 0 := by simpa using congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) hxyz
    have hz' : z = 0 := by simpa using congrArg (fun t : ℤ × ℤ × ℤ => t.2.2) hxyz
    have hpz : (p : E3) = 0 := by
      funext i
      fin_cases i
      · simpa [hx0, hx']
      · simpa [hx1, hy']
      · simpa [hx2, hz']
    have : p = 0 := by
      ext i
      simpa [hpz]
    exact hp0 this

  -- (a) Divisibility of `Q₁` by `n*q`.
  have hQmod : ankeny_Q1 n q x y z ≡ 0 [ZMOD (n : ℤ) * (q : ℤ)] := by
    exact ankeny_Q1_mod (n := n) (q := q) (b := b) (x := x) (y := y) (z := z)
      hnq hq_mod hxy hybz hb
  have hmul_nat : (n : ℤ) * (q : ℤ) = (n * q : ℤ) := by ring
  have hdivQ : (n * q : ℤ) ∣ ankeny_Q1 n q x y z := by
    have : (n : ℤ) * (q : ℤ) ∣ ankeny_Q1 n q x y z := (Int.modEq_zero_iff_dvd).1 hQmod
    simpa [hmul_nat] using this

  -- (b) Strict upper bound from ellipsoid membership: first bound `Q = 2q x² + y² + n z²`,
  -- then use `Q₁ ≤ Q`.
  have hp_diag_mem :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3)
        ∈ l2Ball (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) := by
    simpa [ell, ankenyEllipsoidL2_q1] using hp_mem

  have hr_nonneg :
      0 ≤ ankenyBallRadius_q1 (n : ℝ) (q : ℝ) := by
    simpa [ankenyBallRadius_q1] using Real.sqrt_nonneg (2 * ((n : ℝ) * (q : ℝ)))

  have hsum_sq_lt :
      (∑ i : Fin 3,
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) i) ^ 2)
        < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
    have hp_ball :
        WithLp.toLp (2 : ℝ≥0∞)
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3))
          ∈ Metric.ball (0 : E3L2) (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) := by
      simpa [l2Ball] using hp_diag_mem
    have :
        WithLp.toLp (2 : ℝ≥0∞)
            (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3))
          ∈ {w : E3L2 |
                ∑ i : Fin 3, (w i) ^ 2
                  < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2} := by
      simpa [EuclideanSpace.ball_zero_eq (n := Fin 3)
              (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) hr_nonneg]
        using hp_ball
    simpa [WithLp.ofLp_toLp] using this

  have h0 :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 0
        = Real.sqrt (2 * (q : ℝ)) * ((p : E3) 0) := by
    simp [GeometryOfNumbers.Minkowski.ankenyDiagMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have h1 :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 1 = ((p : E3) 1) := by
    simp [GeometryOfNumbers.Minkowski.ankenyDiagMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  have h2 :
      GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 2
        = Real.sqrt (n : ℝ) * ((p : E3) 2) := by
    simp [GeometryOfNumbers.Minkowski.ankenyDiagMap, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

  have hQ_lt_real :
      (ankeny_Q n q x y z : ℝ) < 2 * (n : ℝ) * (q : ℝ) := by
    have hsum3 :
        (Real.sqrt (2 * (q : ℝ)) * ((p : E3) 0)) ^ 2
          + ((p : E3) 1) ^ 2
          + (Real.sqrt (n : ℝ) * ((p : E3) 2)) ^ 2
          < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
      have : (∑ i : Fin 3, (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) i) ^ 2)
            =
          (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 0) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 1) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 2) ^ 2 := by
        simpa [Fin.sum_univ_three, add_assoc, add_left_comm, add_comm]
      have hsum3' :
          (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 0) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 1) ^ 2
            + (GeometryOfNumbers.Minkowski.ankenyDiagMap (n : ℝ) (q : ℝ) (p : E3) 2) ^ 2
            < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [this] using hsum_sq_lt
      simpa [h0, h1, h2] using hsum3'

    have hnq_nonneg : 0 ≤ 2 * ((n : ℝ) * (q : ℝ)) := by nlinarith [le_of_lt hnR, le_of_lt hqR]
    have hr2 : (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 = 2 * (n : ℝ) * (q : ℝ) := by
      simpa [ankenyBallRadius_q1, pow_two, Real.sq_sqrt hnq_nonneg, mul_assoc, mul_left_comm, mul_comm]

    have hq_nonneg : 0 ≤ (q : ℝ) := by nlinarith
    have hx_term :
        (Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) * ((x : ℤ) : ℝ)) ^ 2
          = (2 * (q : ℝ)) * (((x : ℤ) : ℝ) ^ 2) := by
      simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
    have hz_term :
        (Real.sqrt (n : ℝ) * ((z : ℤ) : ℝ)) ^ 2 = (n : ℝ) * (((z : ℤ) : ℝ) ^ 2) := by
      simp [pow_two, mul_assoc, mul_left_comm, mul_comm]

    have : (ankeny_Q n q x y z : ℝ) < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
      have hsum3_xyz :
          (Real.sqrt (2 * (q : ℝ)) * ((x : ℤ) : ℝ)) ^ 2
            + ((y : ℤ) : ℝ) ^ 2
            + (Real.sqrt (n : ℝ) * ((z : ℤ) : ℝ)) ^ 2
            < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hx0, hx1, hx2] using hsum3
      have hsqrt2q :
          Real.sqrt (2 * (q : ℝ)) * ((x : ℤ) : ℝ) =
            Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) * ((x : ℤ) : ℝ) := by
        have : Real.sqrt (2 * (q : ℝ)) = Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) := by
          simpa using (Real.sqrt_mul (x := (2 : ℝ)) (y := (q : ℝ)) (zero_le_two : (0 : ℝ) ≤ (2 : ℝ)) hq_nonneg)
        simpa [this, mul_assoc, mul_left_comm, mul_comm]
      have hsum3_xyz' :
          (Real.sqrt (2 : ℝ) * Real.sqrt (q : ℝ) * ((x : ℤ) : ℝ)) ^ 2
            + ((y : ℤ) : ℝ) ^ 2
            + (Real.sqrt (n : ℝ) * ((z : ℤ) : ℝ)) ^ 2
            < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hsqrt2q, add_assoc, add_left_comm, add_comm] using hsum3_xyz
      have :
          (2 * (q : ℝ)) * (((x : ℤ) : ℝ) ^ 2) + ((y : ℤ) : ℝ) ^ 2 + (n : ℝ) * (((z : ℤ) : ℝ) ^ 2)
            < (ankenyBallRadius_q1 (n : ℝ) (q : ℝ)) ^ 2 := by
        simpa [hx_term, hz_term, add_assoc, add_left_comm, add_comm] using hsum3_xyz'
      simpa [ankeny_Q, pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using this

    simpa [hr2] using this

  have hQ1_lt_real : (ankeny_Q1 n q x y z : ℝ) < 2 * (n : ℝ) * (q : ℝ) := by
    have hx_sq_nonneg : 0 ≤ (((x : ℤ) : ℝ) ^ 2) := sq_nonneg _
    have hle_x : (q : ℝ) * (((x : ℤ) : ℝ) ^ 2) ≤ (2 * (q : ℝ)) * (((x : ℤ) : ℝ) ^ 2) := by
      have : (q : ℝ) ≤ 2 * (q : ℝ) := by nlinarith
      exact mul_le_mul_of_nonneg_right this hx_sq_nonneg
    -- Work in a normalized real-expression form to keep automation cheap.
    set xr : ℝ := ((x : ℤ) : ℝ)
    set yr : ℝ := ((y : ℤ) : ℝ)
    set zr : ℝ := ((z : ℤ) : ℝ)
    have hle :
        (q : ℝ) * (xr ^ 2) + (yr ^ 2) + (n : ℝ) * (zr ^ 2)
          ≤ (2 * (q : ℝ)) * (xr ^ 2) + (yr ^ 2) + (n : ℝ) * (zr ^ 2) := by
      nlinarith [hle_x]
    have hle' : (ankeny_Q1 n q x y z : ℝ) ≤ (ankeny_Q n q x y z : ℝ) := by
      -- unfold both sides into the same expression and apply `hle`
      simpa [ankeny_Q1, ankeny_Q, xr, yr, zr, pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
        using hle
    exact lt_of_le_of_lt hle' hQ_lt_real

  have hQ1_lt : ankeny_Q1 n q x y z < (2 * n * q : ℤ) := by
    exact_mod_cast hQ1_lt_real

  have hQ1_pos : 0 < ankeny_Q1 n q x y z := by
    have hQ1_nonneg : 0 ≤ ankeny_Q1 n q x y z := by
      dsimp [ankeny_Q1]
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hQ1_ne0 : ankeny_Q1 n q x y z ≠ 0 := by
      intro h0
      have hn' : (0 : ℤ) < n := by exact_mod_cast hn_pos
      have hq' : (0 : ℤ) < q := by exact_mod_cast hq_pos
      have hq_ne0 : (q : ℤ) ≠ 0 := ne_of_gt hq'
      have hn_ne0 : (n : ℤ) ≠ 0 := ne_of_gt hn'
      have hx_sq : x ^ 2 = 0 := by
        have : (q : ℤ) * x ^ 2 = 0 := by
          dsimp [ankeny_Q1] at h0
          nlinarith
        exact (mul_eq_zero.mp this).resolve_left hq_ne0
      have hy_sq : y ^ 2 = 0 := by
        dsimp [ankeny_Q1] at h0
        nlinarith
      have hz_sq : z ^ 2 = 0 := by
        have : (n : ℤ) * z ^ 2 = 0 := by
          dsimp [ankeny_Q1] at h0
          nlinarith
        exact (mul_eq_zero.mp this).resolve_left hn_ne0
      have hx0' : x = 0 := sq_eq_zero_iff.mp hx_sq
      have hy0' : y = 0 := sq_eq_zero_iff.mp hy_sq
      have hz0' : z = 0 := sq_eq_zero_iff.mp hz_sq
      exact hxyz_ne (by simpa [hx0', hy0', hz0'])
    exact lt_of_le_of_ne' hQ1_nonneg hQ1_ne0

  -- `Q₁` is a positive multiple of `n*q`, but also `< 2*(n*q)`, hence `Q₁ = n*q`.
  have hQ1_eq : ankeny_Q1 n q x y z = (n * q : ℤ) := by
    rcases hdivQ with ⟨t, ht⟩
    have hm_pos : 0 < (n * q : ℤ) := by
      have hnq_pos_nat : 0 < n * q := Nat.mul_pos hn_pos hq_pos
      exact_mod_cast hnq_pos_nat
    have ht_pos : 0 < t := by
      have : 0 < (n * q : ℤ) * t := by simpa [ht] using hQ1_pos
      exact pos_of_mul_pos_right this (le_of_lt hm_pos)
    have ht_lt2 : t < 2 := by
      have hbound : ankeny_Q1 n q x y z < (n * q : ℤ) * 2 := by
        have : (2 * n * q : ℤ) = (n * q : ℤ) * 2 := by ring
        simpa [this] using hQ1_lt
      have hmul : (n * q : ℤ) * t < (n * q : ℤ) * 2 := by simpa [ht] using hbound
      exact lt_of_mul_lt_mul_left hmul hm_pos.le
    have ht_eq1 : t = 1 := by omega
    -- fold `t = 1` into the divisibility witness
    have ht' : ankeny_Q1 n q x y z = (n * q : ℤ) * 1 := by
      simpa [ht_eq1] using ht
    simpa [mul_one] using ht'

  refine ⟨x, y, z, ?_, hxyz_ne, ?_, ?_⟩
  · simpa using hQ1_eq
  · simpa using hxy
  · simpa using hybz

/-- Base `p`-divisibility step used in the Ankeny reduction.

If `p ≡ 3 (mod 4)` is a prime dividing `K = n - x^2` (and `p ∤ n`), then reducing the identity
\[
  y^2 + n z^2 = 2 q K
\]
modulo `p` forces `p ∣ y` and `p ∣ z`.

This is the mod-`p` “no nontrivial \(A^2 = -B^2\)” step via
`ZMod.mod_four_ne_three_of_sq_eq_neg_sq'`.
-/
lemma ankeny_p_dvd_yz_of_dvd_K
    {n q K p : ℕ} {x y z : ℤ}
    (hp : Nat.Prime p) (hp4 : p % 4 = 3)
    (hpK : p ∣ K) (hp_not_dvd_n : ¬ p ∣ n)
    (hK_eq : (K : ℤ) = (n : ℤ) - x ^ 2)
    (h_eqK : y ^ 2 + (n : ℤ) * z ^ 2 = 2 * (q : ℤ) * (K : ℤ)) :
    (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  have hpK_int : (p : ℤ) ∣ (K : ℤ) := by exact_mod_cast hpK
  have hk0 : ((K : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (K : ℤ) p).2 hpK_int
  have hk0' : (K : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff K p).2 hpK

  -- Cast the equation into `ZMod p` and use `K = 0` there.
  have hZ0 : ((y ^ 2 + (n : ℤ) * z ^ 2 : ℤ) : ZMod p) = 0 := by
    -- `h_eqK` already has the right shape; just cast and simplify the RHS.
    have := congrArg (fun t : ℤ => (t : ZMod p)) h_eqK
    simpa [hk0', mul_assoc, mul_left_comm, mul_comm] using this

  -- From `p ∣ K = n - x^2`, we have `n = x^2` in `ZMod p`.
  have hn_mod : (n : ZMod p) = (x : ZMod p) ^ 2 := by
    have hp_dvd_nmx : (p : ℤ) ∣ (n : ℤ) - x ^ 2 := by simpa [hK_eq] using hpK_int
    have hsub0 : (((n : ℤ) - x ^ 2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) - x ^ 2 : ℤ) p).2 hp_dvd_nmx
    have hn_cast : ((n : ℤ) : ZMod p) = (x ^ 2 : ZMod p) := by
      have : ((n : ℤ) : ZMod p) - (x ^ 2 : ZMod p) = 0 := by
        simpa [Int.cast_sub] using hsub0
      exact sub_eq_zero.mp this
    simpa [pow_two, mul_assoc] using hn_cast

  -- Turn `y^2 + n*z^2 = 0` into `y^2 = -(x*z)^2`.
  have hy2_eq : (y : ZMod p) ^ 2 = -((x : ZMod p) * (z : ZMod p)) ^ 2 := by
    have h0 : (y : ZMod p) ^ 2 + (n : ZMod p) * (z : ZMod p) ^ 2 = 0 := by
      simpa [pow_two, Int.cast_add, Int.cast_mul, Int.cast_natCast, add_assoc, add_comm,
        add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hZ0
    have hy : (y : ZMod p) ^ 2 = -((n : ZMod p) * (z : ZMod p) ^ 2) :=
      eq_neg_of_add_eq_zero_left h0
    have hy' : (y : ZMod p) ^ 2 = -(((x : ZMod p) ^ 2) * (z : ZMod p) ^ 2) := by
      simpa [hn_mod] using hy
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy'

  -- If `x*z ≠ 0`, we'd contradict `p % 4 = 3`.
  have hxz0 : (x : ZMod p) * (z : ZMod p) = 0 := by
    by_contra hxz_ne
    have : p % 4 ≠ 3 :=
      ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p)
        (x := (y : ZMod p)) (y := (x : ZMod p) * (z : ZMod p))
        hxz_ne (by
          -- rearrange `y^2 = -(xz)^2` into `y^2 = - (xz)^2`
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy2_eq)
    exact this (by simpa [hp4])

  -- Since `p ∤ n` and `n = x^2 (mod p)`, `x` is nonzero in `ZMod p`.
  have hx0 : (x : ZMod p) ≠ 0 := by
    intro hx
    have : (n : ZMod p) = 0 := by simpa [hn_mod, hx]
    exact hp_not_dvd_n ((ZMod.natCast_eq_zero_iff n p).1 this)

  have hz0 : (z : ZMod p) = 0 := by
    exact mul_eq_zero.mp hxz0 |>.resolve_left hx0

  have hy0 : (y : ZMod p) = 0 := by
    -- `y^2 = 0` (since `(x*z)=0`)
    have : (y : ZMod p) ^ 2 = 0 := by simpa [hxz0] using hy2_eq
    -- in a domain, `y*y=0` implies `y=0`
    have : (y : ZMod p) * (y : ZMod p) = 0 := by simpa [pow_two] using this
    exact (mul_eq_zero.mp this).elim id id

  -- Back to integer divisibility.
  have hp_dvd_y : (p : ℤ) ∣ y :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 (by simpa using hy0)
  have hp_dvd_z : (p : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 (by simpa using hz0)
  exact ⟨hp_dvd_y, hp_dvd_z⟩

/-!
### Q₁ variant of the mod-`p` divisibility kernel

For the `Q₁ = qx² + y² + nz²` route we get an identity
\[
  y^2 + n z^2 = q K
\]
instead of `2*q*K`. The core ZMod(`p`) argument is identical: if `p ∣ K` then the RHS
vanishes mod `p`, so we again obtain `y^2 = -(x*z)^2` in `ZMod p` and force `p ∣ y,z`
when `p % 4 = 3`.

This lemma is intentionally “small” (no valuation recursion): it should be reusable
inside the eventual Q₁ descent proof.
-/
/-- Variant of `ankeny_p_dvd_yz_of_dvd_K` that isolates the ZMod(`p`) core.

Assumptions:
- `p % 4 = 3` so `-1` is not a square mod `p`
- `n = x^2` in `ZMod p` and `p ∤ n` (so `x ≠ 0` in `ZMod p`)
- `y^2 + n z^2 = 0` in `ZMod p`

Conclusion: `p ∣ y` and `p ∣ z`.

This is the lemma we want to iterate when peeling off powers of `p` from `y` and `z`.
-/
lemma ankeny_p_dvd_yz_of_zmod_zero
    {n p : ℕ} {x y z : ℤ}
    (hp : Nat.Prime p) (hp4 : p % 4 = 3)
    (hp_not_dvd_n : ¬ p ∣ n)
    (hn_mod : (n : ZMod p) = (x : ZMod p) ^ 2)
    (hZ0 : ((y ^ 2 + (n : ℤ) * z ^ 2 : ℤ) : ZMod p) = 0) :
    (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  -- Turn `y^2 + n*z^2 = 0` into `y^2 = -(x*z)^2`.
  have hy2_eq : (y : ZMod p) ^ 2 = -((x : ZMod p) * (z : ZMod p)) ^ 2 := by
    have h0 : (y : ZMod p) ^ 2 + (n : ZMod p) * (z : ZMod p) ^ 2 = 0 := by
      simpa [pow_two, Int.cast_add, Int.cast_mul, Int.cast_natCast, add_assoc, add_comm,
        add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hZ0
    have hy : (y : ZMod p) ^ 2 = -((n : ZMod p) * (z : ZMod p) ^ 2) :=
      eq_neg_of_add_eq_zero_left h0
    have hy' : (y : ZMod p) ^ 2 = -(((x : ZMod p) ^ 2) * (z : ZMod p) ^ 2) := by
      simpa [hn_mod] using hy
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy'

  have hxz0 : (x : ZMod p) * (z : ZMod p) = 0 := by
    by_contra hxz_ne
    have : p % 4 ≠ 3 :=
      ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p)
        (x := (y : ZMod p)) (y := (x : ZMod p) * (z : ZMod p))
        hxz_ne (by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy2_eq)
    exact this (by simpa [hp4])

  have hx0 : (x : ZMod p) ≠ 0 := by
    intro hx
    have : (n : ZMod p) = 0 := by simpa [hn_mod, hx]
    exact hp_not_dvd_n ((ZMod.natCast_eq_zero_iff n p).1 this)

  have hz0 : (z : ZMod p) = 0 := by
    exact mul_eq_zero.mp hxz0 |>.resolve_left hx0

  have hy0 : (y : ZMod p) = 0 := by
    have : (y : ZMod p) ^ 2 = 0 := by simpa [hxz0] using hy2_eq
    have : (y : ZMod p) * (y : ZMod p) = 0 := by simpa [pow_two] using this
    exact (mul_eq_zero.mp this).elim id id

  have hp_dvd_y : (p : ℤ) ∣ y :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 (by simpa using hy0)
  have hp_dvd_z : (p : ℤ) ∣ z :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 (by simpa using hz0)
  exact ⟨hp_dvd_y, hp_dvd_z⟩

/-!
### Q₁ variant of the mod-`p` divisibility kernel

For the `Q₁ = qx² + y² + nz²` route we get an identity
\[
  y^2 + n z^2 = q K
\]
instead of `2*q*K`. The core ZMod(`p`) argument is identical: if `p ∣ K` then the RHS
vanishes mod `p`, so we again obtain `y^2 = -(x*z)^2` in `ZMod p` and force `p ∣ y,z`
when `p % 4 = 3`.

This lemma is intentionally “small” (no valuation recursion): it should be reusable
inside the eventual Q₁ descent proof.
-/
lemma ankeny_p_dvd_yz_of_dvd_K_q1
    {n q K p : ℕ} {x y z : ℤ}
    (hp : Nat.Prime p) (hp4 : p % 4 = 3)
    (hpK : p ∣ K) (hp_not_dvd_n : ¬ p ∣ n)
    (hK_eq : (K : ℤ) = (n : ℤ) - x ^ 2)
    (h_eqK : y ^ 2 + (n : ℤ) * z ^ 2 = (q : ℤ) * (K : ℤ)) :
    (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩

  have hpK_int : (p : ℤ) ∣ (K : ℤ) := by exact_mod_cast hpK
  have hk0' : (K : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff K p).2 hpK

  -- Cast the equation into `ZMod p` and use `K = 0` there.
  have hZ0 : ((y ^ 2 + (n : ℤ) * z ^ 2 : ℤ) : ZMod p) = 0 := by
    have := congrArg (fun t : ℤ => (t : ZMod p)) h_eqK
    -- RHS: `q*K = 0` in `ZMod p` because `K = 0`.
    simpa [hk0', mul_assoc, mul_left_comm, mul_comm] using this

  -- From `p ∣ K = n - x^2`, we have `n = x^2` in `ZMod p`.
  have hn_mod : (n : ZMod p) = (x : ZMod p) ^ 2 := by
    have hp_dvd_nmx : (p : ℤ) ∣ (n : ℤ) - x ^ 2 := by simpa [hK_eq] using hpK_int
    have hsub0 : (((n : ℤ) - x ^ 2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) - x ^ 2 : ℤ) p).2 hp_dvd_nmx
    have hn_cast : ((n : ℤ) : ZMod p) = (x ^ 2 : ZMod p) := by
      have : ((n : ℤ) : ZMod p) - (x ^ 2 : ZMod p) = 0 := by
        simpa [Int.cast_sub] using hsub0
      exact sub_eq_zero.mp this
    simpa [pow_two, mul_assoc] using hn_cast

  exact ankeny_p_dvd_yz_of_zmod_zero (n := n) (p := p) (x := x) (y := y) (z := z)
    hp hp4 hp_not_dvd_n hn_mod hZ0

/-- The remaining local kernel needed for `Nat.eq_sq_add_sq_iff` in the Ankeny reduction.

For a prime `p ≡ 3 (mod 4)` dividing `K = (n - x^2).natAbs`, show that the exponent of `p` in `K`
is even, i.e. `Even (padicValNat p K)`.

This is the bootstrapping step sketched in the comment inside `reduction_to_sum_three_squares`:
use `ankeny_p_dvd_yz_of_dvd_K` to force `p ∣ y` and `p ∣ z`, then descend on `K / p^2`.

This lemma is intentionally stated so its eventual proof can be developed (and tested) in isolation.
-/
lemma ankeny_even_padicValNat_of_mem_primeFactors
    {n q K p : ℕ} {x y z b : ℤ}
    (hn_odd : Odd n)
    (hq1 : q % 4 = 1)
    (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (hq_prime : Nat.Prime q)
    (hn_sq : Squarefree n)
    (hK_eq : (K : ℤ) = (n : ℤ) - x ^ 2)
    (h_eqK : y ^ 2 + (n : ℤ) * z ^ 2 = 2 * (q : ℤ) * (K : ℤ))
    (hxy : x ≡ y [ZMOD (n : ℤ)])
    (hybz : y ≡ b * z [ZMOD (2 * q : ℤ)])
    (hpK : p ∈ K.primeFactors)
    (hp4 : p % 4 = 3) :
    Even (padicValNat p K) := by
  -- Proof outline (implemented below):
  --
  -- - Use `hpK` to get `p ∣ K` and basic exclusions (`p ≠ 2`, `p ≠ q` from `hp4`, `hq1`).
  -- - Show `¬ p ∣ n` (otherwise `z^2 ≡ -1 (mod p)` from `hq_mod`, contradicting `p % 4 = 3`).
  -- - If `padicValNat p K` were odd, then `p^(2t+1) ∣ K` forces `p^(t+1) ∣ y,z` from the form
  --   `y^2 + n z^2 = 2*q*K`, hence `p^(2t+2) ∣ 2*q*K`.
  -- - Since `p ∤ 2*q`, this bumps the valuation of `K`, contradicting minimality of `2t+1`.
  classical
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpK
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_dvdK : p ∣ K := Nat.dvd_of_mem_primeFactors hpK

  -- Easy exclusions: `p ≠ 2` and `p ≠ q`.
  have hp_ne2 : p ≠ 2 := by
    intro h
    -- `2 % 4 = 2`, not `3`
    subst h
    simp at hp4
  have hp_ne_q : p ≠ q := by
    intro h
    subst h
    -- `q % 4 = 1` contradicts `p % 4 = 3`
    have : (p % 4) ≠ 3 := by simpa [hq1]
    exact this hp4

  -- First, rule out the case `p ∣ n` for primes `p ≡ 3 (mod 4)`.
  -- This is the case split that appears in Ankeny/Aluffi: if `p ∣ n`, one derives that `-1` is a square mod `p`.
  have hp_not_dvd_n : ¬ p ∣ n := by
    intro hp_dvd_n
    -- Sketch (Ankeny/Aluffi):
    --
    -- If `p ∣ n` and `p ∣ K = n - x^2`, then `x ≡ 0 (mod p)` and hence `x^2 ≡ 0 (mod p^2)`,
    -- so `K ≡ n (mod p^2)`.
    --
    -- From `y^2 + n z^2 = 2 q K` we first get `p ∣ y`, so `y^2 ≡ 0 (mod p^2)`.
    -- Reducing the equation mod `p^2` then yields `n z^2 ≡ 2 q K (mod p^2)`.
    -- Dividing by `p` and using `K/p ≡ n/p (mod p)` gives `z^2 ≡ 2 q (mod p)`.
    --
    -- Finally, the congruence `hq_mod : q = -(2)⁻¹ (mod n)` implies `2q ≡ -1 (mod p)`,
    -- so `z^2 ≡ -1 (mod p)`, contradicting `p % 4 = 3`.
    have hpK_int : (p : ℤ) ∣ (K : ℤ) := by exact_mod_cast hp_dvdK
    have hp_dvd_nmx : (p : ℤ) ∣ (n : ℤ) - x ^ 2 := by simpa [hK_eq] using hpK_int
    have hn_modp : ((n : ℤ) : ZMod p) = (x ^ 2 : ZMod p) := by
      have hsub0 : (((n : ℤ) - x ^ 2 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) - x ^ 2 : ℤ) p).2 hp_dvd_nmx
      have : ((n : ℤ) : ZMod p) - (x ^ 2 : ZMod p) = 0 := by
        simpa [Int.cast_sub] using hsub0
      exact sub_eq_zero.mp this

    have hx0_modp : (x : ZMod p) = 0 := by
      -- if `p ∣ n` then `n = 0` in `ZMod p`; hence `x^2 = 0`, hence `x=0`.
      have hn0p : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).2 hp_dvd_n
      have hx2 : (x ^ 2 : ZMod p) = 0 := by simpa [hn0p] using hn_modp.symm
      have : (x : ZMod p) * (x : ZMod p) = 0 := by simpa [pow_two] using hx2
      exact (mul_eq_zero.mp this).elim id id

    -- Since `x ≡ y (mod n)` and `p ∣ n`, we get `x ≡ y (mod p)` and hence `y = 0` in `ZMod p`.
    have hxy_p : x ≡ y [ZMOD (p : ℤ)] :=
      Int.ModEq.of_dvd (by exact_mod_cast hp_dvd_n) hxy
    have hy0_modp : (y : ZMod p) = 0 := by
      have : (y : ZMod p) = (x : ZMod p) := by
        -- cast the ModEq into `ZMod p`
        have := congrArg (fun t : ℤ => (t : ZMod p)) (Int.ModEq.symm hxy_p)
        simpa using this
      simpa [hx0_modp] using this

    -- Step 1: `p ∣ y`, hence `p^2 ∣ y^2`.
    have hp_dvd_y : (p : ℤ) ∣ y :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 (by simpa using hy0_modp)
    rcases hp_dvd_y with ⟨y1, rfl⟩

    -- Step 2: write `n = p * n1` with `p ∤ n1` (using squarefreeness).
    have hp_nat : Nat.Prime p := hp
    have hn_eq : n = p * (n / p) := by
      -- `p ∣ n`
      exact (Nat.mul_div_cancel' hp_dvd_n).symm
    set n1 : ℕ := n / p
    have hn1_ne0_modp : (n1 : ZMod p) ≠ 0 := by
      -- If `p ∣ n1`, then `p^2 ∣ n`, contradicting `Squarefree n`.
      intro hn1_0
      have hp_dvd_n1 : p ∣ n1 := (ZMod.natCast_eq_zero_iff n1 p).1 hn1_0
      have hp2_dvd_n : p * p ∣ n := by
        -- `n = p * n1` and `p ∣ n1`
        rcases hp_dvd_n1 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        -- `n = p * (p * t)`
        -- (use `hn_eq : n = p * n1` and `ht : n1 = p * t`)
        simpa [hn_eq, ht, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      -- squarefree contradiction
      have hsf := (Nat.squarefree_iff_prime_squarefree).1 hn_sq p hp_nat
      exact hsf hp2_dvd_n

    -- Step 3: use `Odd n`, so `2` is a unit in `ZMod n` and
    -- `hq_mod` really does mean `2*q = -1` in `ZMod n`. Then cast down to `ZMod p`.
    have h2u_n : IsUnit (2 : ZMod n) := GeometryOfNumbers.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
    have h2q_n : (2 : ZMod n) * (q : ZMod n) = (-1 : ZMod n) := by
      calc
        (2 : ZMod n) * (q : ZMod n) = (2 : ZMod n) * (-(2 : ZMod n)⁻¹) := by simpa [hq_mod]
        _ = -((2 : ZMod n) * (2 : ZMod n)⁻¹) := by ring
        _ = (-1 : ZMod n) := by
          have h : (2 : ZMod n) * (2 : ZMod n)⁻¹ = (1 : ZMod n) :=
            ZMod.mul_inv_of_unit (2 : ZMod n) h2u_n
          simpa [h]
    have h2q_eq_neg1 : (2 : ZMod p) * (q : ZMod p) = (-1 : ZMod p) := by
      -- Convert `2*q = -1` in `ZMod n` into an integer divisibility statement, then reduce mod `p`.
      have h2q_add1_n : (2 : ZMod n) * (q : ZMod n) + 1 = 0 := by
        simp [h2q_n]
      have hn_dvd : (n : ℤ) ∣ (2 * (q : ℤ) + 1) := by
        -- cast the `ZMod n` equality to `ℤ`-divisibility
        have hZ : ((2 * (q : ℤ) + 1 : ℤ) : ZMod n) = 0 := by
          -- `(2*q+1 : ZMod n) = (2:ZMod n)*(q:ZMod n)+1`
          simpa [Int.cast_add, Int.cast_mul, Int.cast_natCast, add_assoc, mul_assoc, two_mul] using h2q_add1_n
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (q : ℤ) + 1) n).1 hZ
      have hp_dvd_n_int : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hp_dvd_n
      have hp_dvd : (p : ℤ) ∣ (2 * (q : ℤ) + 1) := hp_dvd_n_int.trans hn_dvd
      have hZp : ((2 * (q : ℤ) + 1 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (q : ℤ) + 1) p).2 hp_dvd
      -- rearrange `(2*q+1)=0` into `2*q=-1`
      have : (2 : ZMod p) * (q : ZMod p) + 1 = 0 := by
        simpa [Int.cast_add, Int.cast_mul, Int.cast_natCast, add_assoc, mul_assoc, two_mul] using hZp
      exact eq_neg_of_add_eq_zero_left this

    -- Step 4: a clean “divide by `p` once” argument (no `p^2` arithmetic needed).
    --
    -- Write `x = p*x1` (since `x = 0` in `ZMod p`).
    have hp_dvd_x : (p : ℤ) ∣ x :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd x p).1 (by simpa using hx0_modp)
    rcases hp_dvd_x with ⟨x1, rfl⟩

    -- Define `K1 = K / p` in ℕ, with `n = p*n1` and `K = p*K1`.
    have hn_nat : n = p * n1 := by
      simpa [n1] using (Nat.mul_div_cancel' hp_dvd_n).symm
    set K1 : ℕ := K / p
    have hK_nat : K = p * K1 := by
      simpa [K1] using (Nat.mul_div_cancel' hp_dvdK).symm

    -- From `K = n - (p*x1)^2` and `n = p*n1`, show `K1 ≡ n1 (mod p)`.
    have hK1_mod : (K1 : ℤ) ≡ (n1 : ℤ) [ZMOD (p : ℤ)] := by
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hnZ : (n : ℤ) = (p : ℤ) * (n1 : ℤ) := by
        -- cast `hn_nat`
        exact_mod_cast hn_nat
      have hKZ : (K : ℤ) = (p : ℤ) * (K1 : ℤ) := by
        exact_mod_cast hK_nat
      -- Expand `x^2 = (p*x1)^2 = p^2*x1^2` and cancel the common factor `p`.
      have : (p : ℤ) * (K1 : ℤ) = (p : ℤ) * ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) := by
        -- Start from `hK_eq : (K:ℤ) = n - x^2`.
        -- Here `x` has been rewritten as `p*x1`.
        calc
          (p : ℤ) * (K1 : ℤ) = (K : ℤ) := by simpa [hKZ]
          _ = (n : ℤ) - ((p : ℤ) * x1) ^ 2 := by simpa [hK_eq]
          _ = (p : ℤ) * (n1 : ℤ) - (p : ℤ) ^ 2 * (x1 ^ 2) := by
                -- expand `((p*x1)^2)` into `p^2 * x1^2`
                simp [hnZ, pow_two, mul_assoc, mul_left_comm, mul_comm]
          _ = (p : ℤ) * ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) := by ring
      have hk1 : (K1 : ℤ) = (n1 : ℤ) - (p : ℤ) * (x1 ^ 2) :=
        (mul_left_cancel₀ hpz this)
      -- Hence `K1 - n1` is a multiple of `p`.
      refine (Int.modEq_iff_dvd).2 ?_
      refine ⟨x1 ^ 2, ?_⟩
      -- `n1 - (n1 - p*x1^2) = p*x1^2`
      have : (n1 : ℤ) - ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) = (p : ℤ) * (x1 ^ 2) := by
        ring
      simpa [hk1] using this

    -- Divide the main equation by `p` (exactly, because each term has a factor `p`).
    have h_div :
        (p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2) = 2 * (q : ℤ) * (K1 : ℤ) := by
      have hnZ : (n : ℤ) = (p : ℤ) * (n1 : ℤ) := by exact_mod_cast hn_nat
      have hKZ : (K : ℤ) = (p : ℤ) * (K1 : ℤ) := by exact_mod_cast hK_nat
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      -- Start from `h_eqK`, rewrite `n`/`K`, factor out `p`, then cancel.
      have h_eqK' :
          ((p : ℤ) * y1) ^ 2 + (p : ℤ) * (n1 : ℤ) * (z ^ 2) =
            2 * (q : ℤ) * ((p : ℤ) * (K1 : ℤ)) := by
        -- rewrite `n` and `K` in `h_eqK`
        simpa [hnZ, hKZ, mul_assoc, mul_left_comm, mul_comm] using h_eqK
      have hR : (p : ℤ) * (2 * (q : ℤ) * (K1 : ℤ)) = 2 * (q : ℤ) * ((p : ℤ) * (K1 : ℤ)) := by
        ring
      have hm :
          (p : ℤ) * ((p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2))
            = (p : ℤ) * (2 * (q : ℤ) * (K1 : ℤ)) := by
        calc
          (p : ℤ) * ((p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2))
              = ((p : ℤ) * y1) ^ 2 + (p : ℤ) * (n1 : ℤ) * (z ^ 2) := by ring
          _ = 2 * (q : ℤ) * ((p : ℤ) * (K1 : ℤ)) := h_eqK'
          _ = (p : ℤ) * (2 * (q : ℤ) * (K1 : ℤ)) := by
                simpa using hR.symm
      exact (mul_left_cancel₀ hpz hm)

    -- Reduce `h_div` modulo `p` and substitute `K1 ≡ n1 (mod p)` to obtain `z^2 ≡ 2q (mod p)`.
    have hz2_eq : (z : ZMod p) ^ 2 = (2 : ZMod p) * (q : ZMod p) := by
      -- First, modulo `p`: drop the `p * y1^2` term.
      have hmod1 : (n1 : ZMod p) * ((z : ZMod p) ^ 2) = (2 : ZMod p) * (q : ZMod p) * (K1 : ZMod p) := by
        have := congrArg (fun t : ℤ => (t : ZMod p)) h_div
        -- `p * y1^2` vanishes in `ZMod p`.
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
      -- Replace `K1` by `n1` using the congruence.
      have hK1_cast : (K1 : ZMod p) = (n1 : ZMod p) := by
        -- cast `Int.ModEq` into `ZMod p`
        have := congrArg (fun t : ℤ => (t : ZMod p)) hK1_mod.eq
        -- `Int.cast` agrees with `Nat.cast` here.
        simpa using this
      have hmod2 : (n1 : ZMod p) * ((z : ZMod p) ^ 2) = (2 : ZMod p) * (q : ZMod p) * (n1 : ZMod p) := by
        simpa [hK1_cast, mul_assoc, mul_left_comm, mul_comm] using hmod1
      -- Cancel `n1` (it is nonzero mod p).
      have hn1_ne0 : (n1 : ZMod p) ≠ 0 := hn1_ne0_modp
      -- Reassociate so both sides are `n1 * (...)`, then cancel.
      have hmod2' : (n1 : ZMod p) * ((z : ZMod p) ^ 2) = (n1 : ZMod p) * ((2 : ZMod p) * (q : ZMod p)) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmod2
      exact mul_left_cancel₀ hn1_ne0 hmod2'

    -- From `z^2 = 2q` and `2q = -1`, get `z^2 = -1`, contradict `p % 4 = 3`.
    have hz_sq_neg1 : (z : ZMod p) ^ 2 = (-1 : ZMod p) := by
      -- rewrite using `h2q_eq_neg1`
      -- (this is the only place we use `hz2_eq`)
      simpa [hz2_eq, h2q_eq_neg1]
    have hz_ne0 : (z : ZMod p) ≠ 0 := by
      intro hz0
      have : (0 : ZMod p) = (-1 : ZMod p) := by simpa [hz0] using hz_sq_neg1
      simpa using this
    have hp_ne : p % 4 ≠ 3 :=
      ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p) (x := (1 : ZMod p)) (y := (z : ZMod p))
        hz_ne0 (by
          -- `1^2 = -(z^2)` since `z^2 = -1`
          simp [hz_sq_neg1])
    exact hp_ne hp4

  -- Now we are in the main case `p ∤ n`. We can apply the mod-`p` contradiction lemma already proven.
  have hp_dvd_yz : (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z :=
    ankeny_p_dvd_yz_of_dvd_K (n := n) (q := q) (K := K) (p := p) (x := x) (y := y) (z := z)
      hp hp4 hp_dvdK hp_not_dvd_n hK_eq h_eqK

  -- Finish: show odd `padicValNat p K` is impossible.
  have hK_ne0 : K ≠ 0 := by
    intro hK0
    subst hK0
    simpa using hpK

  have hp_dvd_nmx : (p : ℤ) ∣ (n : ℤ) - x ^ 2 := by
    have : (p : ℤ) ∣ (K : ℤ) := by exact_mod_cast hp_dvdK
    simpa [hK_eq] using this

  -- Local kernel: if `p ∣ (n - x^2)` and `p ∣ (y^2 + n z^2)` with `p % 4 = 3` and `p ∤ n`,
  -- then `p ∣ y` and `p ∣ z`.
  have dvd_yz_of_dvd_form :
      ∀ {y z : ℤ},
        (p : ℤ) ∣ (n : ℤ) - x ^ 2 →
        (p : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) →
        (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
    intro y z hp_nmx hp_form
    haveI : Fact p.Prime := ⟨hp⟩
    have hn_modp : (n : ZMod p) = (x : ZMod p) ^ 2 := by
      have hsub0 : (((n : ℤ) - x ^ 2 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) - x ^ 2 : ℤ) p).2 hp_nmx
      have : ((n : ℤ) : ZMod p) - (x ^ 2 : ZMod p) = 0 := by
        simpa [Int.cast_sub] using hsub0
      simpa [pow_two, mul_assoc] using (sub_eq_zero.mp this)

    have hx0 : (x : ZMod p) ≠ 0 := by
      intro hx
      have : (n : ZMod p) = 0 := by simpa [hn_modp, hx]
      exact hp_not_dvd_n ((ZMod.natCast_eq_zero_iff n p).1 this)

    have hform0 : ((y ^ 2 + (n : ℤ) * z ^ 2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (y ^ 2 + (n : ℤ) * z ^ 2) p).2 hp_form

    have hy2_eq : (y : ZMod p) ^ 2 = -((x : ZMod p) * (z : ZMod p)) ^ 2 := by
      have h0 :
          (y : ZMod p) ^ 2 + (n : ZMod p) * (z : ZMod p) ^ 2 = 0 := by
        simpa [pow_two, Int.cast_add, Int.cast_mul, Int.cast_natCast, add_assoc, add_comm,
          add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hform0
      have hy : (y : ZMod p) ^ 2 = -((n : ZMod p) * (z : ZMod p) ^ 2) :=
        eq_neg_of_add_eq_zero_left h0
      have hy' : (y : ZMod p) ^ 2 = -(((x : ZMod p) ^ 2) * (z : ZMod p) ^ 2) := by
        simpa [hn_modp] using hy
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy'

    have hxz0 : (x : ZMod p) * (z : ZMod p) = 0 := by
      by_contra hxz_ne
      have : p % 4 ≠ 3 :=
        ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p)
          (x := (y : ZMod p)) (y := (x : ZMod p) * (z : ZMod p))
          hxz_ne (by
            simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy2_eq)
      exact this hp4

    have hz0 : (z : ZMod p) = 0 := (mul_eq_zero.mp hxz0).resolve_left hx0
    have hy0 : (y : ZMod p) = 0 := by
      have : (y : ZMod p) ^ 2 = 0 := by simpa [hxz0] using hy2_eq
      have : (y : ZMod p) * (y : ZMod p) = 0 := by simpa [pow_two] using this
      exact (mul_eq_zero.mp this).elim id id

    have hp_dvd_y : (p : ℤ) ∣ y :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 (by simpa using hy0)
    have hp_dvd_z : (p : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 (by simpa using hz0)
    exact ⟨hp_dvd_y, hp_dvd_z⟩

  -- Power version: if `p^(2t+1)` divides the form, then `p^(t+1)` divides `y` and `z`.
  have pow_dvd_yz_of_pow_dvd_form :
      ∀ (t : ℕ) {y z : ℤ},
        (p : ℤ) ^ (2 * t + 1) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) →
        (p : ℤ) ^ (t + 1) ∣ y ∧ (p : ℤ) ^ (t + 1) ∣ z := by
    intro t
    induction t with
    | zero =>
        intro y z hdiv
        have hp_form : (p : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by simpa using hdiv
        simpa using (dvd_yz_of_dvd_form (y := y) (z := z) hp_dvd_nmx hp_form)
    | succ t ih =>
        intro y z hdiv
        -- `p` divides the form, hence `p ∣ y` and `p ∣ z`.
        have hp_form : (p : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
          have hn0 : (2 * t + 3) ≠ 0 := by omega
          have hpdiv : (p : ℤ) ∣ (p : ℤ) ^ (2 * t + 3) := dvd_pow_self (p : ℤ) hn0
          exact hpdiv.trans hdiv
        rcases dvd_yz_of_dvd_form (y := y) (z := z) hp_dvd_nmx hp_form with ⟨hy, hz⟩
        rcases hy with ⟨y1, rfl⟩
        rcases hz with ⟨z1, rfl⟩
        have hfac :
            ((p : ℤ) * y1) ^ 2 + (n : ℤ) * ((p : ℤ) * z1) ^ 2
              = (p : ℤ) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          ring
        have hp_ne0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hp2_ne0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hp_ne0
        have hpow : (p : ℤ) ^ (2 * t + 3) = (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * t + 1) := by
          calc
            (p : ℤ) ^ (2 * t + 3) = (p : ℤ) ^ (2 + (2 * t + 1)) := by
              congr 1
              omega
            _ = (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * t + 1) := by
              simp [pow_add]
        have hdiv' :
            (p : ℤ) ^ (2 * t + 1) ∣ (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          have ht : 2 * (t + 1) + 1 = 2 * t + 3 := by omega
          have : (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * t + 1) ∣ (p : ℤ) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
            simpa [ht, hpow, hfac] using hdiv
          exact (Int.mul_dvd_mul_iff_left hp2_ne0).1 this
        have hyz := ih (y := y1) (z := z1) hdiv'
        refine ⟨?_, ?_⟩
        · simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
            (Int.mul_dvd_mul_left (p : ℤ) hyz.1)
        · simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
            (Int.mul_dvd_mul_left (p : ℤ) hyz.2)

  -- If `padicValNat p K` were odd, we can force one more factor of `p` into `K`, contradiction.
  by_contra h_even
  have hk_odd : Odd (padicValNat p K) := Nat.not_even_iff_odd.1 h_even
  rcases hk_odd with ⟨t, hk⟩

  have hpowK : p ^ (2 * t + 1) ∣ K := by
    -- Use the characterization: `p^k ∣ K ↔ k ≤ padicValNat p K` (for `K ≠ 0`).
    have : (2 * t + 1) ≤ padicValNat p K := by simpa [hk]
    exact (padicValNat_dvd_iff_le (p := p) (a := K) (n := 2 * t + 1) hK_ne0).2 this

  have hpow_form : (p : ℤ) ^ (2 * t + 1) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
    -- Start in `ℕ`, then cast to `ℤ`, and finally rewrite using `h_eqK`.
    have hnat : p ^ (2 * t + 1) ∣ 2 * q * K :=
      dvd_mul_of_dvd_right hpowK (2 * q)
    have hZ : (p ^ (2 * t + 1) : ℤ) ∣ (2 * q * K : ℤ) :=
      (Int.ofNat_dvd_natCast).2 hnat
    have hZ' : (p ^ (2 * t + 1) : ℤ) ∣ (2 * (q : ℤ) * (K : ℤ)) := by
      simpa [Nat.cast_mul, mul_assoc] using hZ
    -- rewrite `2*q*K` into the form of the left-hand side using `h_eqK`
    have : (p ^ (2 * t + 1) : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
      simpa [h_eqK, mul_assoc, mul_left_comm, mul_comm] using hZ'
    -- convert `(p ^ k : ℤ)` to `((p : ℤ) ^ k)`
    simpa [Nat.cast_pow] using this

  have hyz_pow : (p : ℤ) ^ (t + 1) ∣ y ∧ (p : ℤ) ^ (t + 1) ∣ z :=
    pow_dvd_yz_of_pow_dvd_form t (y := y) (z := z) hpow_form

  have hpow_form2 : (p : ℤ) ^ (2 * t + 2) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
    rcases hyz_pow.1 with ⟨y1, rfl⟩
    rcases hyz_pow.2 with ⟨z1, rfl⟩
    -- factor out `p^(2t+2)`
    refine ⟨y1 ^ 2 + (n : ℤ) * z1 ^ 2, ?_⟩
    have hp2 :
        ((p : ℤ) ^ (t + 1)) ^ 2 = (p : ℤ) ^ (2 * t + 2) := by
      have ht : (t + 1) * 2 = 2 * t + 2 := by omega
      -- rewrite `((p^(t+1))^2)` as `p^((t+1)*2)`
      rw [← pow_mul]
      simpa [ht]
    calc
      ((p : ℤ) ^ (t + 1) * y1) ^ 2 + (n : ℤ) * ((p : ℤ) ^ (t + 1) * z1) ^ 2
          = ((p : ℤ) ^ (t + 1)) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by ring
      _ = (p : ℤ) ^ (2 * t + 2) * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          simpa [hp2, mul_assoc, mul_left_comm, mul_comm]

  have hpow_nat2 : p ^ (2 * t + 2) ∣ 2 * q * K := by
    -- cast back to `ℕ` via `Int.ofNat_dvd_natCast`
    have hpowZ : ((p : ℤ) ^ (2 * t + 2)) ∣ (2 * (q : ℤ) * (K : ℤ)) := by
      simpa [h_eqK, mul_assoc, mul_left_comm, mul_comm] using hpow_form2
    have hpowZ' : (p ^ (2 * t + 2) : ℤ) ∣ (2 * (q : ℤ) * (K : ℤ)) := by
      simpa [Nat.cast_pow] using hpowZ
    have : (p ^ (2 * t + 2) : ℤ) ∣ (2 * q * K : ℤ) := by
      -- Avoid expanding casts aggressively (it can trigger simp recursion); associativity is enough.
      simpa [mul_assoc] using hpowZ'
    exact (Int.ofNat_dvd_natCast).1 this

  -- Show `p ∤ 2*q` (we use primality of `q` here).
  have hp_not_dvd_two : ¬ p ∣ 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hval : padicValNat p 2 = 0 := padicValNat_primes (p := p) (q := 2) hp_ne2
    intro hp2
    have : padicValNat p 2 ≠ 0 :=
      (dvd_iff_padicValNat_ne_zero (p := p) (n := 2) (hn0 := by decide)).1 hp2
    exact this hval

  have hp_not_dvd_q : ¬ p ∣ q := by
    haveI : Fact (Nat.Prime q) := ⟨hq_prime⟩
    have hval : padicValNat p q = 0 := padicValNat_primes (p := p) (q := q) hp_ne_q
    intro hpq
    have : padicValNat p q ≠ 0 :=
      (dvd_iff_padicValNat_ne_zero (p := p) (n := q) (hn0 := hq_prime.ne_zero)).1 hpq
    exact this hval

  have hp_not_dvd_2q : ¬ p ∣ 2 * q := by
    intro h
    have := (hp.dvd_mul).1 h
    cases this with
    | inl hp2 => exact hp_not_dvd_two hp2
    | inr hpq => exact hp_not_dvd_q hpq

  have hcop : Nat.Coprime (p ^ (2 * t + 2)) (2 * q) := by
    -- `Coprime p (2*q)` and then lift to powers.
    have : Nat.Coprime p (2 * q) := (hp.coprime_iff_not_dvd).2 hp_not_dvd_2q
    exact this.pow_left (2 * t + 2)

  have hpowK2 : p ^ (2 * t + 2) ∣ K :=
    (hcop.dvd_of_dvd_mul_left (by simpa [Nat.mul_assoc] using hpow_nat2))

  have hmax : ¬ p ^ (padicValNat p K + 1) ∣ K :=
    pow_succ_padicValNat_not_dvd (p := p) (n := K) hK_ne0
  have hcontra : p ^ (padicValNat p K + 1) ∣ K := by
    -- since `padicValNat p K = 2t+1` by `hk`
    have hexp : padicValNat p K + 1 = 2 * t + 2 := by
      calc
        padicValNat p K + 1 = (2 * t + 1) + 1 := by simpa [hk]
        _ = 2 * t + 2 := by omega
    -- rewrite the exponent to avoid simp recursion issues
    simpa [hexp] using hpowK2
  exact hmax hcontra

/-!
### Q₁ version: even valuation kernel

This is the Q₁ analogue of `ankeny_even_padicValNat_of_mem_primeFactors`.

In the Q₁ route we have an identity
\[
  y^2 + n z^2 = q \cdot K
\]
instead of `2*q*K`, and a slightly different congruence interface (`mod q` rather than `mod 2q`).

The intended structure is the same:
- for primes `p % 4 = 3` dividing `K`, force `p ∣ y,z` using `ankeny_p_dvd_yz_of_dvd_K_q1`,
- then show `p^2 ∣ K` and descend.
-/
lemma ankeny_even_padicValNat_of_mem_primeFactors_q1
    {n q K p : ℕ} {x y z b : ℤ}
    (hq1 : q % 4 = 1)
    (hq_prime : Nat.Prime q)
    (hq_mod : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)])
    (hn_sq : Squarefree n)
    (hK_eq : (K : ℤ) = (n : ℤ) - x ^ 2)
    (h_eqK : y ^ 2 + (n : ℤ) * z ^ 2 = (q : ℤ) * (K : ℤ))
    (hxy : x ≡ y [ZMOD (n : ℤ)])
    (hybz : y ≡ b * z [ZMOD (q : ℤ)])
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (q : ℤ)])
    (hpK : p ∈ K.primeFactors)
    (hp4 : p % 4 = 3) :
    Even (padicValNat p K) := by
  classical
  have hp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpK
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_dvdK : p ∣ K := Nat.dvd_of_mem_primeFactors hpK

  -- `p ≠ q` from mod-4 residues.
  have hp_ne_q : p ≠ q := by
    intro h
    subst h
    have : (p % 4) ≠ 3 := by simpa [hq1]
    exact this hp4

  -- Hence `p ∤ q` (since `q` is prime and its divisors are `1` or `q`).
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hpq
    have hdiv : p = 1 ∨ p = q := (Nat.dvd_prime hq_prime).1 hpq
    cases hdiv with
    | inl hp1 => exact hp.ne_one hp1
    | inr hpq_eq => exact hp_ne_q hpq_eq

  -- Key: `p ∤ n` for primes `p ≡ 3 (mod 4)` dividing `K`.
  -- (This is the Q₁ analogue of the `p ∣ n` contradiction in the `2q` route; here we use `q ≡ -1 (mod n)`.)
  have hp_not_dvd_n : ¬ p ∣ n := by
    intro hp_dvd_n
    have hpK_int : (p : ℤ) ∣ (K : ℤ) := by exact_mod_cast hp_dvdK
    have hp_dvd_nmx : (p : ℤ) ∣ (n : ℤ) - x ^ 2 := by simpa [hK_eq] using hpK_int
    have hn_modp : ((n : ℤ) : ZMod p) = (x ^ 2 : ZMod p) := by
      have hsub0 : (((n : ℤ) - x ^ 2 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) - x ^ 2 : ℤ) p).2 hp_dvd_nmx
      have : ((n : ℤ) : ZMod p) - (x ^ 2 : ZMod p) = 0 := by
        simpa [Int.cast_sub] using hsub0
      exact sub_eq_zero.mp this

    have hx0_modp : (x : ZMod p) = 0 := by
      have hn0p : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).2 hp_dvd_n
      have hx2 : (x ^ 2 : ZMod p) = 0 := by simpa [hn0p] using hn_modp.symm
      have : (x : ZMod p) * (x : ZMod p) = 0 := by simpa [pow_two] using hx2
      exact (mul_eq_zero.mp this).elim id id

    -- `x ≡ y (mod n)` and `p ∣ n` ⇒ `x ≡ y (mod p)` ⇒ `y = 0` in `ZMod p`.
    have hxy_p : x ≡ y [ZMOD (p : ℤ)] := Int.ModEq.of_dvd (by exact_mod_cast hp_dvd_n) hxy
    have hy0_modp : (y : ZMod p) = 0 := by
      have : (y : ZMod p) = (x : ZMod p) := by
        have := congrArg (fun t : ℤ => (t : ZMod p)) (Int.ModEq.symm hxy_p)
        simpa using this
      simpa [hx0_modp] using this

    have hp_dvd_y : (p : ℤ) ∣ y :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 (by simpa using hy0_modp)
    rcases hp_dvd_y with ⟨y1, hy1⟩
    -- Also `p ∣ x` in ℤ.
    have hp_dvd_x : (p : ℤ) ∣ x :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd x p).1 (by simpa using hx0_modp)
    rcases hp_dvd_x with ⟨x1, hx1⟩

    -- Squarefree: write `n = p * n1` with `p ∤ n1`.
    have hn_eq : n = p * (n / p) := (Nat.mul_div_cancel' hp_dvd_n).symm
    set n1 : ℕ := n / p
    have hn1_ne0_modp : (n1 : ZMod p) ≠ 0 := by
      intro hn1_0
      have hp_dvd_n1 : p ∣ n1 := (ZMod.natCast_eq_zero_iff n1 p).1 hn1_0
      have hp2_dvd_n : p * p ∣ n := by
        rcases hp_dvd_n1 with ⟨t, ht⟩
        refine ⟨t, ?_⟩
        simpa [hn_eq, ht, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      have hsf := (Nat.squarefree_iff_prime_squarefree).1 hn_sq p hp
      exact hsf hp2_dvd_n

    have hn_nat : n = p * n1 := by simpa [n1] using (Nat.mul_div_cancel' hp_dvd_n).symm
    -- Define `K1 = K / p` in ℕ.
    set K1 : ℕ := K / p
    have hK_nat : K = p * K1 := by simpa [K1] using (Nat.mul_div_cancel' hp_dvdK).symm

    -- From `K = n - x^2` and `x = p*x1`, show `K1 ≡ n1 (mod p)`.
    have hK1_mod : (K1 : ℤ) ≡ (n1 : ℤ) [ZMOD (p : ℤ)] := by
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hnZ : (n : ℤ) = (p : ℤ) * (n1 : ℤ) := by exact_mod_cast hn_nat
      have hKZ : (K : ℤ) = (p : ℤ) * (K1 : ℤ) := by exact_mod_cast hK_nat
      have : (p : ℤ) * (K1 : ℤ) = (p : ℤ) * ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) := by
        calc
          (p : ℤ) * (K1 : ℤ) = (K : ℤ) := by simpa [hKZ]
          _ = (n : ℤ) - x ^ 2 := hK_eq
          _ = (p : ℤ) * (n1 : ℤ) - ((p : ℤ) * x1) ^ 2 := by simpa [hnZ, hx1]
          _ = (p : ℤ) * ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) := by
                simp [pow_two, mul_assoc, mul_left_comm, mul_comm]; ring
      have hk1 : (K1 : ℤ) = (n1 : ℤ) - (p : ℤ) * (x1 ^ 2) := (mul_left_cancel₀ hpz this)
      refine (Int.modEq_iff_dvd).2 ?_
      refine ⟨x1 ^ 2, ?_⟩
      have : (n1 : ℤ) - ((n1 : ℤ) - (p : ℤ) * (x1 ^ 2)) = (p : ℤ) * (x1 ^ 2) := by ring
      simpa [hk1] using this

    -- Divide the main equation by `p`.
    have h_div :
        (p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2) = (q : ℤ) * (K1 : ℤ) := by
      have hnZ : (n : ℤ) = (p : ℤ) * (n1 : ℤ) := by exact_mod_cast hn_nat
      have hKZ : (K : ℤ) = (p : ℤ) * (K1 : ℤ) := by exact_mod_cast hK_nat
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have h_eqK' :
          ((p : ℤ) * y1) ^ 2 + (p : ℤ) * (n1 : ℤ) * (z ^ 2) =
            (q : ℤ) * ((p : ℤ) * (K1 : ℤ)) := by
        simpa [hnZ, hKZ, hy1, mul_assoc, mul_left_comm, mul_comm] using h_eqK
      have hm :
          (p : ℤ) * ((p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2))
            = (p : ℤ) * ((q : ℤ) * (K1 : ℤ)) := by
        calc
          (p : ℤ) * ((p : ℤ) * (y1 ^ 2) + (n1 : ℤ) * (z ^ 2))
              = ((p : ℤ) * y1) ^ 2 + (p : ℤ) * (n1 : ℤ) * (z ^ 2) := by ring
          _ = (q : ℤ) * ((p : ℤ) * (K1 : ℤ)) := h_eqK'
          _ = (p : ℤ) * ((q : ℤ) * (K1 : ℤ)) := by ring
      exact (mul_left_cancel₀ hpz hm)

    -- Reduce modulo `p`, substitute `K1 ≡ n1`, and conclude `z^2 ≡ q (mod p)`.
    have hz2_eq : (z : ZMod p) ^ 2 = (q : ZMod p) := by
      have hmod1 : (n1 : ZMod p) * ((z : ZMod p) ^ 2) = (q : ZMod p) * (K1 : ZMod p) := by
        have := congrArg (fun t : ℤ => (t : ZMod p)) h_div
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using this
      have hK1_cast : (K1 : ZMod p) = (n1 : ZMod p) := by
        have := congrArg (fun t : ℤ => (t : ZMod p)) hK1_mod.eq
        simpa using this
      have hmod2 : (n1 : ZMod p) * ((z : ZMod p) ^ 2) = (n1 : ZMod p) * (q : ZMod p) := by
        simpa [hK1_cast, mul_assoc, mul_left_comm, mul_comm] using hmod1
      exact mul_left_cancel₀ hn1_ne0_modp hmod2

    -- From `q ≡ -1 (mod n)` and `p ∣ n`, get `q ≡ -1 (mod p)` hence `z^2 = -1`, contradict `p % 4 = 3`.
    have hq_mod_p : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (p : ℤ)] :=
      Int.ModEq.of_dvd (by exact_mod_cast hp_dvd_n) hq_mod
    have hq0 : (q : ZMod p) = (-1 : ZMod p) := by
      have := congrArg (fun t : ℤ => (t : ZMod p)) hq_mod_p.eq
      simpa using this
    have hz_sq_neg1 : (z : ZMod p) ^ 2 = (-1 : ZMod p) := by simpa [hq0] using hz2_eq
    have : p % 4 ≠ 3 :=
      ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p)
        (x := (z : ZMod p)) (y := (1 : ZMod p))
        (by simp) (by simpa [pow_two] using hz_sq_neg1)
    exact this (by simpa [hp4])

  -- Force `p ∣ y` and `p ∣ z` (Q₁ mod-`p` kernel).
  have hp_dvd_yz : (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z :=
    ankeny_p_dvd_yz_of_dvd_K_q1 (n := n) (q := q) (K := K) (p := p) (x := x) (y := y) (z := z)
      hp hp4 hp_dvdK hp_not_dvd_n hK_eq h_eqK
  have hp_dvd_y : (p : ℤ) ∣ y := hp_dvd_yz.1
  have hp_dvd_z : (p : ℤ) ∣ z := hp_dvd_yz.2

  -- Show `p^2 ∣ K` (the key cancellation step used by the eventual recursion).
  have hp2_dvd_K : p * p ∣ K := by
    rcases hp_dvd_y with ⟨y1, rfl⟩
    rcases hp_dvd_z with ⟨z1, rfl⟩
    -- `p^2 ∣ y^2 + n z^2 = q*K`.
    have hp2_dvd_qK : p ^ 2 ∣ q * K := by
      have hp2Z : ((p : ℤ) ^ 2) ∣ (q : ℤ) * (K : ℤ) := by
        refine ⟨(y1 ^ 2 + (n : ℤ) * z1 ^ 2), ?_⟩
        -- expand and match `h_eqK`
        have : ((p : ℤ) * y1) ^ 2 + (n : ℤ) * ((p : ℤ) * z1) ^ 2 =
            (p : ℤ) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          ring
        calc
          (q : ℤ) * (K : ℤ)
              = ((p : ℤ) * y1) ^ 2 + (n : ℤ) * ((p : ℤ) * z1) ^ 2 := by
                    simpa [mul_assoc, mul_left_comm, mul_comm] using h_eqK.symm
          _ = (p : ℤ) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := this
      -- cast back to `ℕ`
      have hp2Z' : (p ^ 2 : ℤ) ∣ (q * K : ℤ) := by simpa [Nat.cast_pow] using hp2Z
      exact (Int.ofNat_dvd_natCast).1 hp2Z'
    have hcop : Nat.Coprime (p ^ 2) q := by
      have : Nat.Coprime p q := (hp.coprime_iff_not_dvd).2 hp_not_dvd_q
      exact this.pow_left 2
    have hp2_dvd_K' : p ^ 2 ∣ K :=
      hcop.dvd_of_dvd_mul_left (by simpa [Nat.mul_assoc] using hp2_dvd_qK)
    simpa [pow_two] using hp2_dvd_K'

  -- Finish: show odd `padicValNat p K` is impossible (same shape as the `2q` route).
  have hK_ne0 : K ≠ 0 := by
    intro hK0
    subst hK0
    simpa using hpK

  have hp_dvd_nmx : (p : ℤ) ∣ (n : ℤ) - x ^ 2 := by
    have : (p : ℤ) ∣ (K : ℤ) := by exact_mod_cast hp_dvdK
    simpa [hK_eq] using this

  -- Local kernel (same as in the `2q` lemma): once we have `p ∣ (n - x^2)` and `p ∣ (y^2 + n z^2)`
  -- with `p % 4 = 3` and `p ∤ n`, we can force `p ∣ y` and `p ∣ z`.
  have dvd_yz_of_dvd_form :
      ∀ {y z : ℤ},
        (p : ℤ) ∣ (n : ℤ) - x ^ 2 →
        (p : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) →
        (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
    intro y z hp_nmx hp_form
    haveI : Fact p.Prime := ⟨hp⟩
    have hn_modp : (n : ZMod p) = (x : ZMod p) ^ 2 := by
      have hsub0 : (((n : ℤ) - x ^ 2 : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) - x ^ 2 : ℤ) p).2 hp_nmx
      have : ((n : ℤ) : ZMod p) - (x ^ 2 : ZMod p) = 0 := by
        simpa [Int.cast_sub] using hsub0
      simpa [pow_two, mul_assoc] using (sub_eq_zero.mp this)

    have hx0 : (x : ZMod p) ≠ 0 := by
      intro hx
      have : (n : ZMod p) = 0 := by simpa [hn_modp, hx]
      exact hp_not_dvd_n ((ZMod.natCast_eq_zero_iff n p).1 this)

    have hform0 : ((y ^ 2 + (n : ℤ) * z ^ 2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (y ^ 2 + (n : ℤ) * z ^ 2) p).2 hp_form

    have hy2_eq : (y : ZMod p) ^ 2 = -((x : ZMod p) * (z : ZMod p)) ^ 2 := by
      have h0 :
          (y : ZMod p) ^ 2 + (n : ZMod p) * (z : ZMod p) ^ 2 = 0 := by
        simpa [pow_two, Int.cast_add, Int.cast_mul, Int.cast_natCast, add_assoc, add_comm,
          add_left_comm, mul_assoc, mul_comm, mul_left_comm] using hform0
      have hy : (y : ZMod p) ^ 2 = -((n : ZMod p) * (z : ZMod p) ^ 2) :=
        eq_neg_of_add_eq_zero_left h0
      have hy' : (y : ZMod p) ^ 2 = -(((x : ZMod p) ^ 2) * (z : ZMod p) ^ 2) := by
        simpa [hn_modp] using hy
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy'

    have hxz0 : (x : ZMod p) * (z : ZMod p) = 0 := by
      by_contra hxz_ne
      have : p % 4 ≠ 3 :=
        ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p)
          (x := (y : ZMod p)) (y := (x : ZMod p) * (z : ZMod p))
          hxz_ne (by
            simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy2_eq)
      exact this hp4

    have hz0 : (z : ZMod p) = 0 := (mul_eq_zero.mp hxz0).resolve_left hx0
    have hy0 : (y : ZMod p) = 0 := by
      have : (y : ZMod p) ^ 2 = 0 := by simpa [hxz0] using hy2_eq
      have : (y : ZMod p) * (y : ZMod p) = 0 := by simpa [pow_two] using this
      exact (mul_eq_zero.mp this).elim id id

    have hp_dvd_y : (p : ℤ) ∣ y :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd y p).1 (by simpa using hy0)
    have hp_dvd_z : (p : ℤ) ∣ z :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd z p).1 (by simpa using hz0)
    exact ⟨hp_dvd_y, hp_dvd_z⟩

  -- Power version: if `p^(2t+1)` divides the form, then `p^(t+1)` divides `y` and `z`.
  have pow_dvd_yz_of_pow_dvd_form :
      ∀ (t : ℕ) {y z : ℤ},
        (p : ℤ) ^ (2 * t + 1) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) →
        (p : ℤ) ^ (t + 1) ∣ y ∧ (p : ℤ) ^ (t + 1) ∣ z := by
    intro t
    induction t with
    | zero =>
        intro y z hdiv
        have hp_form : (p : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by simpa using hdiv
        simpa using (dvd_yz_of_dvd_form (y := y) (z := z) hp_dvd_nmx hp_form)
    | succ t ih =>
        intro y z hdiv
        have hp_form : (p : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
          have hn0 : (2 * t + 3) ≠ 0 := by omega
          have hpdiv : (p : ℤ) ∣ (p : ℤ) ^ (2 * t + 3) := dvd_pow_self (p : ℤ) hn0
          exact hpdiv.trans hdiv
        rcases dvd_yz_of_dvd_form (y := y) (z := z) hp_dvd_nmx hp_form with ⟨hy, hz⟩
        rcases hy with ⟨y1, rfl⟩
        rcases hz with ⟨z1, rfl⟩
        have hfac :
            ((p : ℤ) * y1) ^ 2 + (n : ℤ) * ((p : ℤ) * z1) ^ 2
              = (p : ℤ) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          ring
        have hp_ne0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
        have hp2_ne0 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hp_ne0
        have hpow : (p : ℤ) ^ (2 * t + 3) = (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * t + 1) := by
          calc
            (p : ℤ) ^ (2 * t + 3) = (p : ℤ) ^ (2 + (2 * t + 1)) := by
              congr 1
              omega
            _ = (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * t + 1) := by
              simp [pow_add]
        have hdiv' :
            (p : ℤ) ^ (2 * t + 1) ∣ (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          have ht : 2 * (t + 1) + 1 = 2 * t + 3 := by omega
          have : (p : ℤ) ^ 2 * (p : ℤ) ^ (2 * t + 1) ∣ (p : ℤ) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
            simpa [ht, hpow, hfac] using hdiv
          exact (Int.mul_dvd_mul_iff_left hp2_ne0).1 this
        have hyz := ih (y := y1) (z := z1) hdiv'
        refine ⟨?_, ?_⟩
        · simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
            (Int.mul_dvd_mul_left (p : ℤ) hyz.1)
        · simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
            (Int.mul_dvd_mul_left (p : ℤ) hyz.2)

  -- If `padicValNat p K` were odd, force one more factor of `p` into `K`, contradiction.
  by_contra h_even
  have hk_odd : Odd (padicValNat p K) := Nat.not_even_iff_odd.1 h_even
  rcases hk_odd with ⟨t, hk⟩

  have hpowK : p ^ (2 * t + 1) ∣ K := by
    have : (2 * t + 1) ≤ padicValNat p K := by simpa [hk]
    exact (padicValNat_dvd_iff_le (p := p) (a := K) (n := 2 * t + 1) hK_ne0).2 this

  have hpow_form : (p : ℤ) ^ (2 * t + 1) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
    have hnat : p ^ (2 * t + 1) ∣ q * K :=
      dvd_mul_of_dvd_right hpowK q
    have hZ : (p ^ (2 * t + 1) : ℤ) ∣ (q * K : ℤ) :=
      (Int.ofNat_dvd_natCast).2 hnat
    have hZ' : (p ^ (2 * t + 1) : ℤ) ∣ ((q : ℤ) * (K : ℤ)) := by
      simpa [Nat.cast_mul, mul_assoc] using hZ
    have : (p ^ (2 * t + 1) : ℤ) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
      simpa [h_eqK, mul_assoc, mul_left_comm, mul_comm] using hZ'
    simpa [Nat.cast_pow] using this

  have hyz_pow : (p : ℤ) ^ (t + 1) ∣ y ∧ (p : ℤ) ^ (t + 1) ∣ z :=
    pow_dvd_yz_of_pow_dvd_form t (y := y) (z := z) hpow_form

  have hpow_form2 : (p : ℤ) ^ (2 * t + 2) ∣ (y ^ 2 + (n : ℤ) * z ^ 2) := by
    rcases hyz_pow.1 with ⟨y1, rfl⟩
    rcases hyz_pow.2 with ⟨z1, rfl⟩
    refine ⟨y1 ^ 2 + (n : ℤ) * z1 ^ 2, ?_⟩
    have hp2 :
        ((p : ℤ) ^ (t + 1)) ^ 2 = (p : ℤ) ^ (2 * t + 2) := by
      have ht : (t + 1) * 2 = 2 * t + 2 := by omega
      rw [← pow_mul]
      simpa [ht]
    calc
      ((p : ℤ) ^ (t + 1) * y1) ^ 2 + (n : ℤ) * ((p : ℤ) ^ (t + 1) * z1) ^ 2
          = ((p : ℤ) ^ (t + 1)) ^ 2 * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by ring
      _ = (p : ℤ) ^ (2 * t + 2) * (y1 ^ 2 + (n : ℤ) * z1 ^ 2) := by
          simpa [hp2, mul_assoc, mul_left_comm, mul_comm]

  have hpow_nat2 : p ^ (2 * t + 2) ∣ q * K := by
    have hpowZ : ((p : ℤ) ^ (2 * t + 2)) ∣ ((q : ℤ) * (K : ℤ)) := by
      simpa [h_eqK, mul_assoc, mul_left_comm, mul_comm] using hpow_form2
    have hpowZ' : (p ^ (2 * t + 2) : ℤ) ∣ ((q : ℤ) * (K : ℤ)) := by
      simpa [Nat.cast_pow] using hpowZ
    have : (p ^ (2 * t + 2) : ℤ) ∣ (q * K : ℤ) := by
      simpa [Nat.cast_mul, mul_assoc] using hpowZ'
    exact (Int.ofNat_dvd_natCast).1 this

  have hcop : Nat.Coprime (p ^ (2 * t + 2)) q := by
    have : Nat.Coprime p q := (hp.coprime_iff_not_dvd).2 hp_not_dvd_q
    exact this.pow_left (2 * t + 2)

  have hpowK2 : p ^ (2 * t + 2) ∣ K :=
    (hcop.dvd_of_dvd_mul_left (by simpa [Nat.mul_assoc] using hpow_nat2))

  have hmax : ¬ p ^ (padicValNat p K + 1) ∣ K :=
    pow_succ_padicValNat_not_dvd (p := p) (n := K) hK_ne0
  have hcontra : p ^ (padicValNat p K + 1) ∣ K := by
    have hexp : padicValNat p K + 1 = 2 * t + 2 := by
      calc
        padicValNat p K + 1 = (2 * t + 1) + 1 := by simpa [hk]
        _ = 2 * t + 2 := by omega
    simpa [hexp] using hpowK2
  exact hmax hcontra

/-- Reduction of `2qx² + y² + nz² = 2nq` to `n = x² + u² + v²`.

This is the “arithmetic back half” of the Ankeny-style proof: once we have one special quadratic-form
representation, we need to manufacture a *sum of two squares* witness.

Research note (Ankeny 1957, Proc. AMS 8(2), pp. 316–319):
the classical writeup proves (for squarefree `m ≡ 3 (mod 8)`) an identity of the form
\[
  m = R^2 + 2 v
\]
and then shows that every odd prime dividing `v` to an odd power is \( \equiv 1 \pmod 4 \),
so `2*v` is a sum of two squares; hence `m` is a sum of three squares.

Our current Lean development is arranged slightly differently (we work with `K := (n - x^2).natAbs`),
but the *intended invariant* is the same: use `Nat.eq_sq_add_sq_iff` (mathlib’s “sum of two squares”
criterion) to prove `K` is a sum of two squares by ruling out primes \(p \equiv 3 \pmod 4\) appearing
to odd exponent.
-/
lemma reduction_to_sum_three_squares (n q : ℕ) (x y z : ℤ)
    (h_ankeny : 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q)
    (hq_prime : Nat.Prime q) (_hq1 : q % 4 = 1) (_hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (hn_odd : Odd n) (hn_sq : Squarefree n)
    (b : ℤ)
    (hxy : x ≡ y [ZMOD (n : ℤ)]) (hybz : y ≡ b * z [ZMOD (2 * q : ℤ)]) :
    ∃ u v : ℤ, n = x^2 + u^2 + v^2 := by
  have h_eq : y^2 + n * z^2 = 2 * q * (n - x^2) := by
    calc y^2 + n * z^2 = (2 * q * x^2 + y^2 + n * z^2) - 2 * q * x^2 := by ring
      _ = 2 * n * q - 2 * q * x^2 := by rw [h_ankeny]
      _ = 2 * q * (n - x^2) := by ring

  -- Show n - x^2 >= 0
  have h_diff_nonneg : 0 ≤ n - x^2 := by
    have h_rhs : 0 ≤ y^2 + n * z^2 := by
      apply add_nonneg (sq_nonneg y)
      apply mul_nonneg (Int.natCast_nonneg n) (sq_nonneg z)
    rw [h_eq] at h_rhs
    have h2q : 0 < (2 * q : ℤ) := by
      have hq_pos : 0 < q := hq_prime.pos
      norm_cast; linarith
    exact nonneg_of_mul_nonneg_right h_rhs h2q

  let K := (n - x^2).natAbs
  have hK_eq : (K : ℤ) = n - x^2 := Int.natAbs_of_nonneg h_diff_nonneg

  -- At this point we want to show `K` is a sum of two squares; then `n = x^2 + K`.
  --
  by_cases hK0 : K = 0
  · -- Then `n = x^2`, hence trivially a sum of three squares.
    refine ⟨0, 0, ?_⟩
    -- From `K = 0` and `hK_eq : (K:ℤ)=n-x^2`.
    have : (n : ℤ) = x ^ 2 := by
      -- `n - x^2 = 0`
      have : (n : ℤ) - x ^ 2 = 0 := by
        simpa [hK0] using hK_eq.symm
      linarith
    simpa [this]
  ·
    -- Nontrivial case: `K ≠ 0`. We now follow the *intended* (Ankeny-style) structure:
    -- use `Nat.eq_sq_add_sq_iff` to prove `K` is a sum of two squares by ruling out primes
    -- `≡ 3 (mod 4)` appearing to odd exponent in `K`.
    --
    -- The main local ingredient (for a fixed prime `p ≡ 3 (mod 4)` dividing `K`) is that,
    -- reducing the identity `y^2 + n*z^2 = 2*q*K` modulo `p` and using `n ≡ x^2 (mod p)`
    -- yields an equation of the form `A^2 = -B^2` in `ZMod p`. Since `p % 4 = 3`,
    -- `ZMod.mod_four_ne_three_of_sq_eq_neg_sq'` forces `B = 0`, hence `A = 0`,
    -- which can be bootstrapped to show `p^2 ∣ K` and thus `Even (padicValNat p K)`.
    have hK_sq_add_sq : ∃ u v : ℕ, K = u ^ 2 + v ^ 2 := by
      -- Number theory kernel:
      -- use `Nat.eq_sq_add_sq_iff` (Mathlib.NumberTheory.SumTwoSquares), which reduces the goal to
      -- a parity statement about primes `p ≡ 3 (mod 4)` dividing `K`.
      refine (Nat.eq_sq_add_sq_iff (n := K)).2 ?_
      intro p hpK hp4
      simpa using
        ankeny_even_padicValNat_of_mem_primeFactors (n := n) (q := q) (K := K) (p := p)
          (x := x) (y := y) (z := z) (b := b)
          hn_odd _hq1 _hq_mod hq_prime hn_sq hK_eq (by
            -- Rewrite into the form expected by `ankeny_even_padicValNat_of_mem_primeFactors`.
            -- `h_eq : y^2 + n*z^2 = 2*q*(n - x^2)`
            simpa [hK_eq, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t : ℤ => t) h_eq)
          hxy hybz hpK hp4

    obtain ⟨uN, vN, hK⟩ := hK_sq_add_sq
    refine ⟨(uN : ℤ), (vN : ℤ), ?_⟩
    have hKz : (K : ℤ) = (uN ^ 2 + vN ^ 2 : ℤ) := by
      exact_mod_cast hK
    -- `n = x^2 + K = x^2 + u^2 + v^2`.
    have hn_int : (n : ℤ) = x ^ 2 + (K : ℤ) := by
      -- `K = n - x^2`
      linarith [hK_eq]
    calc
      (n : ℤ) = x ^ 2 + (K : ℤ) := hn_int
      _ = x ^ 2 + (uN ^ 2 + vN ^ 2 : ℤ) := by simpa [hKz]
      _ = x ^ 2 + (uN : ℤ) ^ 2 + (vN : ℤ) ^ 2 := by
        -- normalize casts/powers
        simp [pow_two, add_assoc]

/-!
### Q₁ reduction: `q*x^2 + y^2 + n*z^2 = n*q` ⇒ `n = x^2 + u^2 + v^2`

This mirrors `reduction_to_sum_three_squares`, but the “special representation” comes from the Q₁
Minkowski route, and the divisibility identity is `y^2 + n*z^2 = q*(n - x^2)`.

We keep the same invariant \(K := (n - x^2).natAbs\) and the same endpoint: prove `K` is a sum of
two squares via `Nat.eq_sq_add_sq_iff`.
-/
lemma reduction_to_sum_three_squares_q1 (n q : ℕ) (x y z : ℤ)
    (h_ankeny : (q : ℤ) * x^2 + y^2 + (n : ℤ) * z ^ 2 = (n * q : ℤ))
    (hq_prime : Nat.Prime q) (hq1 : q % 4 = 1)
    (hq_mod : (q : ℤ) ≡ (-1 : ℤ) [ZMOD (n : ℤ)])
    (hn_sq : Squarefree n)
    (b : ℤ)
    (hxy : x ≡ y [ZMOD (n : ℤ)]) (hybz : y ≡ b * z [ZMOD (q : ℤ)])
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (q : ℤ)]) :
    ∃ u v : ℤ, (n : ℤ) = x^2 + u^2 + v^2 := by
  have h_eq : y^2 + (n : ℤ) * z^2 = (q : ℤ) * ((n : ℤ) - x^2) := by
    calc
      y^2 + (n : ℤ) * z^2
          = ((q : ℤ) * x^2 + y^2 + (n : ℤ) * z^2) - (q : ℤ) * x^2 := by ring
      _ = (n * q : ℤ) - (q : ℤ) * x^2 := by rw [h_ankeny]
      _ = (q : ℤ) * ((n : ℤ) - x^2) := by ring

  have h_diff_nonneg : 0 ≤ (n : ℤ) - x^2 := by
    have h_rhs : 0 ≤ y^2 + (n : ℤ) * z^2 := by
      apply add_nonneg (sq_nonneg y)
      apply mul_nonneg (Int.natCast_nonneg n) (sq_nonneg z)
    rw [h_eq] at h_rhs
    have hq_pos : 0 < (q : ℤ) := by
      have : 0 < q := hq_prime.pos
      exact_mod_cast this
    exact nonneg_of_mul_nonneg_right h_rhs hq_pos

  let K := ((n : ℤ) - x^2).natAbs
  have hK_eq : (K : ℤ) = (n : ℤ) - x^2 := Int.natAbs_of_nonneg h_diff_nonneg

  by_cases hK0 : K = 0
  · refine ⟨0, 0, ?_⟩
    have : (n : ℤ) = x ^ 2 := by
      have : (n : ℤ) - x ^ 2 = 0 := by simpa [hK0] using hK_eq.symm
      linarith
    simpa [this]
  ·
    have hK_sq_add_sq : ∃ u v : ℕ, K = u ^ 2 + v ^ 2 := by
      refine (Nat.eq_sq_add_sq_iff (n := K)).2 ?_
      intro p hpK hp4
      -- Q₁ parity kernel (currently a single lemma boundary).
      simpa using
        ankeny_even_padicValNat_of_mem_primeFactors_q1 (n := n) (q := q) (K := K) (p := p)
          (x := x) (y := y) (z := z) (b := b)
          hq1 hq_prime hq_mod hn_sq hK_eq (by
            -- cast `h_eq` into the expected `y^2 + n*z^2 = q*K` form
            simpa [hK_eq, mul_assoc, mul_left_comm, mul_comm] using congrArg (fun t : ℤ => t) h_eq)
          hxy hybz hb hpK hp4

    obtain ⟨uN, vN, hK⟩ := hK_sq_add_sq
    refine ⟨(uN : ℤ), (vN : ℤ), ?_⟩
    have hKz : (K : ℤ) = (uN ^ 2 + vN ^ 2 : ℤ) := by exact_mod_cast hK
    have hn_int : (n : ℤ) = x ^ 2 + (K : ℤ) := by linarith [hK_eq]
    calc
      (n : ℤ) = x ^ 2 + (K : ℤ) := hn_int
      _ = x ^ 2 + (uN ^ 2 + vN ^ 2 : ℤ) := by simpa [hKz]
      _ = x ^ 2 + (uN : ℤ) ^ 2 + (vN : ℤ) ^ 2 := by simp [pow_two, add_assoc]

/-- Final theorem for `n ≡ 3 (mod 8)`. -/
theorem sum_three_squares_of_three_mod_eight (n : ℕ) (hn : n % 8 = 3) :
    ∃ x y z : ℕ, x^2 + y^2 + z^2 = n := by
  obtain ⟨s, m, hm_eq, hm_sq⟩ := exists_squarefree_part n
  have hm_mod : m % 8 = 3 := squarefree_part_mod_eight n s m hm_eq hn
  have hm_odd : Odd m := by
    have : m % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have hm_pos : 0 < m := by omega
  obtain ⟨q, hqp, hq1, hq_mod⟩ := exists_ankeny_prime m hm_mod
  have : ∃ b : ℤ, b ^ 2 ≡ - (m : ℤ) [ZMOD (2 * q)] := exists_ankeny_b m q hm_mod hqp hq1 hq_mod
  obtain ⟨b, hb⟩ := this
  obtain ⟨x, y, z, h_rep, h_nz, hxy, hybz⟩ := exists_ankeny_representation m q b hm_pos hm_odd hqp hq1 hq_mod hb
  obtain ⟨u, v, h_final⟩ :=
    reduction_to_sum_three_squares m q x y z h_rep hqp hq1 hq_mod hm_odd hm_sq b hxy hybz
  use s * x.natAbs, s * u.natAbs, s * v.natAbs
  zify
  -- Keep this simp list minimal to avoid unused-simp-arg warnings.
  simp only [mul_pow, ← mul_add, sq_abs]
  have hm_eq_int : (n : ℤ) = s^2 * m := by exact_mod_cast hm_eq
  rw [← h_final, ← hm_eq_int]
  -- `ring` was previously here, but the goal is already closed after rewriting.

/-- Variant of the Ankeny/Minkowski route for the residue class `n ≡ 1 (mod 8)`.

This reuses the same lattice/ellipsoid setup (`2q` in the quadratic form) but swaps the Jacobi-symbol
computation step (see `exists_ankeny_b_one_mod_eight`). -/
theorem sum_three_squares_of_one_mod_eight (n : ℕ) (hn : n % 8 = 1) :
    ∃ x y z : ℕ, x^2 + y^2 + z^2 = n := by
  obtain ⟨s, m, hm_eq, hm_sq⟩ := exists_squarefree_part n
  have hm_mod : m % 8 = 1 := _root_.GeometryOfNumbers.squarefree_part_mod_eight_one n s m hm_eq hn
  have hm_odd : Odd m := by
    have : m % 2 = 1 := by omega
    exact Nat.odd_iff.2 this
  have hm_pos : 0 < m := by omega
  obtain ⟨q, hqp, hq1, hq_mod⟩ := exists_ankeny_prime_one_mod_eight m hm_mod
  obtain ⟨b, hb⟩ := exists_ankeny_b_one_mod_eight m q hm_mod hqp hq1 hq_mod
  obtain ⟨x, y, z, h_rep, h_nz, hxy, hybz⟩ := exists_ankeny_representation m q b hm_pos hm_odd hqp hq1 hq_mod hb
  obtain ⟨u, v, h_final⟩ :=
    reduction_to_sum_three_squares m q x y z h_rep hqp hq1 hq_mod hm_odd hm_sq b hxy hybz
  use s * x.natAbs, s * u.natAbs, s * v.natAbs
  zify
  simp only [mul_pow, ← mul_add, sq_abs]
  have hm_eq_int : (n : ℤ) = s^2 * m := by exact_mod_cast hm_eq
  rw [← h_final, ← hm_eq_int]

end GeometryOfNumbers