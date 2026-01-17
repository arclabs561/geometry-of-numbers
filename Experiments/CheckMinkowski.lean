import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Data.Set.Countable
import Mathlib.Tactic

noncomputable section

/-!
# Minkowski + lattices: API probes and “toy proofs”

This file is a scratchpad for *learning the exact shapes* of the Mathlib lemmas we rely on for the
Ankeny → Legendre three-squares route.

## Why this file exists

- In the main proof, the Minkowski step is a glue point between analysis/measure theory and
  arithmetic (`ℤ`-lattices, congruence-defined sets, determinants/covolumes).
- When these steps fail in Lean, the failure is usually *not* conceptual; it’s about
  definitional equalities, the exact binder shapes, and rewriting/normalization in `ENNReal`.

So we keep a few small, compiling examples here that demonstrate:

- what Minkowski’s theorem expects as inputs,
- how to get the required `[Countable ↥L]` instance in practice,
- how to compute covolumes via determinants,
- how to normalize volume inequalities to `ENNReal.ofReal` comparisons,
- how to express “ellipsoid volumes” as preimages under invertible linear maps.

## Evidence / key API

- `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
  (`Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean`)
- `ZSpan.isAddFundamentalDomain'`, `ZSpan.volume_fundamentalDomain`
  (`Mathlib/Algebra/Module/ZLattice/*`)
- `MeasureTheory.addHaar_preimage_linearMap`, `LinearMap.det_toLin'`
  (`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`,
   `Mathlib/LinearAlgebra/Determinant.lean`)

## Pitfalls seen in this repo

- `simp` can rewrite `Set.pi ... (Icc ...)` into `Set.Icc (fun i => ...) (fun i => ...)`, which can
  break later lemmas expecting the “pi form”. We sometimes use `simp [..., -Set.pi_univ_Icc]`.
- `ENNReal.ofReal (p ^ n)` vs `(ENNReal.ofReal p) ^ n`: normalize with `ENNReal.ofReal_pow`.
-/

open MeasureTheory MeasureTheory.Measure

-- Probes for the exact lemma names/shapes we rely on downstream.
#check MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
#check MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
#check ZLattice.covolume_eq_det
#check ZLattice.covolume_eq_measure_fundamentalDomain

/-!
## Toy 1: ZSpan fundamental domain and volume for a simple ℤ-span lattice in `ℝ^3`

This mirrors what we ended up doing in `Covolume/Legendre/Ankeny.lean`,
but pared down to the minimum: pick a basis `B`, then `F := ZSpan.fundamentalDomain B`,
then:

- `ZSpan.isAddFundamentalDomain' B volume`
- `ZSpan.volume_fundamentalDomain B`
-/

open scoped BigOperators Matrix

section ToyZSpan

-- A concrete diagonal matrix in `ℝ^3`.
def toyA : Matrix (Fin 3) (Fin 3) ℝ :=
  (![![2, 0, 0], ![0, 3, 0], ![0, 0, 5]] : Matrix (Fin 3) (Fin 3) ℝ)

-- A basis of `ℝ^3` obtained from a diagonal matrix, so `det` is a short calculation.
def toyBasis : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ) :=
  (Pi.basisFun ℝ (Fin 3)).map
    (Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 3))
      toyA
      (by
        -- det = 2*3*5 ≠ 0
        have : toyA.det = (30 : ℝ) := by
          simp [toyA, Matrix.det_fin_three]
          norm_num
        -- over a field, det ≠ 0 ↔ IsUnit det
        have : toyA.det ≠ 0 := by
          simpa [this]
        simpa [isUnit_iff_ne_zero, this]))

-- The ℤ-span lattice and its fundamental domain.
def toyLattice : AddSubgroup (Fin 3 → ℝ) :=
  (Submodule.span ℤ (Set.range (toyBasis))).toAddSubgroup

def toyFD : Set (Fin 3 → ℝ) :=
  ZSpan.fundamentalDomain (toyBasis)

-- `toyLattice` is countable: it's a ℤ-span of a finite `Set.range`.
instance : Countable (↥toyLattice) := by
  change Countable (Submodule.span ℤ (Set.range (toyBasis)))
  infer_instance

-- The fundamental-domain theorem for the span lattice.
example : IsAddFundamentalDomain toyLattice toyFD volume := by
  -- This is exactly the lemma we use in the Ankeny proof, but with a tiny toy basis.
  simpa [toyLattice, toyFD] using (ZSpan.isAddFundamentalDomain' (toyBasis) volume)

-- Volume of the fundamental domain is `ENNReal.ofReal |det|`.
example :
    volume toyFD =
      ENNReal.ofReal |(Matrix.of (toyBasis)).det| := by
  simpa [toyFD] using (ZSpan.volume_fundamentalDomain (toyBasis))

-- In this toy, the “basis matrix” is `toyAᵀ` (basis vectors are the columns of `toyA`).
lemma toyBasis_matrixOf : Matrix.of (toyBasis) = (toyA)ᵀ := by
  classical
  ext i j
  -- `toyBasis i` is `toLin _ _ toyA (basisFun i)`, i.e. column `i` of `toyA`.
  -- `Matrix.of toyBasis` therefore has entries `(i,j) ↦ toyA j i`, i.e. `toyAᵀ`.
  simp [toyBasis, Module.Basis.map_apply, Matrix.toLinearEquiv, Matrix.of_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Pi.basisFun_apply, Matrix.mulVec_single_one,
    Matrix.transpose_apply, toyA]

-- Therefore `det (Matrix.of toyBasis) = det toyA = 30`.
lemma toyBasis_det : (Matrix.of (toyBasis)).det = (30 : ℝ) := by
  have hA : toyA.det = (30 : ℝ) := by
    simp [toyA, Matrix.det_fin_three]
    norm_num
  calc
    (Matrix.of toyBasis).det = (toyAᵀ).det := by simpa [toyBasis_matrixOf]
    _ = toyA.det := by simpa using (Matrix.det_transpose toyA)
    _ = 30 := hA

end ToyZSpan

/-!
## Toy 2: The “ellipsoid volume” pattern via a diagonal linear map and an L2 ball

In Ankeny, the convex body is an ellipsoid defined by

```text
2q x₀² + x₁² + n x₂² < 4 n q .
```

The clean way to compute its volume in Mathlib is:

- express the ellipsoid as `T ⁻¹' (Metric.ball 0 R)` for a diagonal linear map `T`,
- use `MeasureTheory.Measure.addHaar_preimage_linearMap` to get a determinant factor,
- compute `volume (Metric.ball 0 R)` explicitly in dimension `3`,
- use a coarse bound `π > 3` (`Real.pi_gt_three`) to discharge the final strict inequality needed
  by Minkowski.

This section pins down the exact type synonyms involved (`EuclideanSpace` is a `WithLp` wrapper),
so we don’t repeat the same “wrong ambient type” mistakes in the main proof file.
-/

section ToyEllipsoidVolume

open scoped Real

-- Work in `Fin 3 → ℝ` directly. For ellipsoids we will use the *L2 ball as a set*:
-- `{x | (∑ i, |x i|^2)^(1/2) < R}`, whose volume is computed by
-- `MeasureTheory.volume_sum_rpow_lt` (with `p = 2`).
abbrev E3 := Fin 3 → ℝ

-- A diagonal linear map on `E3` (implemented via a diagonal matrix).
def diagLin (a b c : ℝ) : E3 →ₗ[ℝ] E3 :=
  Matrix.toLin' (Matrix.diagonal ![a, b, c])

-- The diagonal determinant.
lemma det_diagLin (a b c : ℝ) :
    LinearMap.det (diagLin a b c) = a * b * c := by
  -- `det_toLin'` reduces to matrix determinant.
  simp [diagLin, LinearMap.det_toLin', Matrix.det_diagonal, Fin.prod_univ_three]

/-!
### Diagonal linear maps act coordinatewise

This is the “dot-product mismatch” failure mode we hit in `Ankeny.lean`:
`Matrix.toLin'` expands to a row-dot-product (`⬝ᵥ`), but for diagonal matrices we want the
simple coordinate formula `v i * x i`.

These lemmas pin down that reduction and give a clean `T x = 0 → x = 0` fact for diagonal maps.
-/

lemma diagLin_apply (a b c : ℝ) (x : E3) :
    diagLin a b c x = fun i =>
      (Matrix.diagonal ![a, b, c] *ᵥ x) i := by
  rfl

lemma diagLin_apply_coord (a b c : ℝ) (x : E3) (i : Fin 3) :
    diagLin a b c x i = (![a, b, c] i) * x i := by
  -- `toLin'` is `mulVec`; `mulVec_diagonal` is the key simplifier.
  simpa [diagLin, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

lemma diagLin_eq_zero_of_ne_zero (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {x : E3} (hx : diagLin a b c x = 0) : x = 0 := by
  funext i
  fin_cases i
  · -- i = 0
    have h0 : a * x 0 = 0 := by
      -- apply `congrArg` to the function equality at coordinate `0`
      have := congrArg (fun y => y 0) hx
      simpa [diagLin_apply_coord] using this
    exact (mul_eq_zero.mp h0).resolve_left ha
  · -- i = 1
    have h1 : b * x 1 = 0 := by
      have := congrArg (fun y => y 1) hx
      simpa [diagLin_apply_coord] using this
    exact (mul_eq_zero.mp h1).resolve_left hb
  · -- i = 2
    have h2 : c * x 2 = 0 := by
      have := congrArg (fun y => y 2) hx
      simpa [diagLin_apply_coord] using this
    exact (mul_eq_zero.mp h2).resolve_left hc

-- The L2 ball as a set in coordinate form (this avoids `WithLp` type synonyms).
def l2Ball (R : ℝ) : Set E3 :=
  {x | (∑ i, |x i| ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) < R}

-- Volume of the L2 ball in `ℝ^3`, straight from `volume_sum_rpow_lt` (p = 2, card = 3).
lemma volume_l2Ball (R : ℝ) :
    volume (l2Ball R) =
      (ENNReal.ofReal R) ^ 3 *
        ENNReal.ofReal
          ((2 * Real.Gamma (1 / (2 : ℝ) + 1)) ^ (Fintype.card (Fin 3)) /
            Real.Gamma ((Fintype.card (Fin 3) : ℝ) / (2 : ℝ) + 1)) := by
  -- This is a direct specialization of `MeasureTheory.volume_sum_rpow_lt`.
  have hp : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
  -- `Nonempty (Fin 3)` is automatic.
  simpa [l2Ball, Fintype.card_fin] using
    (MeasureTheory.volume_sum_rpow_lt (ι := Fin 3) (p := (2 : ℝ)) hp R)

-- Haar scaling: volume of the diagonal-preimage of the L2 ball.
lemma volume_preimage_l2Ball (a b c R : ℝ) (hdet : a * b * c ≠ 0) :
    volume ((diagLin a b c) ⁻¹' (l2Ball R)) =
      ENNReal.ofReal |(a * b * c)⁻¹| * volume (l2Ball R) := by
  -- The general lemma is `Measure.addHaar_preimage_linearMap` in `EqHaar.lean`.
  -- We rewrite `det (diagLin ...)` using `det_diagLin`.
  have hdet' : LinearMap.det (diagLin a b c) ≠ 0 := by
    simpa [det_diagLin] using hdet
  simpa [MeasureTheory.Measure.addHaar_preimage_linearMap, det_diagLin]
    using (MeasureTheory.Measure.addHaar_preimage_linearMap (μ := volume)
      (f := diagLin a b c) hdet' (s := l2Ball R))

end ToyEllipsoidVolume

/-!
## Toy 2: Minkowski invocation skeleton

This is *not* a proof yet; it’s a “shape check” for the lemma:
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`.

The hard part in our real proof is building a measurable symmetric convex body `s`
and proving the measure inequality. This section shows the binder shape and the data-flow
once those hypotheses are available.
-/

section ToyMinkowski

open MeasureTheory

#check MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure

/-!
### Concrete Minkowski toy: a nonzero lattice point in a big cube

This is a fully-typed (and fully-proved) *miniature* of the “Minkowski step” we need later:

- we already have a fundamental domain `toyFD` for `toyLattice` from Toy 1
- we build a symmetric convex set `sR = [-R,R]^3`
- we pick a concrete `R` large enough that `volume toyFD * 2^3 < volume sR`
- Minkowski gives a **nonzero** `x : toyLattice` with `x ∈ sR`

This is not Ankeny’s ellipsoid (that’s the real work), but it exercises the same API.
-/

section Concrete

open scoped BigOperators

-- Work in `ℝ^3` with the toy lattice from the previous section.
local notation "E3" => (Fin 3 → ℝ)

-- A big axis-aligned cube in `ℝ^3`.
def cube (R : ℝ) : Set E3 :=
  Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-R) R)

lemma cube_symm (R : ℝ) : ∀ x ∈ cube R, -x ∈ cube R := by
  intro x hx
  classical
  -- coordinatewise: if `x i ∈ Icc(-R,R)` then `-x i ∈ Icc(-R,R)`
  simp [cube, Set.mem_pi, -Set.pi_univ_Icc] at hx ⊢
  intro i
  specialize hx i
  rcases hx with ⟨hxL, hxU⟩
  constructor <;> linarith

lemma cube_convex (R : ℝ) : Convex ℝ (cube R) := by
  -- `Icc` is convex in an ordered `ℝ`-module; pointwise order gives the instance on `E3`.
  simpa [cube, -Set.pi_univ_Icc] using (convex_pi (𝕜 := ℝ) (fun _ _ => convex_Icc (-R) R))

-- The volume of `[-R,R]` in `ℝ` is `2R` (as an `ENNReal`), and the `ℝ^3` cube is the cube of that.
lemma volume_cube (R : ℝ) (hR : 0 ≤ R) :
    volume (cube R) = ENNReal.ofReal ((2 * R) ^ 3) := by
  classical
  -- `volume` on `E3` is product Lebesgue measure: `volume_pi` + 1D interval lengths.
  -- `Real.volume_Icc` gives `ofReal (R - (-R)) = ofReal (R + R)`.
  -- Normalize `R + R` to `2 * R` at the end.
  have hnonneg : 0 ≤ R + R := by nlinarith
  -- `ofReal (p^n) = ofReal p ^ n` is the key normal form for the product-measure computation.
  simp [cube, volume_pi, Measure.pi_pi, Real.volume_Icc, -Set.pi_univ_Icc, two_mul,
    ENNReal.ofReal_pow hnonneg]

/-!
Now that we have:

- a countability instance for `toyLattice` (as a `span ℤ` of a finite range),
- an explicit determinant computation for `toyBasis`,

we can actually run Minkowski on a cube and close the volume inequality completely.

This is still not Ankeny’s ellipsoid, but it validates the full Minkowski call site.
-/

section MinkowskiCubeToy

-- A fully concrete Minkowski call: `toyLattice` has a nonzero point in `[-4,4]^3`.
example :
    ∃ x : toyLattice, x ≠ 0 ∧ (x : E3) ∈ cube 4 := by
  classical
  have fund : IsAddFundamentalDomain (↥toyLattice) toyFD volume := by
    simpa [toyLattice, toyFD] using (ZSpan.isAddFundamentalDomain' (toyBasis) volume)

  have hFD : volume toyFD = ENNReal.ofReal (30 : ℝ) := by
    -- `volume toyFD = ofReal |det|`, and `det = 30` in this toy.
    simpa [toyFD, toyBasis_det] using (ZSpan.volume_fundamentalDomain (toyBasis))

  have hCube : volume (cube 4) = ENNReal.ofReal (512 : ℝ) := by
    have h := (volume_cube (R := (4 : ℝ)) (by norm_num : (0 : ℝ) ≤ 4))
    have hpow : ((2 * (4 : ℝ)) ^ 3) = (512 : ℝ) := by norm_num
    simpa [hpow] using h

  have hrank : Module.finrank ℝ E3 = 3 := by simp

  have hineq : volume toyFD * 2 ^ (Module.finrank ℝ E3) < volume (cube 4) := by
    have hL : volume toyFD * 2 ^ (Module.finrank ℝ E3) = ENNReal.ofReal (240 : ℝ) := by
      calc
        volume toyFD * 2 ^ (Module.finrank ℝ E3)
            = ENNReal.ofReal (30 : ℝ) * (2 : ENNReal) ^ 3 := by
                simpa [hFD, hrank]
        _ = ENNReal.ofReal (30 : ℝ) * (8 : ENNReal) := by norm_num
        _ = ENNReal.ofReal (30 : ℝ) * ENNReal.ofReal (8 : ℝ) := by simp
        _ = ENNReal.ofReal ((30 : ℝ) * 8) := by
              symm
              simpa using (ENNReal.ofReal_mul (p := (30 : ℝ)) (q := (8 : ℝ)) (by positivity))
        _ = ENNReal.ofReal (240 : ℝ) := by norm_num
    -- convert to a real inequality under `ENNReal.ofReal`.
    have : ENNReal.ofReal (240 : ℝ) < ENNReal.ofReal (512 : ℝ) := by
      have hpos : (0 : ℝ) < 512 := by norm_num
      exact (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by norm_num : (240 : ℝ) < 512)
    -- Rewrite the Minkowski inequality goal into the same `ofReal` comparison.
    rw [hL, hCube]
    exact this

  rcases
      MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
        (μ := volume) (F := toyFD) (s := cube 4) (L := toyLattice)
        fund (cube_symm (R := 4)) (cube_convex (R := 4)) hineq
    with ⟨x, hx0, hx_mem⟩
  exact ⟨x, hx0, hx_mem⟩

end MinkowskiCubeToy

section CountabilityToy

-- A tiny countability helper: any subgroup that is the range of a map from a countable type is countable.
-- (This is the most direct way to satisfy Minkowski’s `[Countable L]` premise in experiments.)
def intCastHom : (Fin 3 → ℤ) →+ E3 where
  toFun z i := (z i : ℝ)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def Z3_as_addSubgroup : AddSubgroup E3 :=
  intCastHom.range

-- The underlying set is countable, hence the subtype is countable.
instance : Countable (↥Z3_as_addSubgroup) := by
  classical
  -- `Fin 3 → ℤ` is countable, so the range of the “integer cast” map is a countable set in `E3`.
  have hEq : (Z3_as_addSubgroup : Set E3) = Set.range (fun z : Fin 3 → ℤ => intCastHom z) := by
    ext x
    simp [Z3_as_addSubgroup, AddMonoidHom.mem_range]
  have hset : (Z3_as_addSubgroup : Set E3).Countable := by
    simpa [hEq] using (Set.countable_range (fun z : Fin 3 → ℤ => intCastHom z))
  exact (Set.countable_coe_iff.2 hset)

end CountabilityToy

end Concrete

end ToyMinkowski

/-!
## Toy 3: Ellipsoid volumes via linear changes of variables

For Ankeny, the convex body is an ellipsoid defined by a quadratic form. The clean way to get its
volume is: “an ellipsoid is the preimage of a ball under an invertible linear map”, then use the
Haar/Lebesgue scaling lemma for linear maps.

This section isolates the *measure-theory plumbing*; it does not try to compute `volume (ball 0 r)`
explicitly.
-/

section ToyEllipsoid

open MeasureTheory

local notation "E3" => (Fin 3 → ℝ)

-- A convenient abbreviation for the linear map induced by a matrix on `ℝ^3`.
def linOfMatrix (D : Matrix (Fin 3) (Fin 3) ℝ) : E3 →ₗ[ℝ] E3 :=
  Matrix.toLin' D

-- Volume of the preimage of a ball under an invertible linear map.
lemma volume_preimage_ball_linOfMatrix (D : Matrix (Fin 3) (Fin 3) ℝ) (hD : D.det ≠ 0) (r : ℝ) :
    volume ((linOfMatrix D) ⁻¹' Metric.ball (0 : E3) r)
      = ENNReal.ofReal |(D.det)⁻¹| * volume (Metric.ball (0 : E3) r) := by
  -- `det (toLin' D) = det D`
  have hf : LinearMap.det (linOfMatrix D) ≠ 0 := by
    simpa [linOfMatrix, LinearMap.det_toLin'] using hD
  -- Haar-scaling for Lebesgue measure:
  simpa [linOfMatrix, LinearMap.det_toLin'] using
    (addHaar_preimage_linearMap (μ := (volume : Measure E3)) hf (Metric.ball (0 : E3) r))

end ToyEllipsoid

-- For Ankeny, the intended covolume computation is via an explicit ℤ-basis in ℤ^3:
--
--   v1 = (n, 0, 0)
--   v2 = (2q, 2q, 0)
--   v3 = (b, b, 1)
--
-- det([v1 v2 v3]) = 2*n*q
--
-- The main missing work is turning `ankeny_lattice` (defined by congruences) into a `ZLattice`
-- or an equivalent `Submodule ℤ (Fin 3 → ℝ)` with that basis, so we can plug into `covolume_eq_det`.

def checkMinkowskiAvailable : IO Unit := do
  IO.println "Checking Minkowski (GeometryOfNumbers) imports..."
  IO.println "See `#check` outputs above for lemma names."

def main : IO Unit := checkMinkowskiAvailable

#eval main

