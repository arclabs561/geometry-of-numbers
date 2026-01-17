import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Int.ModEq
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import PolygonalNumberTheorem.Legendre.Exceptions

/-!
# Minkowski Descent for Legendre's Three-Squares Theorem

This file is a (currently partial) formalization of a Minkowski-style route to
Legendre’s three-square theorem, specialized to the key case \(n \equiv 3 \pmod 8\).

## What this file is trying to prove

Ultimately we want:

- `sum_three_squares_of_three_mod_eight`: if `n % 8 = 3`, then `n` is a sum of three squares.
- `minkowski_three_squares`: the general statement “every `n` not of the form \(4^a(8b+7)\) is
  a sum of three squares”.

This file is one attempt at packaging the Minkowski step as a reusable “descent lattice” lemma.
The fully-worked Ankeny (1957) proof lives in `PolygonalNumberTheorem/Legendre/Ankeny.lean`.

## Intuition first (the data flow)

The geometry-of-numbers step looks like this:

1. Choose integers `u, v` such that \(u^2 + v^2 + 1 \equiv 0 \pmod n\).  
   (This is the “local condition” that makes the norm square congruence work.)

2. Build a rank-3 ℤ-lattice `descent_lattice n u v` inside `E = ℝ^3` encoding the congruences
   \(x \equiv u z \pmod n\) and \(y \equiv v z \pmod n\).

3. Compute the covolume of this lattice via an explicit basis matrix and
   `ZSpan.volume_fundamentalDomain`.

4. Apply Minkowski’s theorem
   `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
   to a symmetric convex body (typically an ellipsoid).

5. Convert the resulting nonzero lattice point back into a three-squares representation.

## Evidence / key Mathlib lemmas used in this style of proof

- Minkowski: `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`
  (`Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean`)
- Covolume via basis: `ZSpan.isAddFundamentalDomain'`, `ZSpan.volume_fundamentalDomain`
  (`Mathlib/Algebra/Module/ZLattice/*`)
- Volume scaling under linear maps (for ellipsoids): `MeasureTheory.addHaar_preimage_linearMap`
  (`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`)

## Pitfalls (Lean)

- Many geometric statements are phrased as `IsAddFundamentalDomain (↥L) ...`, i.e. they depend on the
  *carrier subtype* of a lattice. Rewriting across `L = L'` is therefore fragile.
  Prefer returning an explicit lattice together with inclusion lemmas, as in the Ankeny file.
-/

namespace PolygonalNumberTheorem

open MeasureTheory MeasureTheory.Measure Set WithLp Module
open scoped NNReal ENNReal BigOperators Matrix

/-! `E` is just `ℝ^3`, written as `Fin 3 → ℝ` (the type used by Mathlib’s `volume` on `ℝ^ι`). -/
abbrev E := (Fin 3 → ℝ)

/-- A concrete basis of `E = ℝ^3` used to define the descent lattice.

### Informal description

We build a basis by starting from the standard basis `b0 := Pi.basisFun` and mapping it by an
invertible linear map whose matrix is:

```text
⎡ n  0  u ⎤
⎢ 0  n  v ⎥
⎣ 0  0  1 ⎦
```

This matrix is upper triangular, so its determinant is \(n^2\), hence nonzero when `n > 0`.

### Why we need this

This basis is used to express `descent_lattice` as a ℤ-span (`descent_lattice_eq_zspan`), and then
compute its covolume (`descent_lattice_covolume`) using `ZSpan.volume_fundamentalDomain`.

### Pitfall

In Lean, `Matrix.of basis` uses basis vectors as columns, so the matrix you get is typically a
transpose of the matrix used to define the linear map. When computing determinants, use
`Matrix.det_transpose` rather than fighting definitional equalities.
-/
noncomputable def descent_basis (n : ℕ) (u v : ℤ) (hn : 0 < n) :
    Module.Basis (Fin 3) ℝ E :=
  let b0 : Module.Basis (Fin 3) ℝ E := Pi.basisFun ℝ (Fin 3)
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    !![(n : ℝ), 0, (u : ℝ);
      0, (n : ℝ), (v : ℝ);
      0, 0, (1 : ℝ)]
  have hdet : A.det ≠ 0 := by
    sorry
  b0.map (Matrix.toLinearEquiv b0 A (isUnit_iff_ne_zero.mpr hdet))

/-- The “descent lattice” inside `E = ℝ^3`.

An element `p : E` is in `descent_lattice n u v` iff it is an integer point `(x,y,z)` (viewed in `ℝ^3`)
with the congruences:

```text
x ≡ u*z  [ZMOD n]
y ≡ v*z  [ZMOD n]
```

### Why we need this

If `u^2 + v^2 + 1 ≡ 0 [ZMOD n]`, then any lattice point satisfies
`x^2 + y^2 + z^2 ≡ 0 [ZMOD n]` (see `mem_descent_lattice_norm_sq_mod`). This is the algebraic side of
the Minkowski argument: lattice membership ⇒ norm-square congruence.
-/
def descent_lattice (n : ℕ) (u v : ℤ) : AddSubgroup E where
  carrier := { p | ∃ x y z : ℤ, p 0 = (x : ℝ) ∧ p 1 = (y : ℝ) ∧ p 2 = (z : ℝ) ∧
                                x ≡ u * z [ZMOD n] ∧ y ≡ v * z [ZMOD n] }
  add_mem' := by
    rintro _ _ ⟨x1, y1, z1, hx1_p, hy1_p, hz1_p, hx1, hy1⟩ ⟨x2, y2, z2, hx2_p, hy2_p, hz2_p, hx2, hy2⟩
    use x1 + x2, y1 + y2, z1 + z2
    constructor; · simp [hx1_p, hx2_p]
    constructor; · simp [hy1_p, hy2_p]
    constructor; · simp [hz1_p, hz2_p]
    constructor
    · rw [mul_add]; exact hx1.add hx2
    · rw [mul_add]; exact hy1.add hy2
  zero_mem' := by
    use 0, 0, 0
    constructor; · simp
    constructor; · simp
    constructor; · simp
    constructor <;> simp
  neg_mem' := by
    rintro _ ⟨x, y, z, hx_p, hy_p, hz_p, hx, hy⟩
    use -x, -y, -z
    constructor; · simp [hx_p]
    constructor; · simp [hy_p]
    constructor; · simp [hz_p]
    constructor
    · rw [mul_neg]; exact hx.neg
    · rw [mul_neg]; exact hy.neg

/-- Characterize the descent lattice as explicit integer combinations. -/
lemma mem_descent_lattice_iff (n : ℕ) (u v : ℤ) (p : E) :
    p ∈ descent_lattice n u v ↔
    ∃ x y z : ℤ, p 0 = (x : ℝ) ∧ p 1 = (y : ℝ) ∧ p 2 = (z : ℝ) ∧
                 x ≡ u * z [ZMOD n] ∧ y ≡ v * z [ZMOD n] := Iff.rfl

/-- Characterize the descent lattice as the Z-span of the basis. -/
lemma descent_lattice_eq_zspan (n : ℕ) (u v : ℤ) (hn : 0 < n) :
    descent_lattice n u v = (Submodule.span ℤ (Set.range (descent_basis n u v hn))).toAddSubgroup := by
  sorry

/-- If `p ∈ descent_lattice n u v` and `u^2 + v^2 + 1 ≡ 0 [ZMOD n]`, then the norm square satisfies
`x^2 + y^2 + z^2 ≡ 0 [ZMOD n]`.

### Evidence

The proof is purely algebraic: use `Int.ModEq.pow` to square the defining congruences, add them, then
factor out `z^2`.
-/
lemma mem_descent_lattice_norm_sq_mod (n : ℕ) (u v : ℤ) (p : E)
    (hp : p ∈ descent_lattice n u v)
    (h_local : u^2 + v^2 + 1 ≡ 0 [ZMOD n]) :
    ∃ x y z : ℤ, p 0 = (x : ℝ) ∧ p 1 = (y : ℝ) ∧ p 2 = (z : ℝ) ∧
                 x^2 + y^2 + z^2 ≡ 0 [ZMOD n] := by
  obtain ⟨x, y, z, hx0, hy0, hz0, hx, hy⟩ := hp
  use x, y, z, hx0, hy0, hz0
  have hsum : x^2 + y^2 + z^2 ≡ (u * z)^2 + (v * z)^2 + z^2 [ZMOD n] := by
    apply Int.ModEq.add
    · apply Int.ModEq.add
      · exact hx.pow 2
      · exact hy.pow 2
    · exact Int.ModEq.refl _
  have h_norm_id : (u * z)^2 + (v * z)^2 + z^2 = z^2 * (u^2 + v^2 + 1) := by ring
  have h_final : z^2 * (u^2 + v^2 + 1) ≡ z^2 * 0 [ZMOD n] := Int.ModEq.mul_left _ h_local
  rw [mul_zero] at h_final
  exact hsum.trans (h_norm_id ▸ h_final)

/-- The volume of the fundamental domain of the descent lattice. -/
lemma descent_lattice_covolume (n : ℕ) (u v : ℤ) (hn : 0 < n) :
    ∃ F : Set E,
      IsAddFundamentalDomain (descent_lattice n u v) F volume ∧
      volume F = (n ^ 2 : ℝ≥0∞) := by
  sorry

/-- For odd `n`, there exist `u, v` such that `u^2 + v^2 + 1 ≡ 0 [ZMOD n]`.

This is the “local solvability” input needed by `mem_descent_lattice_norm_sq_mod`.
In Ankeny’s proof this comes from quadratic-residue arguments; here it is left as a placeholder.
-/
lemma exists_sq_add_sq_add_one_eq_zero_mod_odd (n : ℕ) (hn : Odd n) :
    ∃ u v : ℤ, u^2 + v^2 + 1 ≡ 0 [ZMOD n] := by
  sorry

/-- Every integer `n ≡ 3 (mod 8)` is a sum of three squares. -/
theorem sum_three_squares_of_three_mod_eight (n : ℕ) (hn : n % 8 = 3) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  sorry

/-- Main theorem (target statement): every `n` not of the form \(4^a(8b+7)\) is a sum of 3 squares.

This file currently does not complete the proof; the completed proof route is in `Legendre/Ankeny.lean`.
-/
theorem minkowski_three_squares (n : ℕ) (_h : ¬ Nat.is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  sorry

end PolygonalNumberTheorem
