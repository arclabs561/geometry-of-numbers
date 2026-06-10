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
import GeometryOfNumbers.Legendre.Exceptions
import GeometryOfNumbers.Legendre.Main
import GeometryOfNumbers.Legendre.Ankeny
import GeometryOfNumbers.Core.ModularSquares

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
The fully-worked Ankeny (1957) proof lives in `GeometryOfNumbers/Legendre/Ankeny.lean`.

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
- Lattice covolume via basis: `ZSpan.isAddFundamentalDomain'`, `ZSpan.volume_fundamentalDomain`
  (`Mathlib/Algebra/Module/ZLattice/*`)
- Volume scaling under linear maps (for ellipsoids): `MeasureTheory.addHaar_preimage_linearMap`
  (`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`)

## Pitfalls (Lean)

- Many geometric statements are phrased as `IsAddFundamentalDomain (↥L) ...`, i.e. they depend on the
  *carrier subtype* of a lattice. Rewriting across `L = L'` is therefore fragile.
  Prefer returning an explicit lattice together with inclusion lemmas, as in the Ankeny file.
-/

namespace GeometryOfNumbers
open MeasureTheory MeasureTheory.Measure Set WithLp Module
open scoped NNReal ENNReal BigOperators Matrix

/-! `E` is just `ℝ^3`, written as `Fin 3 → ℝ` (the type used by Mathlib’s `volume` on `ℝ^ι`). -/
abbrev E := (Fin 3 → ℝ)

/-- A concrete basis of `E = ℝ^3` used to define the descent lattice.

### Informal description

We build a basis by starting from the standard basis `b0 := Pi.basisFun` and mapping it by an
invertible linear map whose matrix is:

```text
[ n  0  u ]
| 0  n  v |
[ 0  0  1 ]
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
    -- Upper-triangular, so det is the product of diagonal entries: `n*n*1`.
    have htri : A.BlockTriangular id := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [A] at hij ⊢
    have hdet_eq : A.det = ∏ i : Fin 3, A i i := Matrix.det_of_upperTriangular (M := A) htri
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
    have : (∏ i : Fin 3, A i i) ≠ 0 := by
      -- diagonal entries are `n, n, 1`
      simp [A, Fin.prod_univ_three, hn']
    exact hdet_eq.symm ▸ this
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
  classical
  -- For this explicit `descent_basis`, the basis vectors are the columns of the matrix:
  --   [ n  0  u ]
  --   | 0  n  v |
  --   [ 0  0  1 ]
  -- so the ℤ-span consists of all triples `(x,y,z)` with
  --   x = n*a + u*z,  y = n*b + v*z.
  let b0 : E := ![(n : ℝ), 0, 0]
  let b1 : E := ![0, (n : ℝ), 0]
  let b2 : E := ![(u : ℝ), (v : ℝ), 1]

  have hbasis0 : descent_basis n u v hn 0 = b0 := by
    -- Unfold the definition: the mapped basis is the standard basis multiplied by `A`.
    -- This is the first column.
    ext j
    fin_cases j <;>
      simp [descent_basis, b0, Basis.map_apply, Matrix.toLinearEquiv, Matrix.toLin_eq_toLin',
        Matrix.toLin'_apply, Pi.basisFun_apply]

  have hbasis1 : descent_basis n u v hn 1 = b1 := by
    -- second column
    ext j
    fin_cases j <;>
      simp [descent_basis, b1, Basis.map_apply, Matrix.toLinearEquiv, Matrix.toLin_eq_toLin',
        Matrix.toLin'_apply, Pi.basisFun_apply]

  have hbasis2 : descent_basis n u v hn 2 = b2 := by
    -- third column
    ext j
    fin_cases j <;>
      simp [descent_basis, b2, Basis.map_apply, Matrix.toLinearEquiv, Matrix.toLin_eq_toLin',
        Matrix.toLin'_apply, Pi.basisFun_apply]

  ext p
  constructor
  · intro hp
    -- Extract integer coordinates and congruences.
    rcases hp with ⟨x, y, z, hx0, hy0, hz0, hx, hy⟩
    -- Unpack congruences into explicit `n`-multiples.
    have hx_fac : ∃ t : ℤ, u * z = x + (n : ℤ) * t := (Int.modEq_iff_add_fac).1 hx
    have hy_fac : ∃ t : ℤ, v * z = y + (n : ℤ) * t := (Int.modEq_iff_add_fac).1 hy
    rcases hx_fac with ⟨tx, htx⟩
    rcases hy_fac with ⟨ty, hty⟩
    -- Rewrite as `x = n*a + u*z`, `y = n*b + v*z`.
    have hx' : (x : ℝ) = (n : ℝ) * (-tx : ℤ) + (u : ℝ) * z := by
      -- `u*z = x + n*tx` ⇒ `x = u*z - n*tx`
      have hx_int : (x : ℤ) = u * z - (n : ℤ) * tx := by linarith [htx]
      have hx_real : (x : ℝ) = (u : ℝ) * (z : ℝ) - (n : ℝ) * (tx : ℝ) := by
        exact_mod_cast hx_int
      -- rewrite `-(n*tx)` as `n*(-tx)` and reorder
      -- (avoid `nlinarith` here; this is pure ring bookkeeping).
      simpa [sub_eq_add_neg, Int.cast_neg, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
        using hx_real
    have hy' : (y : ℝ) = (n : ℝ) * (-ty : ℤ) + (v : ℝ) * z := by
      have hy_int : (y : ℤ) = v * z - (n : ℤ) * ty := by linarith [hty]
      have hy_real : (y : ℝ) = (v : ℝ) * (z : ℝ) - (n : ℝ) * (ty : ℝ) := by
        exact_mod_cast hy_int
      simpa [sub_eq_add_neg, Int.cast_neg, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm]
        using hy_real

    -- Show `p` is a ℤ-linear combination of the basis vectors.
    have hp_span : p ∈ Submodule.span ℤ (Set.range (descent_basis n u v hn)) := by
      -- Use the explicit coefficient function `c : Fin 3 → ℤ`.
      refine (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := descent_basis n u v hn) (x := p)).2 ?_
      refine ⟨![(-tx), (-ty), z], ?_⟩
      -- Expand the finitary sum and use the explicit basis vectors.
      -- (`•` is `zsmul`; on `ℝ` and `E` it coincides with multiplication by the integer cast.)
      funext j
      fin_cases j
      · -- coordinate 0
        -- p0 = x = n*(-tx) + u*z
        simp [Fin.sum_univ_three, hbasis0, hbasis1, hbasis2, b0, b1, b2, hx0, hx', zsmul_eq_mul]
        ring
      · -- coordinate 1
        simp [Fin.sum_univ_three, hbasis0, hbasis1, hbasis2, b0, b1, b2, hy0, hy', zsmul_eq_mul]
        ring
      · -- coordinate 2
        simp [Fin.sum_univ_three, hbasis0, hbasis1, hbasis2, b0, b1, b2, hz0, zsmul_eq_mul]

    -- Move from submodule membership to add subgroup membership.
    simpa using hp_span

  · intro hp_span
    -- Convert span-membership into an explicit integer combination of the three basis vectors.
    have hp' : p ∈ Submodule.span ℤ (Set.range (descent_basis n u v hn)) := by
      simpa using hp_span
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := descent_basis n u v hn) (x := p)).1 hp' with
      ⟨c, hc⟩
    -- Let the integer coefficients be `a,b,z`.
    let a : ℤ := c 0
    let b : ℤ := c 1
    let z : ℤ := c 2
    have hc0 : ∑ i : Fin 3, c i • descent_basis n u v hn i = p := hc
    -- Define integer coordinates `x,y` from the combination.
    let x : ℤ := n * a + u * z
    let y : ℤ := n * b + v * z
    refine ⟨x, y, z, ?_, ?_, ?_, ?_, ?_⟩
    · -- p 0 = x
      have := (congrArg (fun q : E => q 0) hc0).symm
      -- Evaluate the sum at coordinate 0 and simplify.
      -- This is where we use the explicit basis vectors.
      -- Note: `zsmul_eq_mul` converts ℤ-scalar action into multiplication by the integer cast in ℝ.
      simpa [a, b, z, x, b0, b1, b2, Fin.sum_univ_three, hbasis0, hbasis1, hbasis2, zsmul_eq_mul,
        add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    · -- p 1 = y
      have := (congrArg (fun q : E => q 1) hc0).symm
      simpa [a, b, z, y, b0, b1, b2, Fin.sum_univ_three, hbasis0, hbasis1, hbasis2, zsmul_eq_mul,
        add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    · -- p 2 = z
      have := (congrArg (fun q : E => q 2) hc0).symm
      simpa [a, b, z, b0, b1, b2, Fin.sum_univ_three, hbasis0, hbasis1, hbasis2, zsmul_eq_mul] using this
    · -- x ≡ u*z [ZMOD n]
      -- Use `Int.modEq_iff_dvd`: it suffices to show `(n:ℤ) ∣ u*z - x`.
      refine (Int.modEq_iff_dvd).2 ?_
      refine ⟨-a, ?_⟩
      -- `u*z - (n*a + u*z) = n*(-a)`.
      simp [x, sub_eq_add_neg, add_left_comm, add_comm]
    · -- y ≡ v*z [ZMOD n]
      refine (Int.modEq_iff_dvd).2 ?_
      refine ⟨-b, ?_⟩
      simp [y, sub_eq_add_neg, add_left_comm, add_comm]

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
  classical
  let B : Module.Basis (Fin 3) ℝ E := descent_basis n u v hn
  let F : Set E := ZSpan.fundamentalDomain B
  refine ⟨F, ?_, ?_⟩

  · -- Fundamental domain for the span lattice, then rewrite to `descent_lattice`.
    have hFD_span :
        IsAddFundamentalDomain ((Submodule.span ℤ (Set.range B)).toAddSubgroup) F volume := by
      simpa [F, B] using (ZSpan.isAddFundamentalDomain' B volume)
    -- `IsAddFundamentalDomain` is phrased over the *carrier type* `↥L`, so we cannot `cases` the lattice
    -- equality without running into dependent-elimination issues. Instead, transport the three fields
    -- (`ae_covers`, `aedisjoint`) across the membership equivalence induced by `descent_lattice_eq_zspan`.
    let L1 : AddSubgroup E := descent_lattice n u v
    let L2 : AddSubgroup E := (Submodule.span ℤ (Set.range B)).toAddSubgroup
    have hmem : ∀ p : E, p ∈ L1 ↔ p ∈ L2 := by
      intro p
      -- Use the proven equality on membership (prop-level rewriting is safe).
      simpa [L1, L2] using congrArg (fun (L : AddSubgroup E) => p ∈ L)
        (descent_lattice_eq_zspan (n := n) (u := u) (v := v) hn)
    -- Build the fundamental-domain structure for `L1` by transporting the three fields.
    refine ⟨hFD_span.nullMeasurableSet, ?_, ?_⟩
    · -- `ae_covers`
      refine hFD_span.ae_covers.mono ?_
      intro x hx
      rcases hx with ⟨g2, hg2⟩
      refine ⟨⟨g2.1, (hmem g2.1).2 g2.2⟩, ?_⟩
      simpa using hg2
    · -- `aedisjoint`
      intro g1 g2 hne
      let g1' : L2 := ⟨g1.1, (hmem g1.1).1 g1.2⟩
      let g2' : L2 := ⟨g2.1, (hmem g2.1).1 g2.2⟩
      have hne' : g1' ≠ g2' := by
        intro h
        apply hne
        apply Subtype.ext
        simpa [g1', g2'] using congrArg Subtype.val h
      -- `g +ᵥ F` depends only on the underlying `E` element, so we can reuse the `L2` proof.
      simpa [g1', g2'] using (hFD_span.aedisjoint (i := g1') (j := g2') hne')

  · -- Volume computation: `volume F = ofReal |det (Matrix.of B)| = n^2`.
    have hvol :
        volume F = ENNReal.ofReal |(Matrix.of B).det| := by
      simp [F, B]

    -- The matrix used to define `descent_basis` (see `descent_basis` docstring).
    let A : Matrix (Fin 3) (Fin 3) ℝ :=
      !![(n : ℝ), 0, (u : ℝ);
        0, (n : ℝ), (v : ℝ);
        0, 0, (1 : ℝ)]

    have hB : Matrix.of B = Aᵀ := by
      ext i j
      -- `Matrix.of` treats basis vectors as rows; for a mapped `Pi.basisFun` basis this gives a transpose.
      simp [B, descent_basis, A, Module.Basis.map_apply, Matrix.toLinearEquiv, Matrix.of_apply,
        Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Pi.basisFun_apply, Matrix.transpose_apply]

    have hdetA : A.det = (n ^ 2 : ℝ) := by
      -- Upper triangular, so det is `n*n*1`.
      simp [A, Matrix.det_fin_three, pow_two]

    have hdetB : (Matrix.of B).det = (n ^ 2 : ℝ) := by
      calc
        (Matrix.of B).det = (Aᵀ).det := by simp [hB]
        _ = A.det := by simp
        _ = (n ^ 2 : ℝ) := hdetA

    have hnonneg : 0 ≤ (n ^ 2 : ℝ) := by
      nlinarith

    calc
      volume F = ENNReal.ofReal |(Matrix.of B).det| := hvol
      _ = ENNReal.ofReal (n ^ 2 : ℝ) := by simp [hdetB, abs_of_nonneg hnonneg]
      _ = (n ^ 2 : ℝ≥0∞) := by simp [ENNReal.ofReal_natCast]

/-- For odd `n`, there exist `u, v` such that `u^2 + v^2 + 1 ≡ 0 [ZMOD n]`.

This is the “local solvability” input needed by `mem_descent_lattice_norm_sq_mod`.

We *do not* reprove this here: the lemma is already available in this repo (see `Core/ModularSquares`)
and we re-export it under a name that matches this file’s narrative.
-/
lemma exists_sq_add_sq_add_one_eq_zero_mod_odd' (n : ℕ) (hn : Odd n) :
    ∃ u v : ℤ, u^2 + v^2 + 1 ≡ 0 [ZMOD n] := by
  simpa using GeometryOfNumbers.exists_sq_add_sq_add_one_eq_zero_mod_odd n hn

/-- Every integer `n ≡ 3 (mod 8)` is a sum of three squares.

This file’s Minkowski route is still a scaffold; the fully worked proof lives in
`GeometryOfNumbers/Legendre/Ankeny.lean`. We provide this lemma as an alias to avoid duplicating an
unfinished proof in this file.
-/
theorem minkowski_sum_three_squares_of_three_mod_eight (n : ℕ) (hn : n % 8 = 3) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n :=
  GeometryOfNumbers.sum_three_squares_of_three_mod_eight n hn

/-- Main theorem (target statement): every `n` not of the form \(4^a(8b+7)\) is a sum of 3 squares.

This file currently does not complete the proof; the completed proof route is in `Legendre/Ankeny.lean`.
-/
theorem minkowski_three_squares (n : ℕ) (_h : ¬ is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  -- Delegate to the canonical proof route in `Legendre/Main.lean`.
  simpa using GeometryOfNumbers.sum_three_squares_of_not_exception n _h

end GeometryOfNumbers