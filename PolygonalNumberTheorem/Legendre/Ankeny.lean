import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import PolygonalNumberTheorem.Legendre.Exceptions
import PolygonalNumberTheorem.Legendre.AnkenyLemmas

/-!
# Ankeny's 1957 Proof of Legendre's Three-Squares Theorem

This file implements Ankeny's elementary proof of Legendre's three-squares theorem
using Minkowski's theorem and Dirichlet's theorem on primes in arithmetic progressions.
The proof focuses on the case `n ≡ 3 (mod 8)`, which is the core case for the
Polygonal Number Theorem.
-/

namespace PolygonalNumberTheorem

open MeasureTheory MeasureTheory.Measure Set Module Matrix
open scoped NNReal ENNReal BigOperators Matrix

/-- Existence of the Ankeny prime `q`.
    For `n ≡ 3 (mod 8)`, there exists a prime `q ≡ 1 (mod 4)` such that `q ≡ -1/2 (mod n)`. -/
lemma exists_ankeny_prime (n : ℕ) (hn : n % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ (q : ZMod n) = - (2 : ZMod n)⁻¹ := by
  have hn_odd : n % 2 = 1 := by omega
  let h4n := coprime_four_n n hn_odd
  let a4 : ZMod 4 := 1
  let an : ZMod n := - (2 : ZMod n)⁻¹
  obtain ⟨a, ha⟩ := (ZMod.chineseRemainder h4n).surjective (a4, an)
  
  have h_unit : IsUnit a := by
    have hu2 : IsUnit (2 : ZMod n) := isUnit_two_zmod n hn_odd
    have hu2inv : IsUnit ((2 : ZMod n)⁻¹) := by
      -- `ZMod` has a total `Inv`, but for units we can certify `a⁻¹` is a unit using the
      -- characteristic lemmas `inv_mul_of_unit` / `mul_inv_of_unit`.
      refine (isUnit_iff_exists_inv).2 ?_
      exact ⟨(2 : ZMod n), (ZMod.inv_mul_of_unit (2 : ZMod n) hu2)⟩
    have hun : IsUnit an := by
      dsimp [an]
      exact IsUnit.neg hu2inv
    have : IsUnit ((ZMod.chineseRemainder h4n) a) := by
      -- Transport to `ZMod 4 × ZMod n` via `ha`, then use `Prod.isUnit_iff`.
      -- `ha : chineseRemainder a = (a4, an)`
      -- so it suffices to show `IsUnit (a4, an)`.
      -- (Then `a4 = 1` and `an` is a unit because `2` is a unit mod odd `n`.)
      rw [ha, Prod.isUnit_iff]
      exact ⟨by simpa [a4], hun⟩
    -- Pull `IsUnit` back across the ring equivalence.
    exact (MulEquiv.isUnit_map (f := (ZMod.chineseRemainder h4n)) (x := a)).1 this
  
  let m := a.val
  have h_nz : 4 * n ≠ 0 := by omega
  haveI : NeZero (4 * n) := ⟨h_nz⟩
  have h_m : (m : ZMod (4 * n)) = a := by
    rw [ZMod.natCast_val, show (ZMod.cast : ZMod (4 * n) → ZMod (4 * n)) = id from ZMod.cast_id']
    rfl
  have hm_unit : IsUnit (m : ZMod (4 * n)) := h_m.symm ▸ h_unit
  
  obtain ⟨q, hqp, hq_mod⟩ := (Nat.infinite_setOf_prime_and_eq_mod hm_unit).nonempty
  use q
  constructor; · exact hqp
  
  have hq_a : (q : ZMod (4 * n)) = a := hq_mod.trans h_m
  constructor
  · -- q % 4 = 1
    have h_comp_fst :
        ∀ x : ZMod (4 * n),
          ZMod.castHom (dvd_mul_right 4 n) (ZMod 4) x = (ZMod.chineseRemainder h4n x).1 := by
      intro x
      -- `ZMod.chineseRemainder` maps via `castHom` into the product; `fst` recovers the mod-4 cast.
      simp [ZMod.chineseRemainder, ZMod.castHom_apply]
    let f : ZMod (4 * n) →+* ZMod 4 := ZMod.castHom (dvd_mul_right 4 n) (ZMod 4)
    have ha1 : (ZMod.chineseRemainder h4n a).1 = a4 := by
      -- `ha : chineseRemainder a = (a4, an)`
      simpa using congrArg Prod.fst ha
    have hfa : f a = a4 := by
      simpa [f] using (h_comp_fst a).trans ha1
    have hq4z : (q : ZMod 4) = a4 := by
      have hq4' : f (q : ZMod (4 * n)) = f a := congrArg f hq_a
      -- `f` on a natural cast is just the natural cast in `ZMod 4`.
      simpa [f, ZMod.castHom_apply, ZMod.cast_natCast (h := dvd_mul_right 4 n), hfa] using hq4'
    have : q % 4 = 1 := by
      have hval : (q : ZMod 4).val = (a4 : ZMod 4).val := congrArg ZMod.val hq4z
      -- Fix the argument order: `ZMod.val_natCast 4 q`.
      simpa [a4, ZMod.val_natCast] using hval
    exact this
  · -- q ≡ -1/2 mod n
    have h_comp_snd :
        ∀ x : ZMod (4 * n),
          ZMod.castHom (dvd_mul_left n 4) (ZMod n) x = (ZMod.chineseRemainder h4n x).2 := by
      intro x
      simp [ZMod.chineseRemainder, ZMod.castHom_apply]
    let f : ZMod (4 * n) →+* ZMod n := ZMod.castHom (dvd_mul_left n 4) (ZMod n)
    have ha2 : (ZMod.chineseRemainder h4n a).2 = an := by
      simpa using congrArg Prod.snd ha
    have hfa : f a = an := by
      simpa [f] using (h_comp_snd a).trans ha2
    have hqn : (q : ZMod n) = an := by
      have hqn' : f (q : ZMod (4 * n)) = f a := congrArg f hq_a
      simpa [f, ZMod.castHom_apply, ZMod.cast_natCast (h := dvd_mul_left n 4), hfa] using hqn'
    exact hqn

/-- Existence of `b` such that `b² ≡ -n (mod 4q)`. -/
lemma exists_ankeny_b (n q : ℕ) (hn : n % 8 = 3) (hq : Nat.Prime q) (hq1 : q % 4 = 1)
    (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) :
    ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (4 * q)] := by
  -- 1. Show (-n/q) = 1 using quadratic reciprocity.
  -- 2. Lift solution mod q to mod 4q.
  sorry

/-- The Ankeny lattice `L = { (x,y,z) : x ≡ y (mod n), y ≡ bz (mod 2q) }`. -/
def ankeny_lattice (n q : ℕ) (b : ℤ) : AddSubgroup (Fin 3 → ℝ) where
  carrier := { p | ∃ x y z : ℤ, p 0 = x ∧ p 1 = y ∧ p 2 = z ∧
                                x ≡ y [ZMOD n] ∧ y ≡ b * z [ZMOD (2 * q)] }
  add_mem' := by
    rintro _ _ ⟨x1, y1, z1, hx1, hy1, hz1, hmod1x, hmod1y⟩ ⟨x2, y2, z2, hx2, hy2, hz2, hmod2x, hmod2y⟩
    use x1 + x2, y1 + y2, z1 + z2
    constructor; · simp [hx1, hx2]
    constructor; · simp [hy1, hy2]
    constructor; · simp [hz1, hz2]
    constructor
    · exact hmod1x.add hmod2x
    · rw [mul_add]; exact hmod1y.add hmod2y
  zero_mem' := by
    use 0, 0, 0
    simp
  neg_mem' := by
    rintro _ ⟨x, y, z, hx, hy, hz, hmodx, hmody⟩
    use -x, -y, -z
    constructor; · simp [hx]
    constructor; · simp [hy]
    constructor; · simp [hz]
    constructor
    · exact hmodx.neg
    · rw [mul_neg]; exact hmody.neg

/-- Covolume of the Ankeny lattice is `2nq`. -/
lemma ankeny_lattice_covolume (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    ∃ F : Set (Fin 3 → ℝ),
      IsAddFundamentalDomain (ankeny_lattice n q b) F volume ∧
      volume F = (2 * n * q : ℝ≥0∞) := by
  -- Construct basis and use ZSpan.isAddFundamentalDomain.
  sorry

/-- The quadratic form `Q = 2qx² + y² + nz²`. -/
def ankeny_Q (n q : ℕ) (x y z : ℤ) : ℤ :=
  2 * q * x^2 + y^2 + n * z^2

/-- Any point in the Ankeny lattice satisfies `Q ≡ 0 (mod 2nq)`. -/
lemma ankeny_Q_mod (n q : ℕ) (b : ℤ) (x y z : ℤ)
    (h_lat : (fun i => match i with | 0 => (x:ℝ) | 1 => (y:ℝ) | 2 => (z:ℝ)) ∈ ankeny_lattice n q b)
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (2 * q)]) :
    (ankeny_Q n q x y z) ≡ 0 [ZMOD (2 * n * q)] := by
  -- Proof:
  -- Q ≡ -x^2 + y^2 ≡ 0 (mod n)
  -- Q ≡ (bz)^2 + nz^2 ≡ 0 (mod 2q)
  sorry

/-- Minkowski application: there exists a representation `2qx² + y² + nz² = 2nq`. -/
lemma exists_ankeny_representation (n q : ℕ) (b : ℤ) (hn : n % 8 = 3) (hq : Nat.Prime q)
    (hq1 : q % 4 = 1) (hb : b^2 ≡ - (n : ℤ) [ZMOD (4 * q)]) :
    ∃ x y z : ℤ, 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q ∧ (x, y, z) ≠ 0 := by
  -- 1. Ellipsoid E with volume > 8 * covolume.
  -- 2. Minkowski point.
  -- 3. Q is divisible by 2nq and 0 < Q < 4nq => Q = 2nq.
  sorry

/-- Reduction of `2qx² + y² + nz² = 2nq` to `n = x² + u² + v²`. -/
lemma reduction_to_sum_three_squares (n q : ℕ) (x y z : ℤ)
    (h_ankeny : 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q)
    (hq : Nat.Prime q) (hq1 : q % 4 = 1) :
    ∃ u v : ℤ, n = x^2 + u^2 + v^2 := by
  -- Use Sum of Two Squares theorem on (y² + nz²)/(2q).
  sorry

/-- Final theorem for `n ≡ 3 (mod 8)`. -/
theorem sum_three_squares_of_three_mod_eight (n : ℕ) (hn : n % 8 = 3) :
    ∃ x y z : ℕ, x^2 + y^2 + z^2 = n := by
  -- 1. Assume n square-free (wlog).
  -- 2. Find q, b.
  -- 3. Find x, y, z.
  -- 4. Reduce.
  sorry

end PolygonalNumberTheorem
