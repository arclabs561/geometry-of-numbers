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
  -- 1. Combine congruences mod 4 and mod n via CRT.
  -- 2. Check gcd(target, 4n) = 1.
  -- 3. Apply Dirichlet's theorem.
  sorry

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
