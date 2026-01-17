import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares
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
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Covolume.Legendre.Exceptions
import Covolume.Legendre.AnkenyLemmas

namespace Covolume

open MeasureTheory MeasureTheory.Measure Set Module Matrix
open scoped NNReal ENNReal BigOperators Matrix
open scoped NumberTheorySymbols

/-- Existence of the Ankeny prime `q`. -/
lemma exists_ankeny_prime (n : ℕ) (hn : n % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ (q : ZMod n) = - (2 : ZMod n)⁻¹ := by
  sorry

/-- Existence of `b` such that `b² ≡ -n (mod 4q)`. -/
lemma exists_ankeny_b (n q : ℕ) (hn : n % 8 = 3) (hq : Nat.Prime q) (hq1 : q % 4 = 1)
    (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) :
    ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (4 * q)] := by
  sorry

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

/-- A convenient full-rank ℤ-lattice for Ankeny has covolume `2nq`. -/
lemma ankeny_lattice_covolume (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    ∃ (L : AddSubgroup (Fin 3 → ℝ)) (F : Set (Fin 3 → ℝ)),
      IsAddFundamentalDomain L F volume ∧ 
      volume F = (2 * n * q : ℝ≥0∞) ∧ 
      (L : Set (Fin 3 → ℝ)).Countable ∧ 
      (L : Set (Fin 3 → ℝ)) ⊆ ankeny_lattice n q b := by
  sorry

/-- The quadratic form `Q = 2qx² + y² + nz²`. -/
def ankeny_Q (n q : ℕ) (x y z : ℤ) : ℤ := 2 * q * x^2 + y^2 + n * z^2

/-- Any point in the Ankeny lattice satisfies `Q ≡ 0 (mod 2nq)`. -/
lemma ankeny_Q_mod (n q : ℕ) (b : ℤ) (x y z : ℤ) (hn : n % 8 = 3) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) (h_lat : (fun i => match i with | 0 => (x:ℝ) | 1 => (y:ℝ) | 2 => (z:ℝ)) ∈ ankeny_lattice n q b) (hb : b^2 ≡ - (n : ℤ) [ZMOD (2 * q)]) : (ankeny_Q n q x y z) ≡ 0 [ZMOD (2 * n * q)] := by
  sorry

/-- Minkowski application: there exists a representation `2qx² + y² + nz² = 2nq`. -/
lemma exists_ankeny_representation (n q : ℕ) (b : ℤ) (hn : n % 8 = 3) (hq : Nat.Prime q)
    (hq1 : q % 4 = 1) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (4 * q)]) :
    ∃ x y z : ℤ, 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q ∧ (x, y, z) ≠ (0, 0, 0) := by
  sorry

/-- Reduction of `2qx² + y² + nz² = 2nq` to `n = x² + u² + v²`.
    Hypothesis `Squarefree n` makes the `p | n` case easier (contradiction via `z^2 ≡ -1`). -/
lemma reduction_to_sum_three_squares (n q : ℕ) (x y z : ℤ)
    (h_ankeny : 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q)
    (hq_prime : Nat.Prime q) (hq1 : q % 4 = 1) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) 
    (hn : n % 8 = 3) (hn_sq : Squarefree n) :
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
  
  -- Use Nat.eq_sq_add_sq_iff
  suffices ∃ u v : ℕ, K = u ^ 2 + v ^ 2 by
    obtain ⟨u, v, huv⟩ := this
    use (u : ℤ), (v : ℤ)
    sorry -- Setup descent induction

  rw [Nat.eq_sq_add_sq_iff]
  intro p hp_prime_factors hp_mod3
  sorry

/-- Final theorem for `n ≡ 3 (mod 8)`. -/
theorem sum_three_squares_of_three_mod_eight (n : ℕ) (hn : n % 8 = 3) :
    ∃ x y z : ℕ, x^2 + y^2 + z^2 = n := by
  obtain ⟨s, m, hm_eq, hm_sq⟩ := exists_squarefree_part n
  have hm_mod : m % 8 = 3 := squarefree_part_mod_eight n s m hm_eq hn
  obtain ⟨q, hqp, hq1, hq_mod⟩ := exists_ankeny_prime m hm_mod
  have : ∃ b : ℤ, b ^ 2 ≡ - (m : ℤ) [ZMOD (4 * q)] := exists_ankeny_b m q hm_mod hqp hq1 hq_mod
  obtain ⟨b, hb⟩ := this
  obtain ⟨x, y, z, h_rep, h_nz⟩ := exists_ankeny_representation m q b hm_mod hqp hq1 hq_mod hb
  obtain ⟨u, v, h_final⟩ := reduction_to_sum_three_squares m q x y z h_rep hqp hq1 hq_mod hm_mod hm_sq
  use s * x.natAbs, s * u.natAbs, s * v.natAbs
  zify
  -- Keep this simp list minimal to avoid unused-simp-arg warnings.
  simp only [mul_pow, ← mul_add, sq_abs]
  have hm_eq_int : (n : ℤ) = s^2 * m := by exact_mod_cast hm_eq
  rw [← h_final, ← hm_eq_int]
  -- `ring` was previously here, but the goal is already closed after rewriting.

end Covolume
