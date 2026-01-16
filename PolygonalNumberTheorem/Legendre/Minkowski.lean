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
import PolygonalNumberTheorem.Legendre.Exceptions

/-!
# Minkowski Descent for Legendre's Three-Squares Theorem

This file implements the "hard direction" of Legendre's three-squares theorem
specifically for the case `n ≡ 3 (mod 8)`, which is the case required for
Fermat's Polygonal Number Theorem.
-/

namespace PolygonalNumberTheorem

open MeasureTheory MeasureTheory.Measure Set WithLp Module
open scoped NNReal ENNReal BigOperators

abbrev E := (Fin 3 → ℝ)

/-- The basis for the descent lattice. -/
noncomputable def descent_basis (n : ℕ) (u v : ℤ) (hn : 0 < n) :
    Module.Basis (Fin 3) ℝ E :=
  let b0 : Module.Basis (Fin 3) ℝ E := Pi.basisFun ℝ (Fin 3)
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    !![(n : ℝ), 0, (u : ℝ);
      0, (n : ℝ), (v : ℝ);
      0, 0, (1 : ℝ)]
  have hdet : A.det ≠ 0 := by
    classical
    have h : A.det = (n : ℝ) * (n : ℝ) := by
      simp [A, Matrix.det_fin_three]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have h_nz : (n : ℝ) * (n : ℝ) ≠ 0 := mul_ne_zero hnR hnR
    rw [h]; exact h_nz
  have hA : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  b0.map (Matrix.toLinearEquiv b0 A hA)

/-- The lattice of points `(x, y, z)` in `ℝ³` satisfying congruences mod n. -/
def descent_lattice (n : ℕ) (u v : ℤ) : AddSubgroup E where
  carrier := { p | ∃ x y z : ℤ, p = (fun i => (match i with | 0 => x | 1 => y | 2 => z : ℝ)) ∧
                                x ≡ u * z [ZMOD n] ∧ y ≡ v * z [ZMOD n] }
  add_mem' := by
    rintro _ _ ⟨x1, y1, z1, rfl, hx1, hy1⟩ ⟨x2, y2, z2, rfl, hx2, hy2⟩
    use x1 + x2, y1 + y2, z1 + z2
    constructor
    · ext i; fin_cases i <;> simp
    · constructor
      · simp [hx1, hx2, mul_add]; exact Int.ModEq.add hx1 hx2
      · simp [hy1, hy2, mul_add]; exact Int.ModEq.add hy1 hy2
  zero_mem' := by
    use 0, 0, 0
    constructor
    · ext i; fin_cases i <;> simp
    · constructor <;> simp
  neg_mem' := by
    rintro _ ⟨x, y, z, rfl, hx, hy⟩
    use -x, -y, -z
    constructor
    · ext i; fin_cases i <;> simp
    · constructor
      · rw [mul_neg]; exact hx.neg
      · rw [mul_neg]; exact hy.neg

/-- Characterize the descent lattice as the Z-span of the basis. -/
lemma descent_lattice_eq_zspan (n : ℕ) (u v : ℤ) (hn : 0 < n) :
    descent_lattice n u v = (Submodule.span ℤ (Set.range (descent_basis n u v hn))).toAddSubgroup := by
  sorry

/-- A point in the descent lattice satisfies the congruence condition mod n. -/
lemma mem_descent_lattice_norm_sq_mod (n : ℕ) (u v : ℤ) (p : E)
    (hp : p ∈ descent_lattice n u v)
    (h_local : u^2 + v^2 + 1 ≡ 0 [ZMOD n]) :
    ∃ x y z : ℤ, p = (fun i => (match i with | 0 => x | 1 => y | 2 => z : ℝ)) ∧
                 x^2 + y^2 + z^2 ≡ 0 [ZMOD n] := by
  obtain ⟨x, y, z, rfl, hx, hy⟩ := hp
  use x, y, z, rfl
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

/-- Every odd integer `n` satisfies the modular root condition. -/
lemma exists_sq_add_sq_add_one_eq_zero_mod_odd (n : ℕ) (hn : Odd n) :
    ∃ u v : ℤ, u^2 + v^2 + 1 ≡ 0 [ZMOD n] := by
  sorry

/-- Every integer `n ≡ 3 (mod 8)` is a sum of three squares. -/
theorem sum_three_squares_of_three_mod_eight (n : ℕ) (hn : n % 8 = 3) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  sorry

/-- Main theorem via Minkowski: every n not of the form 4^a(8k+7) is sum of 3 squares. -/
theorem minkowski_three_squares (n : ℕ) (_h : ¬ Nat.is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  sorry

end PolygonalNumberTheorem
