import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Basis.Submodule
import PolygonalNumberTheorem.Legendre.Exceptions

namespace PolygonalNumberTheorem

open MeasureTheory MeasureTheory.Measure Set WithLp Module
open scoped NNReal ENNReal

abbrev E := (Fin 3 → ℝ)

/-- The lattice of integer points `(x, y, z)` in `ℝ³` satisfying:

* `x ≡ u * z [ZMOD n]`
* `y ≡ v * z [ZMOD n]`
-/
noncomputable def descent_basis (n : ℕ) (u v : ℤ) (hn : 0 < n) :
    Module.Basis (Fin 3) ℝ E :=
  let b0 : Module.Basis (Fin 3) ℝ E := Pi.basisFun ℝ (Fin 3)
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    !![(n : ℝ), 0, (u : ℝ);
      0, (n : ℝ), (v : ℝ);
      0, 0, (1 : ℝ)]
  have hdet : A.det ≠ 0 := by
    have hdet' : A.det = (n : ℝ) * (n : ℝ) := by
      classical
      simp [A, Matrix.det_fin_three]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have : (n : ℝ) * (n : ℝ) ≠ 0 := mul_ne_zero hnR hnR
    simpa [hdet'] using this
  have hA : IsUnit A.det := by
    simpa [isUnit_iff_ne_zero] using hdet
  b0.map (Matrix.toLinearEquiv b0 A hA)

noncomputable def descent_lattice (n : ℕ) (u v : ℤ) (hn : 0 < n) :
    AddSubgroup E :=
  (Submodule.span ℤ (Set.range (descent_basis n u v hn))).toAddSubgroup

/-- The volume of the fundamental domain of the descent lattice. -/
lemma descent_lattice_covolume (n : ℕ) (u v : ℤ) (hn : 0 < n) :
    ∃ F : Set E,
      IsAddFundamentalDomain (descent_lattice n u v hn) F volume ∧
      volume F = (n ^ 2 : ℝ≥0∞) := by
  classical
  let b : Module.Basis (Fin 3) ℝ E := descent_basis n u v hn
  let F : Set E := ZSpan.fundamentalDomain b
  have hfund : IsAddFundamentalDomain (descent_lattice n u v hn) F volume := by
    simpa [descent_lattice, b, F] using (ZSpan.isAddFundamentalDomain' (b := b) (μ := volume))
  have hvol : volume F = (n ^ 2 : ℝ≥0∞) := by
    have hbase :
        volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal |(Matrix.of b).det| := by
      simpa using (ZSpan.volume_fundamentalDomain (b := b))
    -- TODO: Prove this determinant computation cleanly.
    sorry
  exact ⟨F, hfund, hvol⟩

/-- Characterize the descent lattice as explicit integer combinations of columns. -/
lemma mem_descent_lattice_iff (n : ℕ) (u v : ℤ) (hn : 0 < n) (p : Fin 3 → ℤ) :
    (fun i => (p i : ℝ)) ∈ descent_lattice n u v hn ↔
    ∃ a b c : ℤ, (p 0 : ℤ) = a * n + c * u ∧
                 (p 1 : ℤ) = b * n + c * v ∧
                 (p 2 : ℤ) = c := by
  sorry

/-- A point in the descent lattice satisfies the congruence condition mod n. -/
lemma mem_descent_lattice_norm_sq_mod (n : ℕ) (u v : ℤ) (p : Fin 3 → ℤ)
    (hn : 0 < n)
    (hp : (fun i => (p i : ℝ)) ∈ descent_lattice n u v hn)
    (h_local : u^2 + v^2 + 1 ≡ 0 [ZMOD n]) :
    (p 0)^2 + (p 1)^2 + (p 2)^2 ≡ 0 [ZMOD n] := by
  sorry

theorem exists_three_squares_via_minkowski (n : ℕ) (u v : ℤ) (hn : 0 < n)
    (h_local : u^2 + v^2 + 1 ≡ 0 [ZMOD n]) :
    ∃ (p : Fin 3 → ℤ), (p 0)^2 + (p 1)^2 + (p 2)^2 = n := by
  sorry

theorem odd_not_seven_mod_eight_is_sum_three_squares (n : ℕ) (hn_odd : Odd n)
    (hn_not7 : n % 8 ≠ 7) : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  sorry

theorem two_mod_four_is_sum_three_squares (n : ℕ) (hn : n % 4 = 2) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  sorry

/-- Main theorem via Minkowski: every n not of the form 4^a(8k+7) is sum of 3 squares. -/
theorem minkowski_three_squares (n : ℕ) (h : ¬ Nat.is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  sorry

end PolygonalNumberTheorem
