import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import PolygonalNumberTheorem.TernaryQF
import PolygonalNumberTheorem.SumThreeSquares

/-!
# Minkowski's Approach to Legendre's Three-Square Theorem

This file develops the geometry-of-numbers approach to proving the hard direction
of Legendre's three-square theorem.
-/

namespace PolygonalNumberTheorem

open MeasureTheory MeasureTheory.Measure Set WithLp
open scoped NNReal ENNReal

/-- The lattice of integer points `(x, y, z)` in `ℝ³` satisfying:

* `x ≡ u * z [ZMOD n]`
* `y ≡ v * z [ZMOD n]`
-/
def descent_lattice (n : ℕ) (u v : ℤ) : AddSubgroup (EuclideanSpace ℝ (Fin 3)) where
  carrier := { p | ∃ (x y z : ℤ), p = !₂[(x : ℝ), (y : ℝ), (z : ℝ)] ∧ x ≡ u * z [ZMOD n] ∧ y ≡ v * z [ZMOD n] }
  add_mem' := by
    sorry
  zero_mem' := by
    sorry
  neg_mem' := by
    sorry

/-- The volume of the fundamental domain of the descent lattice. -/
lemma descent_lattice_covolume (n : ℕ) (u v : ℤ) :
    ∃ F : Set (EuclideanSpace ℝ (Fin 3)), IsAddFundamentalDomain (descent_lattice n u v) F volume ∧ volume F = (n ^ 2 : ℝ≥0∞) := by
  sorry

/-- A point in the descent lattice satisfies the congruence condition mod n. -/
lemma mem_descent_lattice_norm_sq_mod (n : ℕ) (u v : ℤ) (p : Fin 3 → ℤ)
    (hp : !₂[(p 0 : ℝ), (p 1 : ℝ), (p 2 : ℝ)] ∈ descent_lattice n u v)
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
