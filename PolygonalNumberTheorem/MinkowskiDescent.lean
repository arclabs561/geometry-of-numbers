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
    rintro _ _ ⟨x1, y1, z1, rfl, hx1, hy1⟩ ⟨x2, y2, z2, rfl, hx2, hy2⟩
    use x1 + x2, y1 + y2, z1 + z2
    constructor
    · ext i; fin_cases i <;> simp
    · constructor
      · rw [Int.add_mul]; exact hx1.add hx2
      · rw [Int.add_mul]; exact hy1.add hy2
  zero_mem' := by
    use 0, 0, 0
    simp
  neg_mem' := by
    rintro _ ⟨x, y, z, rfl, hx, hy⟩
    use -x, -y, -z
    constructor
    · ext i; fin_cases i <;> simp
    · constructor
      · rw [Int.neg_mul]; exact hx.neg
      · rw [Int.neg_mul]; exact hy.neg

/-- The volume of the fundamental domain of the descent lattice. -/
lemma descent_lattice_covolume (n : ℕ) (u v : ℤ) (hn : 0 < n) :
    ∃ F : Set (EuclideanSpace ℝ (Fin 3)), IsAddFundamentalDomain (descent_lattice n u v) F volume ∧ volume F = (n ^ 2 : ℝ≥0∞) := by
  -- We'll use the mapping from Z^3 to (Z/nZ)^2 given by (x,y,z) -> (x - uz, y - vz).
  -- The kernel is exactly the lattice points.
  -- The index is |(Z/nZ)^2| = n^2.
  sorry

/-- A point in the descent lattice satisfies the congruence condition mod n. -/
lemma mem_descent_lattice_norm_sq_mod (n : ℕ) (u v : ℤ) (p : Fin 3 → ℤ)
    (hp : !₂[(p 0 : ℝ), (p 1 : ℝ), (p 2 : ℝ)] ∈ descent_lattice n u v)
    (h_local : u^2 + v^2 + 1 ≡ 0 [ZMOD n]) :
    (p 0)^2 + (p 1)^2 + (p 2)^2 ≡ 0 [ZMOD n] := by
  rcases hp with ⟨x, y, z, heq, hx, hy⟩
  have h0 : p 0 = x := by 
    have : !₂[(p 0 : ℝ), (p 1 : ℝ), (p 2 : ℝ)] 0 = x := by rw [← heq]; simp
    simp at this; exact_mod_cast this
  have h1 : p 1 = y := by 
    have : !₂[(p 0 : ℝ), (p 1 : ℝ), (p 2 : ℝ)] 1 = y := by rw [← heq]; simp
    simp at this; exact_mod_cast this
  have h2 : p 2 = z := by 
    have : !₂[(p 0 : ℝ), (p 1 : ℝ), (p 2 : ℝ)] 2 = z := by rw [← heq]; simp
    simp at this; exact_mod_cast this
  rw [h0, h1, h2]
  calc (x^2 + y^2 + z^2 : ℤ)
    _ ≡ (u*z)^2 + (v*z)^2 + z^2 [ZMOD n] := by
        apply Int.ModEq.add
        · apply Int.ModEq.add
          · apply Int.ModEq.pow 2 hx
          · apply Int.ModEq.pow 2 hy
        · exact Int.ModEq.refl _
    _ = z^2 * (u^2 + v^2 + 1) := by ring
    _ ≡ z^2 * 0 [ZMOD n] := Int.ModEq.mul_left _ h_local
    _ = 0 := by ring

theorem exists_three_squares_via_minkowski (n : ℕ) (u v : ℤ) (hn : 0 < n)
    (h_local : u^2 + v^2 + 1 ≡ 0 [ZMOD n]) :
    ∃ (p : Fin 3 → ℤ), (p 0)^2 + (p 1)^2 + (p 2)^2 = n := by
  -- 1. Apply Minkowski's Theorem to a sphere of radius sqrt(2n).
  -- volume(Sphere(R)) = 4/3 * pi * R^3.
  -- R^2 = 2n => volume ≈ 11.85 n^(3/2).
  -- We need 11.85 n^(3/2) > 8 n^2 => 1.48 > sqrt(n) => n < 2.19.
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
