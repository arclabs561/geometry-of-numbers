import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Field.Pointwise

/-!
# Successive Minima

This file defines the successive minima of a lattice with respect to a symmetric convex body.
This is a foundational concept in the Geometry of Numbers, bridging the gap between
the shortest vector problem and Minkowski's Second Theorem.

## Definitions
- `successive_minima L K k`: The k-th successive minimum of lattice L with respect to body K.
  It is defined as the infimum of λ > 0 such that λK contains k linearly independent points of L.

## Missing Infrastructure in Mathlib
Currently, Mathlib4 lacks a formalization of successive minima. This module targets
that gap as part of the Covolume library's infrastructure play.
-/

namespace Covolume

open Set Pointwise

/-- The k-th successive minimum of a lattice with respect to a symmetric convex body. -/
noncomputable def successive_minima {n : ℕ} (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] 
    (K : Set (Fin n → ℝ)) (k : ℕ) : ℝ :=
  if 1 ≤ k ∧ k ≤ n then
    sInf { r | 0 < r ∧ ∃ (s : Set (Fin n → ℝ)), (∀ x ∈ s, x ∈ L) ∧ s.Countable ∧ 
      LinearIndependent ℝ (fun (x : s) => (x : Fin n → ℝ)) ∧ s.ncard = k ∧ ∀ x ∈ s, x ∈ r • K }
  else 0

/-- Minkowski's First Theorem phrased in terms of the first successive minimum λ₁.
    λ₁^n * volume(K) ≤ 2^n * covolume(L). -/
lemma minkowski_first_theorem_minima {n : ℕ} (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L]
    (K : Set (Fin n → ℝ)) [IsZLattice ℝ L] (hK_conv : Convex ℝ K) (hK_symm : ∀ x ∈ K, -x ∈ K) 
    (hK_vol : 0 < MeasureTheory.volume K) :
    (successive_minima L K 1)^n * (MeasureTheory.volume K).toReal ≤ 2^n * (ZLattice.covolume L) :=
  sorry

/-- The successive minima are non-decreasing: λ₁ ≤ λ₂ ≤ ... ≤ λₙ. -/
lemma successive_minima_mono {n : ℕ} (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L]
    (K : Set (Fin n → ℝ)) (i j : ℕ) (hij : i ≤ j) (hi : 1 ≤ i) (hj : j ≤ n) :
    successive_minima L K i ≤ successive_minima L K j :=
  sorry

end Covolume
