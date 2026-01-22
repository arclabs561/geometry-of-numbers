import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.Field.Pointwise
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

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
that gap as part of this repo's infrastructure work.
-/

namespace GeometryOfNumbers
open Set Pointwise
open scoped BigOperators

/-- Witness predicate for the `k`-th successive minimum.

`r ∈ successive_minima_witnesses L K k` means: there exists a set `s` of `k` linearly independent
lattice points contained in the dilate `r • K`.
-/
noncomputable def successive_minima_witnesses {n : ℕ}
    (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L]
    (K : Set (Fin n → ℝ)) (k : ℕ) : Set ℝ :=
  { r | 0 < r ∧ ∃ (s : Set (Fin n → ℝ)), (∀ x ∈ s, x ∈ L) ∧ s.Countable ∧
      LinearIndependent ℝ (fun (x : s) => (x : Fin n → ℝ)) ∧ s.ncard = k ∧ ∀ x ∈ s, x ∈ r • K }

/-- The k-th successive minimum of a lattice with respect to a symmetric convex body. -/
noncomputable def successive_minima {n : ℕ} (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L]
    (K : Set (Fin n → ℝ)) (k : ℕ) : ℝ :=
  if _hk : 1 ≤ k ∧ k ≤ n then
    sInf (successive_minima_witnesses L K k)
  else 0

@[simp] lemma successive_minima_eq_zero_of_not_range {n : ℕ}
    (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] (K : Set (Fin n → ℝ)) (k : ℕ)
    (hk : ¬ (1 ≤ k ∧ k ≤ n)) :
    successive_minima L K k = 0 := by
  simp [successive_minima, hk]

lemma successive_minima_eq_sInf_of_range {n : ℕ}
    (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] (K : Set (Fin n → ℝ)) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ n) :
    successive_minima L K k =
      sInf (successive_minima_witnesses L K k) := by
  simp [successive_minima, hk, successive_minima_witnesses]

/-!
## Roadmap (no admitted theorems in this module)

This file intentionally contains **no** admitted theorems.

Next intended steps (once we commit to building this theory out) are to prove:

- a usable “λ₁ bound” lemma bridging to Minkowski’s convex-body theorem
- Minkowski’s second theorem (product bound) in terms of successive minima

Monotonicity in `k` (the first foundational lemma) is now in:

- `GeometryOfNumbers/Core/SuccessiveMinimaTheorems.lean`

Further theorems belong there as we harden statement shapes.

Note: analytic results like Siegel’s mean value theorem / Poisson summation belong in a separate
module (likely `Archive/` initially) once we decide how we want to represent the “space of lattices”
and the measure-theory interfaces in Lean.
-/

end GeometryOfNumbers