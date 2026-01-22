import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Quadratic Forms and Lattices

This file defines the `QuadraticLattice` interface, which connects abstract quadratic forms over the integers to the geometric properties of lattices in Euclidean space.

## Implementation Details
1.  **Lattice Embedding**: A method for representing quadratic form values as lattice norms.
2.  **Geometric Reduction**: Provision for utilizing Minkowski's Convex Body Theorem in representation problems.
3.  **Volume Invariants**: Definitions linking the covolume of the lattice to the fundamental domain measure.
-/

namespace GeometryOfNumbers
/-- A bridge between a quadratic form and its geometric lattice representation. -/
structure QuadraticLattice (n : ℕ) (Q : QuadraticForm ℤ (Fin n → ℤ)) where
  /-- The geometric lattice in ℝⁿ. -/
  lattice : Submodule ℤ (Fin n → ℝ)
  /-- Proof that the submodule has discrete topology. -/
  discrete : DiscreteTopology lattice
  /-- Proof that it is a full-rank discrete subgroup. -/
  is_lattice : IsZLattice ℝ lattice
  /-- An explicit embedding of integer coordinates into the lattice ambient space. -/
  embed : (Fin n → ℤ) → (Fin n → ℝ)
  /-- The embedding lands in the lattice. -/
  embed_mem : ∀ (v : Fin n → ℤ), embed v ∈ lattice
  /-- The norm-squared of the embedded vector matches the quadratic form value. -/
  norm_sq_eq : ∀ (v : Fin n → ℤ), ‖embed v‖^2 = (Q v : ℝ)

attribute [instance] QuadraticLattice.discrete
attribute [instance] QuadraticLattice.is_lattice

/-- The covolume of the underlying ℤ-lattice (as a real number). -/
noncomputable def QuadraticLattice.covolume {n : ℕ} {Q : QuadraticForm ℤ (Fin n → ℤ)}
    (L : QuadraticLattice n Q) : ℝ :=
  ZLattice.covolume L.lattice

end GeometryOfNumbers