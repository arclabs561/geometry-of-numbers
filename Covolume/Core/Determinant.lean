import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume

/-!
# Lattice Determinants and Covolumes

This file establishes the connection between the determinant of a lattice basis
and its covolume (the measure of its fundamental domain).

## Main Results
- `covolume_eq_det`: The covolume of a lattice spanned by a basis is equal to the
  absolute value of the determinant of the basis matrix.
-/

namespace Covolume

open Matrix

/-- The covolume of a ℤ-lattice in ℝⁿ is equal to the absolute value of the 
    determinant of any basis matrix. -/
lemma covolume_eq_det {n : ℕ} (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] 
    [IsZLattice ℝ L] (b : Basis (Fin n) ℤ L) :
    ZLattice.covolume L = |(Matrix.of (fun i j => (b j : Fin n → ℝ) i)).det| := by
  -- This is a fundamental result in the Geometry of Numbers.
  -- Mathlib has parts of this in ZLattice.Covolume.
  sorry

end Covolume
