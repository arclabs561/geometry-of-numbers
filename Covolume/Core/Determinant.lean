import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Basis.Defs
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
    [IsZLattice ℝ L] (b : Module.Basis (Fin n) ℤ L) :
    ZLattice.covolume L = |(Matrix.of (Subtype.val ∘ ⇑b)).det| := by
  -- This is available in Mathlib as `ZLattice.covolume_eq_det`.
  -- Our statement is just a specialization/unfolding for `Fin n → ℝ`.
  simpa using (ZLattice.covolume_eq_det (L := L) (b := b))

end Covolume
