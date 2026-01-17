import Covolume.Core.SuccessiveMinima
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Successive Minima Experiment

Verifying the `successive_minima` definition for the standard integer lattice ℤ².
-/

namespace Covolume.Experiments

open Set

/-- Standard ℤ² lattice. -/
def lattice_z2 : Submodule ℤ (Fin 2 → ℝ) := 
  Submodule.span ℤ (range (Pi.basisFun ℝ (Fin 2)))

/-- The unit disk in ℝ². -/
def unit_disk : Set (Fin 2 → ℝ) := { v | ‖v‖ ≤ 1 }

/-- The first successive minimum of ℤ² wrt unit disk should be 1. -/
lemma lambda1_z2 [DiscreteTopology ↥lattice_z2] : successive_minima lattice_z2 unit_disk 1 ≥ 0 := by
  -- Placeholder: once we have a convenient `DiscreteTopology`/`IsZLattice` instance
  -- for `lattice_z2`, we can turn this into an actual computation check.
  --
  -- For now this file exists to keep the intended statement close to the definition.
  sorry

end Covolume.Experiments
