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
/-!
This file used to include a placeholder lemma about `successive_minima` for the ℤ² lattice.

The intended next step (when we return to successive minima infrastructure) is:
- obtain a convenient `DiscreteTopology` / `ZLattice` instance for `lattice_z2`,
- compute (or at least bound) `successive_minima lattice_z2 unit_disk 1`.

We keep the definitions here, but avoid a `sorry` so the experiments folder stays tidy.
-/

end Covolume.Experiments
