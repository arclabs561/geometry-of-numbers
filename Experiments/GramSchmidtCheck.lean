import Covolume.Computable.LLL
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Gram-Schmidt Probing

Testing the `gram_schmidt_projections` definition.
-/

namespace Covolume.Experiments

open Computable

/-- A simple 2D basis to test Gram-Schmidt. -/
noncomputable def basis2d : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

/-- Projection μ_{1,0} should be 1/2. -/
/-!
This file used to contain a placeholder lemma about `gram_schmidt_projections`.

The LLL implementation has since stabilized elsewhere; if we want executable checks here, prefer:
- a small `#eval`-style numeric sanity check in a separate (non-library) script, or
- a lemma stated in a form that can be proved without unfolding the full Gram–Schmidt stack.

We remove the unfinished lemma to keep `Experiments/` free of `sorry`.
-/

end Covolume.Experiments
