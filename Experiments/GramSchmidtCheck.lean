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
lemma mu10_check : gram_schmidt_projections basis2d 1 0 ≥ 0 := by
  -- Just checking it builds and runs
  dsimp [gram_schmidt_projections]
  sorry

end Covolume.Experiments
