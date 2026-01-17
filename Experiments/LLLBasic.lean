import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# LLL Basic Experiment

Probing Mathlib's `gram_schmidt` and basis handling to prepare for
the LLL algorithm implementation.
-/

namespace Covolume.Experiments

open Matrix

/-- A simple 2D basis to test Gram-Schmidt. -/
def basis2d : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

/-- The Gram-Schmidt orthogonalization of basis2d. -/
noncomputable def ortho2d := 
  gramSchmidt ℝ (fun i => basis2d i)

#check ortho2d

/-- In 2D, if we have [1, 1] and [0, 1], the GS basis should be [1, 1] and [-1/2, 1/2]?
    Wait, GS depends on the inner product. 
    Standard GS:
    u1 = v1 = [1, 1]
    u2 = v2 - proj_u1(v2) = [0, 1] - ([0,1]·[1,1] / [1,1]·[1,1]) * [1,1]
       = [0, 1] - (1/2)*[1,1] = [-1/2, 1/2]
-/

end Covolume.Experiments
