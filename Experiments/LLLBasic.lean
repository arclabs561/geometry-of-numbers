import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# LLL Basic Experiment

Probing Mathlib's `gram_schmidt` and basis handling to prepare for
the LLL algorithm implementation.
-/

namespace GeometryOfNumbers.Experiments

open Matrix

noncomputable section

/-- A simple 2D basis to test Gram-Schmidt. -/
def basis2d : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

-- `gramSchmidt` lives in `InnerProductSpace`; when we actually want to compute
-- with it here, we should move to `EuclideanSpace ℝ (Fin 2)` (or use `toLp 2`)
-- so the inner-product-space instances line up.
--
-- For now, keep this as a tiny “import + name lookup” experiment.
open InnerProductSpace

private def _probe_gramSchmidt := @InnerProductSpace.gramSchmidt

/- In 2D with the standard inner product:
   v1 = [1, 1], v2 = [0, 1]
   u1 = v1
   u2 = v2 - proj_{u1}(v2) = [-1/2, 1/2]
-/

end

end GeometryOfNumbers.Experiments
