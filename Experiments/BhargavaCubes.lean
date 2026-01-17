import Covolume.Core.Composition
import Mathlib.Tactic

/-!
# Bhargava Cube Experiment

Verifying that the three slice quadratic forms of a cube have the same discriminant.
-/

namespace Covolume.Experiments

open Composition

/-- A specific integer cube to test. -/
def test_cube : IntegerCube :=
  fun i j k => 
    match i, j, k with
    | 0, 0, 0 => 1
    | 0, 0, 1 => 0
    | 0, 1, 0 => 0
    | 0, 1, 1 => 1
    | 1, 0, 0 => 0
    | 1, 0, 1 => 1
    | 1, 1, 0 => 1
    | 1, 1, 1 => 0

/-- Calculate the discriminant of a binary quadratic form directly. -/
def bqf_disc (a b c : ℤ) : ℤ := b^2 - 4 * a * c

-- Further experiments will follow here once discriminant extraction is implemented.

end Covolume.Experiments
