import GeometryOfNumbers.Core.Composition
import Mathlib.Tactic

/-!
# Bhargava Cube Experiment

Verifying on a concrete example that the three slice quadratic forms of a cube have the same discriminant.
-/

namespace GeometryOfNumbers.Experiments

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

-- Concrete sanity check: for `test_cube`, all three slice discriminants agree.
example : discriminant (slice_bqf test_cube 0) = discriminant (slice_bqf test_cube 1) := by
  native_decide

example : discriminant (slice_bqf test_cube 1) = discriminant (slice_bqf test_cube 2) := by
  native_decide

end GeometryOfNumbers.Experiments
