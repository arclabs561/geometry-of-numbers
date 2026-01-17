import Mathlib.Data.Nat.Basic

namespace Covolume

/-!
# Three-Square Exceptions

This file defines the set of integers that cannot be represented as a sum of three squares.

## Mathematical Definition
A positive integer \(n\) is a three-square exception if and only if it is of the form \(4^a(8k + 7)\) for some integers \(a, k \ge 0\).
-/

def is_three_square_exception (n : ℕ) : Prop :=
  ∃ a k : ℕ, n = 4 ^ a * (8 * k + 7)

end Covolume

