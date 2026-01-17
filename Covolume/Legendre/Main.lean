import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import Covolume.Legendre.Exceptions
import Covolume.Legendre.Ankeny

namespace Covolume

/-- Necessary condition: representation as a sum of three squares implies n is not an exception. -/
theorem not_exception_of_sum_three_squares (n : ℕ) (h : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) :
    ¬ is_three_square_exception n := by
  sorry

/-- Sufficient condition: n not an exception implies representation as a sum of three squares. -/
theorem sum_three_squares_of_not_exception (n : ℕ) (h : ¬ is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  sorry

end Covolume
