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
  /-
  ESCAPE HATCH (current):
  This should be the “easy direction” of Legendre:
  \[
    x^2 + y^2 + z^2 = n \implies n \neq 4^a (8b+7).
  \]
  In Lean, this is mostly modular arithmetic + valuation facts:
  - squares mod 8 are in `{0,1,4}`,
  - if `n = 4^a (8b+7)` then `n ≡ 7 (mod 8)` after dividing out maximal powers of 4,
  - show a sum of three squares cannot be `≡ 7 (mod 8)`.

  TODO:
  - Factor the proof around a lemma `sum_three_squares_mod8_ne7`.
  - Use the existing predicate `is_three_square_exception` in `Exceptions.lean` as the canonical form.
  -/
  sorry

/-- Sufficient condition: n not an exception implies representation as a sum of three squares. -/
theorem sum_three_squares_of_not_exception (n : ℕ) (h : ¬ is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  /-
  ESCAPE HATCH (current):
  This is the “hard direction”. In this repo we route it through Ankeny’s descent pipeline:
  - reduce to the squarefree part `m` with `m % 8 = 3`,
  - choose `q` and `b`,
  - build the lattice, apply Minkowski, get `2*q*x^2 + y^2 + m*z^2 = 2*m*q`,
  - descend to `m = x^2 + u^2 + v^2`, then scale back to `n`.

  TODO:
  - Make this theorem a thin wrapper around `sum_three_squares_of_three_mod_eight` + squarefree-part glue.
  - Keep “Minkowski route” alternative in `Legendre/Minkowski.lean`, but treat Ankeny as canonical.
  -/
  sorry

end Covolume
