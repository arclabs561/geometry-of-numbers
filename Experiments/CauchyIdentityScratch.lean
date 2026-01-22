import GeometryOfNumbers.Core.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Scratch space for the Cauchy polygonal-number reduction.

Goal: sanity-check the algebraic “spine” we intend to use in `GeometryOfNumbers/Cauchy/Main.lean`,
separately from any interval / inequality choices.

The key identity already lives in `GeometryOfNumbers/Core/Basic.lean`:

\[
  2\cdot\sum_{i=1}^4 P(s, x_i)
    = (s-2)\cdot\sum_{i=1}^4 x_i^2 + (4-s)\cdot\sum_{i=1}^4 x_i.
\]

What we actually need in the `cauchy_decomposition`-style proofs is the rearranged form:

\[
  (s-2)\cdot\sum x_i^2
    = 2\cdot\sum P(s,x_i) + (s-4)\cdot\sum x_i.
\]
-/

namespace Experiments

open GeometryOfNumbers

theorem cauchy_polygonal_identity_rearranged
    (s : ℕ) (hs : 3 ≤ s) (t u v w : ℕ) :
    let m : ℤ := (s : ℤ) - 2
    m * ((t : ℤ) ^ 2 + (u : ℤ) ^ 2 + (v : ℤ) ^ 2 + (w : ℤ) ^ 2) =
      (2 * (polygonal s t + polygonal s u + polygonal s v + polygonal s w) : ℤ)
        + ((m - 2) * ((t : ℤ) + (u : ℤ) + (v : ℤ) + (w : ℤ))) := by
  have h :=
    GeometryOfNumbers.cauchy_polygonal_identity (s := s) hs t u v w
  dsimp at h ⊢
  -- `h : 2*sumP = m*sumSq + (2-m)*sumLin`; rearrange via linear arithmetic in ℤ.
  linarith

/-- Unfolding check in a form that avoids division-by-2 bookkeeping.

`two_mul_polygonal` already encodes the “clear the /2” trick correctly, so we verify the
4-sum statement at the `2 * …` level.

This is the algebraic shape Nathanson uses before invoking Cauchy’s lemma. -/
theorem two_mul_sum_four_polygonal
    (s : ℕ) (t u v w : ℕ) :
    2 * (polygonal s t + polygonal s u + polygonal s v + polygonal s w)
      = 2 * (t + u + v + w) + (s - 2) * (t * (t - 1) + u * (u - 1) + v * (v - 1) + w * (w - 1)) := by
  have ht := GeometryOfNumbers.two_mul_polygonal s t
  have hu := GeometryOfNumbers.two_mul_polygonal s u
  have hv := GeometryOfNumbers.two_mul_polygonal s v
  have hw := GeometryOfNumbers.two_mul_polygonal s w
  -- Expand LHS and rewrite each `2 * polygonal` term.
  simp [Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] at *
  rw [ht, hu, hv, hw]
  ring

end Experiments

