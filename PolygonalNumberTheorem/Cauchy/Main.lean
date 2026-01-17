import PolygonalNumberTheorem.Core.Basic
import PolygonalNumberTheorem.Legendre.Main
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Int.Cast.Field

open Nat Real
open BigOperators

namespace PolygonalNumberTheorem

/-- If a real interval has length `> 2`, it contains an odd integer. -/
lemma exists_odd_in_interval {L U : ℝ} (hLU : L + 2 < U) :
    ∃ b : ℤ, Odd b ∧ L < (b : ℝ) ∧ (b : ℝ) < U := by
  sorry

/-- Gauss’s Eureka theorem: every natural number is a sum of three triangular numbers. -/
theorem gauss_eureka (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n := by
  sorry

/-- Fermat's Polygonal Number Theorem. -/
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  rcases hs with h_s3 | h_s4 | h_s5
  · -- s = 3: Gauss's Eureka theorem.
    obtain ⟨a, b, c, habc⟩ := gauss_eureka n
    use ![a, b, c]
    dsimp [triangular] at habc
    -- The sum over Fin 3 needs to match Triangular sum
    sorry
  · -- s = 4: Lagrange's Four-Square Theorem.
    obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares n
    use ![a, b, c, d]
    -- The sum over Fin 4 needs to match Square sum
    sorry
  · -- s ≥ 5: Cauchy's proof route.
    sorry

end PolygonalNumberTheorem
