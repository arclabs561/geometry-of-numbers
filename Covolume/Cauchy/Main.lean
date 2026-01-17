import Covolume.Core.Basic
import Covolume.Legendre.Main
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

namespace Covolume

/-- If a real interval has length `> 2`, it contains an odd integer. -/
lemma exists_odd_in_interval {L U : ℝ} (hLU : L + 2 < U) :
    ∃ b : ℤ, Odd b ∧ L < (b : ℝ) ∧ (b : ℝ) < U := by
  -- Use `b0 = ⌊L⌋ + 1`. If `b0` is odd we are done; otherwise `b0 + 1` is odd.
  let b0 : ℤ := Int.floor L + 1
  have hL_b0 : L < (b0 : ℝ) := by
    -- `L < ⌊L⌋ + 1`
    simpa [b0, Int.cast_add, Int.cast_one] using (Int.lt_floor_add_one L)
  have hfloor_le : (Int.floor L : ℝ) ≤ L := Int.floor_le L
  have hb0_le : (b0 : ℝ) ≤ L + 1 := by
    -- `⌊L⌋ + 1 ≤ L + 1`
    have : (Int.floor L : ℝ) + 1 ≤ L + 1 := by linarith
    simpa [b0, Int.cast_add, Int.cast_one, add_assoc, add_comm, add_left_comm] using this
  have hL1U : L + 1 < U := by linarith
  have hb0_U : (b0 : ℝ) < U := lt_of_le_of_lt hb0_le hL1U

  rcases Int.even_or_odd b0 with hb0_even | hb0_odd
  · -- `b0` even: take `b = b0 + 1`.
    let b : ℤ := b0 + 1
    have hb_odd : Odd b := by
      -- In ℤ: `Odd b ↔ ¬ Even b`.
      apply (Int.not_even_iff_odd).1
      intro hb_even
      -- `Even (b0 + 1)` would imply `Odd b0`, contradicting `Even b0`.
      have hb0_odd' : Odd b0 := by
        -- `Even (b0 + 1) ↔ (Odd b0 ↔ Odd 1)` by `Int.even_add'`.
        -- Since `Odd 1`, this simplifies to `Even (b0 + 1) ↔ Odd b0`.
        have : Even (b0 + 1) ↔ Odd b0 := by
          simpa [Int.even_add', (show Odd (1 : ℤ) by decide)]
        exact this.mp hb_even
      exact (Int.not_odd_iff_even.2 hb0_even) hb0_odd'

    have hL_b : L < (b : ℝ) := by
      -- `L < b0 < b0 + 1`
      have hb0_lt_b : (b0 : ℝ) < (b : ℝ) := by
        -- `b = b0 + 1`
        simp [b, Int.cast_add, Int.cast_one]
      exact lt_trans hL_b0 hb0_lt_b

    have hb_le : (b : ℝ) ≤ L + 2 := by
      -- `b = ⌊L⌋ + 2 ≤ L + 2`
      have : (Int.floor L : ℝ) + 2 ≤ L + 2 := by linarith
      -- rewrite `b` as `⌊L⌋ + 2`
      have hb : (b : ℝ) = (Int.floor L : ℝ) + 2 := by
        simp [b, b0, Int.cast_add, Int.cast_one, add_assoc, add_left_comm, add_comm]
      simpa [hb]
    have hb_U : (b : ℝ) < U := lt_of_le_of_lt hb_le hLU
    exact ⟨b, hb_odd, hL_b, hb_U⟩
  · exact ⟨b0, hb0_odd, hL_b0, hb0_U⟩

/-- Gauss's Triangular Number Theorem: every natural number is a sum of three triangular numbers. -/
theorem gauss_triangular (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n := by
  sorry

/-- Fermat's Polygonal Number Theorem. -/
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  rcases hs with h_s3 | h_s4 | h_s5
  · -- s = 3: Gauss's Triangular Number Theorem.
    obtain ⟨a, b, c, habc⟩ := gauss_triangular n
    use ![a, b, c]
    dsimp [triangular] at habc
    rw [← habc]
    simp [Fin.sum_univ_succ]
    ring
  · -- s = 4: Lagrange's Four-Square Theorem.
    obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares n
    use ![a, b, c, d]
    simp [polygonal_four_eq_sq]
    rw [← habcd]
    simp [Fin.sum_univ_succ]
    ring
  · -- s ≥ 5: Cauchy's proof route.
    sorry

end Covolume
