import GeometryOfNumbers.Core.Basic
import GeometryOfNumbers.Cauchy.MediumTablesSmall
import GeometryOfNumbers.Cauchy.MediumTablesMge22
import GeometryOfNumbers.Legendre.Main
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

namespace GeometryOfNumbers
/-- If a real interval has length `> 2`, it contains an odd integer. -/
lemma exists_odd_in_interval {L U : ℝ} (hLU : L + 2 < U) :
    ∃ b : ℤ, Odd b ∧ L < (b : ℝ) ∧ (b : ℝ) < U := by
  -- Use `b0 = ⌊L⌋ + 1`. If `b0` is odd we are done; otherwise `b0 + 1` is odd.
  let b0 : ℤ := Int.floor L + 1
  have hL_b0 : L < (b0 : ℝ) := by
    -- `L < ⌊L⌋ + 1`
    simp [b0, Int.cast_add, Int.cast_one]
  have hfloor_le : (Int.floor L : ℝ) ≤ L := Int.floor_le L
  have hb0_le : (b0 : ℝ) ≤ L + 1 := by
    -- `⌊L⌋ + 1 ≤ L + 1`
    have : (Int.floor L : ℝ) + 1 ≤ L + 1 := by linarith
    simpa [b0, Int.cast_add, Int.cast_one, add_comm, add_left_comm] using this
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
          simp
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
        simp [b, b0, Int.cast_add, add_left_comm, add_comm]
      simpa [hb]
    have hb_U : (b : ℝ) < U := lt_of_le_of_lt hb_le hLU
    exact ⟨b, hb_odd, hL_b, hb_U⟩
  · exact ⟨b0, hb0_odd, hL_b0, hb0_U⟩

/-- Gauss's Triangular Number Theorem: every natural number is a sum of three triangular numbers. -/
theorem gauss_triangular (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n := by
  classical
  let m : ℕ := 8 * n + 3
  have hm8 : m % 8 = 3 := by simp [m]
  rcases GeometryOfNumbers.sum_three_squares_of_three_mod_eight m hm8 with ⟨x, y, z, hxyz⟩

  have hmod4 :
      ((x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = (3 : ZMod 4) := by
    have hcast : ((x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ZMod 4) = (m : ZMod 4) := by simp [hxyz]
    simpa [m, pow_two, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast

  -- Finite check in `ZMod 4`: if a sum of three squares is `3`, then each square is `1`.
  have hsq :
      ((x : ZMod 4) ^ 2 = 1) ∧ ((y : ZMod 4) ^ 2 = 1) ∧ ((z : ZMod 4) ^ 2 = 1) := by
    have h :
        ∀ X Y Z : ZMod 4,
          X ^ 2 + Y ^ 2 + Z ^ 2 = 3 → (X ^ 2 = 1 ∧ Y ^ 2 = 1 ∧ Z ^ 2 = 1) := by
      decide
    exact h (x : ZMod 4) (y : ZMod 4) (z : ZMod 4) hmod4
  have hx_sq1 : (x : ZMod 4) ^ 2 = 1 := hsq.1
  have hy_sq1 : (y : ZMod 4) ^ 2 = 1 := hsq.2.1
  have hz_sq1 : (z : ZMod 4) ^ 2 = 1 := hsq.2.2

  have hx_odd : Odd x := by
    rcases Nat.even_or_odd x with hx_even | hx_odd
    · rcases hx_even with ⟨k, rfl⟩
      have h22 : ((2 : ZMod 4) * (2 : ZMod 4)) = 0 := by decide
      have h0' : ((2 * k : ℕ) : ZMod 4) ^ 2 = 0 := by
        simp [pow_two, mul_left_comm, mul_comm, h22]
      have h0 : ((k + k : ℕ) : ZMod 4) ^ 2 = 0 := by
        simpa [two_mul] using h0'
      have h1 : ((k + k : ℕ) : ZMod 4) ^ 2 = 1 := by
        simpa [two_mul] using hx_sq1
      have hfalse : False := by
        have : (0 : ZMod 4) = 1 := by
          simpa using (h0.symm.trans h1)
        exact (by decide : (0 : ZMod 4) ≠ 1) this
      exact False.elim hfalse
    · exact hx_odd

  have hy_odd : Odd y := by
    rcases Nat.even_or_odd y with hy_even | hy_odd
    · rcases hy_even with ⟨k, rfl⟩
      have h22 : ((2 : ZMod 4) * (2 : ZMod 4)) = 0 := by decide
      have h0' : ((2 * k : ℕ) : ZMod 4) ^ 2 = 0 := by
        simp [pow_two, mul_left_comm, mul_comm, h22]
      have h0 : ((k + k : ℕ) : ZMod 4) ^ 2 = 0 := by
        simpa [two_mul] using h0'
      have h1 : ((k + k : ℕ) : ZMod 4) ^ 2 = 1 := by
        simpa [two_mul] using hy_sq1
      have hfalse : False := by
        have : (0 : ZMod 4) = 1 := by
          simpa using (h0.symm.trans h1)
        exact (by decide : (0 : ZMod 4) ≠ 1) this
      exact False.elim hfalse
    · exact hy_odd

  have hz_odd : Odd z := by
    rcases Nat.even_or_odd z with hz_even | hz_odd
    · rcases hz_even with ⟨k, rfl⟩
      have h22 : ((2 : ZMod 4) * (2 : ZMod 4)) = 0 := by decide
      have h0' : ((2 * k : ℕ) : ZMod 4) ^ 2 = 0 := by
        simp [pow_two, mul_left_comm, mul_comm, h22]
      have h0 : ((k + k : ℕ) : ZMod 4) ^ 2 = 0 := by
        simpa [two_mul] using h0'
      have h1 : ((k + k : ℕ) : ZMod 4) ^ 2 = 1 := by
        simpa [two_mul] using hz_sq1
      have hfalse : False := by
        have : (0 : ZMod 4) = 1 := by
          simpa using (h0.symm.trans h1)
        exact (by decide : (0 : ZMod 4) ≠ 1) this
      exact False.elim hfalse
    · exact hz_odd

  rcases hx_odd with ⟨a, rfl⟩
  rcases hy_odd with ⟨b, rfl⟩
  rcases hz_odd with ⟨c, rfl⟩
  refine ⟨a, b, c, ?_⟩

  -- Rewrite each odd square as `8*triangular + 1` and regroup.
  have h8 : 8 * (triangular a + triangular b + triangular c) + 3 = m := by
    have hx : (1 + 2 * a) ^ 2 = 8 * triangular a + 1 := by
      simpa [add_comm, add_left_comm, add_assoc] using odd_sq_eq_eight_triangular_add_one a
    have hy : (1 + 2 * b) ^ 2 = 8 * triangular b + 1 := by
      simpa [add_comm, add_left_comm, add_assoc] using odd_sq_eq_eight_triangular_add_one b
    have hz : (1 + 2 * c) ^ 2 = 8 * triangular c + 1 := by
      simpa [add_comm, add_left_comm, add_assoc] using odd_sq_eq_eight_triangular_add_one c
    have htri :
        (8 * triangular a + 1) + (8 * triangular b + 1) + (8 * triangular c + 1) = m := by
      simpa [hx, hy, hz, add_assoc, add_left_comm, add_comm, -triangular_def] using hxyz
    -- Regroup without unfolding `triangular`.
    let ta : ℕ := triangular a
    let tb : ℕ := triangular b
    let tc : ℕ := triangular c
    have htri' : (8 * ta + 1) + (8 * tb + 1) + (8 * tc + 1) = m := by
      simpa [ta, tb, tc] using htri
    have hregroup : (8 * ta + 1) + (8 * tb + 1) + (8 * tc + 1) = 8 * (ta + tb + tc) + 3 := by
      ring
    -- desired form
    simpa [ta, tb, tc] using (hregroup.symm.trans htri')

  have h8' : 8 * (triangular a + triangular b + triangular c) + 3 = 8 * n + 3 := by
    simpa [m] using h8
  have hmul : 8 * (triangular a + triangular b + triangular c) = 8 * n :=
    Nat.add_right_cancel h8'
  exact Nat.mul_left_cancel (by decide : 0 < 8) hmul

/- Fermat's Polygonal Number Theorem. -/
-- Design boundary (from `PROOF_ROADMAP.md`):
-- Cauchy/Nathanson reduction should prove that for `s ≥ 5`, every `n` is a sum of `s` `s`-gonal
-- numbers, with a construction where *at most four* of the terms are not `0` or `1`.
-- This section keeps the parameter-selection + Cauchy-lemma interface explicit, so the rest of
-- `cauchy_decomposition` is bookkeeping.

/-- Nathanson-style parameter selection (interface).

Let \(m = s-2\). We want to choose odd \(b\), a residue \(r\) with \(0 \le r \le s-4\), and a
quotient \(q\) such that:

\[
  n = m q + b + r,
\]

and the two inequalities needed to apply Cauchy’s lemma with \(a = 2q+b\):

\[
  b^2 < 4a,\qquad 3a < b^2 + 2b + 4.
\]

This is the “interval + residue class” step in the streamlined proof (e.g. Whitty’s talk notes). -/
/-
NOTE: This is a regular block comment (not a doc comment), because the preceding `/-- ... -/`
is a docstring intended to attach to `nathanson_parameters`.

The eventual proofs of `nathanson_parameters` / `cauchy_lemma` are arithmetic-heavy. A recurring
source of friction is rewriting between `ℕ` and `ℤ` inequalities. We keep a couple of small,
local lemmas here so the main proof skeleton can stay readable.
-/

lemma int_sq_lt_int_ofNat_mul {b q : ℕ} :
    ((b : ℤ) ^ 2 < 4 * ((2 * q + b : ℕ) : ℤ)) ↔ b ^ 2 < 4 * (2 * q + b) := by
  -- Both sides are comparisons of nonnegative integers; `norm_cast` can bridge them.
  norm_cast

lemma int_three_mul_ofNat_lt_int_poly {b q : ℕ} :
    (3 * ((2 * q + b : ℕ) : ℤ) < (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4) ↔
      3 * (2 * q + b) < b ^ 2 + 2 * b + 4 := by
  norm_cast

/-!
### Inequality normalization (algebra only)

These lemmas do not “solve” the Nathanson window, but they reduce later proofs to a small set of
canonical inequality shapes by moving additive terms across the inequality.

They are intentionally stated over `ℤ`, since `Nat` subtraction is awkward.
-/

lemma int_b2_lt_four_two_mul_q_add_b_iff (b q : ℕ) :
    ((b : ℤ) ^ 2 < 4 * ((2 * q + b : ℕ) : ℤ)) ↔ ((b : ℤ) ^ 2 - 4 * (b : ℤ) < 8 * (q : ℤ)) := by
  -- Normalize the cast: `↑(2*q+b) = 2*↑q + ↑b`, then expand `4*(...)`.
  have h4cast : (4 * ((2 * q + b : ℕ) : ℤ)) = 4 * (2 * (q : ℤ) + (b : ℤ)) := by
    simp [Nat.cast_add, Nat.cast_mul, mul_add]
  have h4exp : (4 * (2 * (q : ℤ) + (b : ℤ))) = 8 * (q : ℤ) + 4 * (b : ℤ) := by
    ring
  constructor
  · intro h
    have h' : (b : ℤ) ^ 2 < 4 * (2 * (q : ℤ) + (b : ℤ)) := by
      simpa [h4cast] using h
    have h'' : (b : ℤ) ^ 2 < 8 * (q : ℤ) + 4 * (b : ℤ) := by
      simpa [h4exp] using h'
    -- subtract `4b`
    have := sub_lt_sub_right h'' (4 * (b : ℤ))
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  · intro h
    have h'' : (b : ℤ) ^ 2 < 8 * (q : ℤ) + 4 * (b : ℤ) := by
      -- add `4b` back
      have := add_lt_add_right h (4 * (b : ℤ))
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    have h' : (b : ℤ) ^ 2 < 4 * (2 * (q : ℤ) + (b : ℤ)) := by
      simpa [h4exp] using h''
    simpa [h4cast] using h'

lemma int_three_two_mul_q_add_b_lt_iff (b q : ℕ) :
    (3 * ((2 * q + b : ℕ) : ℤ) < (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4) ↔
      (6 * (q : ℤ) < (b : ℤ) ^ 2 - (b : ℤ) + 4) := by
  -- Expand the linear term:
  have hL : (3 * ((2 * q + b : ℕ) : ℤ)) = 6 * (q : ℤ) + 3 * (b : ℤ) := by
    -- `↑(2*q+b) = 2*↑q + ↑b`, then distribute `3`.
    simp [Nat.cast_add, Nat.cast_mul]
    ring
  -- Rewrite the RHS as `(b^2 - b + 4) + 3*b` so we can cancel `+ 3*b`.
  have hR : ((b : ℤ) ^ 2 + 2 * (b : ℤ) + 4) = (b : ℤ) ^ 2 - (b : ℤ) + 4 + 3 * (b : ℤ) := by
    ring
  constructor
  · intro h
    have h' := h
    -- rewrite both sides, then cancel `+ 3*b`.
    rw [hL] at h'
    rw [hR] at h'
    -- cancel `+ 3*b` on both sides
    exact lt_of_add_lt_add_right h'
  · intro h
    have h' : 6 * (q : ℤ) + 3 * (b : ℤ) < (b : ℤ) ^ 2 - (b : ℤ) + 4 + 3 * (b : ℤ) := by
      -- `add_lt_add_right` produces `3*b + 6*q < 3*b + (...)`; commute into our preferred shape.
      simpa [add_assoc, add_left_comm, add_comm] using add_lt_add_right h (3 * (b : ℤ))
    -- fold back to the original inequality
    have h'' := h'
    rw [← hL] at h''
    rw [← hR] at h''
    exact h''

/-- Division-algorithm unpacking for `n = m*q + b + r` with `m = s-2`.

This isolates the purely algebraic part of the Nathanson parameter choice from the
interval/modular argument used to ensure `r ≤ s-4`. -/
lemma sub_mod_add_div (s n b : ℕ) (hb : b ≤ n) :
    let m : ℕ := s - 2
    let x : ℕ := n - b
    n = m * (x / m) + b + x % m := by
  intro m x
  -- Start from the division algorithm for `x`.
  have hx : x = m * (x / m) + x % m := by
    -- `Nat.mod_add_div` is `x % m + m * (x / m) = x`; rewrite.
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (Nat.mod_add_div x m).symm
  -- Rebuild `n` from `x = n - b`.
  have hn : n = x + b := by
    exact (Nat.sub_add_cancel hb).symm
  -- Substitute and rearrange.
  calc
    n = x + b := hn
    _ = (m * (x / m) + x % m) + b := by
          -- Avoid `simp [hx]`: rewriting `x` using `hx` would loop because the RHS still contains `x`.
          simpa [Nat.add_assoc] using congrArg (fun t => t + b) hx
    _ = m * (x / m) + b + x % m := by ac_rfl

/-- If `x % m = m - 1` and `m ≥ 3`, then `(x - 2) % m = m - 3`.

This is the tiny modular arithmetic step used in the Nathanson parameter selection:
if one odd choice of `b` makes `(n-b) % m` land on the “bad” last residue class `m-1`,
then shifting to `b+2` moves the remainder down by `2`. -/
lemma mod_sub_two_of_mod_eq_pred {m x : ℕ} (hm : 3 ≤ m) (hx : x % m = m - 1) :
    (x - 2) % m = m - 3 := by
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hm
  let q : ℕ := x / m
  have hxrep : x = (m - 1) + m * q := by
    -- `x = x % m + m * (x / m)` and `x % m = m-1`.
    have h := (Nat.mod_add_div x m).symm
    -- `Nat.mod_add_div` is phrased as `x % m + m * (x / m) = x`.
    -- We only need a rearranged version.
    -- (Also, `m` may be `0` in general, so keep `hm_pos` in scope.)
    simpa [q, hx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  have h2 : 2 ≤ m - 1 := by
    -- since `m ≥ 3`, we have `m-1 ≥ 2`.
    omega
  have hxsub : x - 2 = m * q + (m - 3) := by
    -- subtract `2` from the explicit remainder form.
    calc
      x - 2 = ((m - 1) + m * q) - 2 := by simp [hxrep]
      _ = (m * q + (m - 1)) - 2 := by ac_rfl
      _ = m * q + ((m - 1) - 2) := by
            -- push subtraction into the second addend (since `2 ≤ m-1`)
            simpa using (Nat.add_sub_assoc h2 (m * q))
      _ = m * q + (m - 3) := by omega
  calc
    (x - 2) % m = (m * q + (m - 3)) % m := by simp [hxsub]
    _ = ((m - 3) + m * q) % m := by ac_rfl
    _ = (m - 3) % m := by simp [Nat.add_mul_mod_self_left]
    _ = m - 3 := by
          apply Nat.mod_eq_of_lt
          -- `m-3 < m` for `m ≥ 1`, in particular for `m ≥ 3`.
          omega

/-- Given a candidate `b` with room to shift to `b+2`, we can always choose `b' ∈ {b, b+2}`
so that the remainder `r` in `n = (s-2)q + b' + r` satisfies `r ≤ s-4`.

This is the purely modular “avoid the last residue class” step in the Nathanson parameter
selection. -/
lemma exists_qr_with_remainder_le {s n b : ℕ} (hs : 5 ≤ s) (hb2 : b + 2 ≤ n) :
    ∃ b' q r : ℕ,
      (b' = b ∨ b' = b + 2) ∧
        r ≤ s - 4 ∧
          n = (s - 2) * q + b' + r := by
  let m : ℕ := s - 2
  have hm : 3 ≤ m := by
    -- `s ≥ 5` ⇒ `s-2 ≥ 3`.
    omega
  have hb : b ≤ n := le_trans (Nat.le_add_right b 2) hb2
  let x : ℕ := n - b
  have hn_b : n = m * (x / m) + b + x % m := by
    simpa [m, x] using sub_mod_add_div s n b hb

  by_cases hlast : x % m = m - 1
  · -- Bad remainder: shift `b` to `b+2`, which shifts `x` down by `2`.
    let b' : ℕ := b + 2
    have hb' : b' ≤ n := hb2
    let x' : ℕ := n - b'
    have hx' : x' = x - 2 := by
      -- `n - (b+2) = (n-b) - 2` under `b+2 ≤ n`.
      omega
    have hr' : x' % m = m - 3 := by
      -- `x % m = m-1` ⇒ `(x-2) % m = m-3`.
      simpa [x', hx'] using mod_sub_two_of_mod_eq_pred (m := m) (x := x) hm hlast
    have hn_b' : n = m * (x' / m) + b' + x' % m := by
      simpa [m, b', x'] using sub_mod_add_div s n b' hb'
    refine ⟨b', x' / m, x' % m, ?_, ?_, ?_⟩
    · right; rfl
    · -- `m-3 ≤ m-2 = s-4`
      -- (rewrite `s-4` as `m-2` via `m = s-2`)
      have hmbound : m - 3 ≤ m - 2 := by omega
      have : x' % m ≤ m - 2 := by simpa [hr'] using hmbound
      simpa [m] using this
    · -- normalize into the target `n = (s-2)*q + b' + r`
      simpa [m, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn_b'
  · -- Good remainder already: `x % m ≤ m-2 = s-4`.
    have hx_lt : x % m < m := Nat.mod_lt x (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hm)
    have hx_le : x % m ≤ m - 2 := by
      -- If `x % m < m` and `x % m ≠ m-1`, then `x % m ≤ m-2`.
      omega
    refine ⟨b, x / m, x % m, ?_, ?_, ?_⟩
    · left; rfl
    · -- `m-2 = s-4`
      simpa [m] using hx_le
    · simpa [m, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn_b

/-!
## Nathanson parameter selection

We isolate a tiny “small-n” base case: when `n` is small compared to `s`, we can pick `q = 0`
and `b = 1` and discharge the inequality window by arithmetic.

This is not the main argument (which is an interval/window existence proof), but splitting it
out makes the remaining task both smaller and more honest.
-/

/-- `nathanson_parameters` base case: if `n ≤ s-3` (with `s ≥ 5`), take `q=0`, `b=1`. -/
lemma nathanson_parameters_small (s : ℕ) (hs : 5 ≤ s) (n : ℕ) (hn : 0 < n) (hsmall : n ≤ s - 3) :
    ∃ b q r : ℕ,
      r ≤ s - 4 ∧ Odd b ∧
        ((b : ℤ) ^ 2 < 4 * ((2 * q + b : ℕ) : ℤ)) ∧
        (3 * ((2 * q + b : ℕ) : ℤ) < (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4) ∧
        n = (s - 2) * q + b + r := by
  refine ⟨1, 0, n - 1, ?_, ?_, ?_, ?_, ?_⟩
  · -- `n - 1 ≤ s - 4`
    have : n - 1 ≤ s - 4 := by omega
    exact this
  · simp
  · -- `1^2 < 4*(2*0+1)`
    norm_num
  · -- `3*(2*0+1) < 1^2 + 2*1 + 4`
    norm_num
  · -- `n = (s-2)*0 + 1 + (n-1)`
    have hn1 : 1 ≤ n := Nat.succ_le_iff.2 hn
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hn1
    -- normalize the RHS and then close with `hsub`.
    calc
      n = n - 1 + 1 := by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsub.symm
      _ = (s - 2) * 0 + 1 + (n - 1) := by ring_nf

/-- Nathanson's key window inequality in the “large” regime.

For \(x := n/m\) large enough, the interval
\[
  \Bigl(\tfrac12 + \sqrt{6x-3},\ \tfrac23 + \sqrt{8x-8}\Bigr)
\]
has length \(>4\), which lets us pick two consecutive odd integers inside.

This lemma proves the explicit bound used in `nathanson_parameters`.
-/
lemma nathanson_gap_large {x : ℝ} (hx : (108 : ℝ) < x) :
    ((1 / 2 : ℝ) + Real.sqrt (6 * x - 3)) + 4 <
      ((2 / 3 : ℝ) + Real.sqrt (8 * x - 8)) := by
  have hx_le : (108 : ℝ) ≤ x := le_of_lt hx
  have hA0 : 0 ≤ 8 * x - 8 := by nlinarith [hx_le]
  have hB0 : 0 ≤ 6 * x - 3 := by nlinarith [hx_le]
  have hApos : 0 < 8 * x - 8 := by nlinarith [hx]

  -- Reduce to the inequality on the sqrt-difference.
  have hdiff : (23 / 6 : ℝ) < Real.sqrt (8 * x - 8) - Real.sqrt (6 * x - 3) := by
    set A : ℝ := 8 * x - 8
    set B : ℝ := 6 * x - 3
    have hA0' : 0 ≤ A := by simpa [A] using hA0
    have hB0' : 0 ≤ B := by simpa [B] using hB0
    have hApos' : 0 < A := by simpa [A] using hApos

    set sA : ℝ := Real.sqrt A
    set sB : ℝ := Real.sqrt B

    have hsA0 : 0 ≤ sA := by simp [sA]
    have hsB0 : 0 ≤ sB := by simp [sB]
    have hsApos : 0 < sA := by
      -- `sqrt` is positive on positive inputs.
      simpa [sA] using Real.sqrt_pos.2 hApos'
    have hden_pos : 0 < sA + sB := by nlinarith [hsApos, hsB0]

    -- Cauchy/AM-GM: `sA + sB ≤ sqrt(2*(A+B))`.
    have hden_le : sA + sB ≤ Real.sqrt (2 * (A + B)) := by
      have h2ab : 2 * sA * sB ≤ sA ^ 2 + sB ^ 2 := by
        have hsq : 0 ≤ (sA - sB) ^ 2 := sq_nonneg (sA - sB)
        -- `(sA - sB)^2 = sA^2 + sB^2 - 2*sA*sB`
        -- so `2*sA*sB ≤ sA^2 + sB^2`.
        nlinarith [hsq]
      have hsquare : (sA + sB) ^ 2 ≤ 2 * (A + B) := by
        calc
          (sA + sB) ^ 2
              = sA ^ 2 + sB ^ 2 + 2 * sA * sB := by ring
          _ ≤ (sA ^ 2 + sB ^ 2) + (sA ^ 2 + sB ^ 2) := by nlinarith [h2ab]
          _ = 2 * (sA ^ 2 + sB ^ 2) := by ring
          _ = 2 * (A + B) := by
            -- `sA^2 = A`, `sB^2 = B` since `A,B ≥ 0`.
            simp [sA, sB, Real.sq_sqrt hA0', Real.sq_sqrt hB0']
      have h2AB0 : 0 ≤ 2 * (A + B) := by nlinarith [hA0', hB0']
      have hnonneg : 0 ≤ sA + sB := by nlinarith [hsA0, hsB0]
      -- `a ≤ sqrt(b)` iff `0 ≤ a` and `a^2 ≤ b` (given `0 ≤ b`).
      exact (Real.le_sqrt hnonneg h2AB0).2 hsquare

    -- Rewrite `sqrt(2*(A+B))` into the concrete `sqrt(28*x-22)` shape we use below.
    have hden_le' : sA + sB ≤ Real.sqrt (x * 28 - 22) := by
      have h2AB : 2 * (A + B) = x * 28 - 22 := by
        simp [A, B]; ring
      have ht0 : 0 ≤ (x * 28 - 22) := by nlinarith [hx_le]
      simpa [h2AB] using hden_le

    -- Polynomial step: show `(23/6) * sqrt(x*28-22) < 2x-5` by squaring.
    have hpoly_mul : (23 / 6 : ℝ) * Real.sqrt (x * 28 - 22) < (2 * x - 5) := by
      -- Use `x*28-22` consistently so `Real.sq_sqrt` fires without rewriting.
      set L : ℝ := (23 / 6 : ℝ) * Real.sqrt (x * 28 - 22)
      set R : ℝ := (2 * x - 5)
      have hL0 : 0 ≤ L := by
        have hconst : 0 ≤ (23 / 6 : ℝ) := by norm_num
        exact mul_nonneg hconst (Real.sqrt_nonneg _)
      have hR0 : 0 ≤ R := by nlinarith [hx_le]
      have hsq : L ^ 2 < R ^ 2 := by
        have ht0 : 0 ≤ (x * 28 - 22) := by nlinarith [hx_le]
        have hsqt :
            Real.sqrt (x * 28 - 22) * Real.sqrt (x * 28 - 22) = (x * 28 - 22) := by
          simpa [pow_two] using (Real.sq_sqrt ht0)
        have : (23 / 6 : ℝ) ^ 2 * (x * 28 - 22) < (2 * x - 5) ^ 2 := by
          nlinarith [hx_le]
        -- Expand squares and rewrite `sqrt(t)*sqrt(t)` to `t`.
        simpa [L, R, pow_two, hsqt, mul_assoc, mul_left_comm, mul_comm] using this
      have habs : |L| < |R| := (sq_lt_sq).1 hsq
      have hLR : L < R := by
        simpa [abs_of_nonneg hL0, abs_of_nonneg hR0] using habs
      simpa [L, R] using hLR

    -- Use `sA+sB ≤ sqrt(2*(A+B)) = sqrt(28x-22)` to transfer the bound to `sA+sB`.
    have hmul_denom : (23 / 6 : ℝ) * (sA + sB) < (2 * x - 5) := by
      have hconst : 0 ≤ (23 / 6 : ℝ) := by norm_num
      have hle : (23 / 6 : ℝ) * (sA + sB) ≤ (23 / 6 : ℝ) * Real.sqrt (x * 28 - 22) :=
        mul_le_mul_of_nonneg_left hden_le' hconst
      exact lt_of_le_of_lt hle hpoly_mul

    -- Rationalization identity (in multiplicative form).
    have hrat_mul : (sA - sB) * (sA + sB) = (2 * x - 5) := by
      calc
        (sA - sB) * (sA + sB) = sA ^ 2 - sB ^ 2 := by ring
        _ = A - B := by simp [sA, sB, Real.sq_sqrt hA0', Real.sq_sqrt hB0']
        _ = 2 * x - 5 := by simp [A, B]; ring

    -- Conclude `23/6 < sA - sB` by right-multiplying with `(sA+sB) > 0`.
    have hlt_prod :
        (23 / 6 : ℝ) * (sA + sB) < (sA - sB) * (sA + sB) := by
      -- RHS is `2x-5`.
      simpa [hrat_mul] using hmul_denom
    have : (23 / 6 : ℝ) < (sA - sB) := by
      -- Cancel the nonnegative left factor `sA+sB` from `(sA+sB)*(23/6) < (sA+sB)*(sA-sB)`.
      have hmul : (sA + sB) * (23 / 6 : ℝ) < (sA + sB) * (sA - sB) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hlt_prod
      exact lt_of_mul_lt_mul_left hmul (le_of_lt hden_pos)
    simpa [sA, sB, A, B] using this

  -- Finish from the sqrt-difference inequality.
  have : ((1 / 2 : ℝ) + Real.sqrt (6 * x - 3)) + 4 <
      ((2 / 3 : ℝ) + Real.sqrt (8 * x - 8)) := by
    -- `linarith` after rearranging.
    linarith [hdiff]
  simpa using this

/-!
## Deprecated: the uniform `nathanson_parameters` lemma

The “Cauchy route” through `cauchy_lemma` requires two window inequalities. Those inequalities are
**not** uniformly satisfiable in the bounded regime `n ≤ 108 * (s - 2)` (counterexample: `s=5, n=5`).

So we do **not** keep a global `nathanson_parameters` lemma in this file anymore.

The only version we rely on is the large-regime lemma `nathanson_parameters_large` below, which is
the analytic interval/window argument.
-/

/- (historical note)

Older versions of this file contained `nathanson_parameters` / `nathanson_parameters_medium`.
Those were removed once we had a correct split by regime and a proved top-level theorem.
-/
/-  (historical / removed proof body; kept in git history)
    have hn324 : 324 < n := lt_of_le_of_lt h324 hnm
    have hn_large : 325 ≤ n := Nat.succ_le_iff.2 hn324
    have hnR0 : (0 : ℝ) ≤ n_R := by
      -- `n_R` is a local `let`.
      simp [n_R]
    have hnR14 : (14 : ℝ) ≤ n_R := by
      have : (14 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (by decide : 14 ≤ 325) hn_large)
      simpa [n_R] using this

    -- `n_R / m_R ≤ n_R` since `0 ≤ n_R` and `1 ≤ m_R`.
    have hm1 : (1 : ℝ) ≤ m_R := by
      have : (1 : ℕ) ≤ m := le_trans (by decide : 1 ≤ 3) hm'
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
      simpa [m_R] using this
    have hdiv : n_R / m_R ≤ n_R := div_le_self hnR0 hm1
    have hinside : 8 * (n_R / m_R) - 8 ≤ 8 * n_R := by nlinarith [hdiv]
    have hsqrt1 : Real.sqrt (8 * (n_R / m_R) - 8) ≤ Real.sqrt (8 * n_R) :=
      Real.sqrt_le_sqrt hinside

    -- `sqrt(8*n) ≤ n-3` for `n ≥ 14` (square both sides).
    have hsqrt2 : Real.sqrt (8 * n_R) ≤ n_R - 3 := by
      have hnonneg : 0 ≤ n_R - 3 := by linarith
      have hsq : 8 * n_R ≤ (n_R - 3) ^ 2 := by nlinarith [hnR14]
      exact (Real.sqrt_le_iff).2 ⟨hnonneg, by simpa [pow_two] using hsq⟩

    have hsqrt : Real.sqrt (8 * (n_R / m_R) - 8) ≤ n_R - 3 := le_trans hsqrt1 hsqrt2
    have hub_lt : (upper_bound : ℝ) < n_R := by
      -- `upper_bound = 2/3 + sqrt(...) ≤ 2/3 + (n-3) = n - 7/3 < n`.
      dsimp [upper_bound]
      have hle : (2 / 3 : ℝ) + Real.sqrt (8 * (n_R / m_R) - 8) ≤ (2 / 3 : ℝ) + (n_R - 3) := by
        nlinarith [hsqrt]
      have hlt : (2 / 3 : ℝ) + (n_R - 3) < n_R := by linarith
      exact lt_of_le_of_lt hle hlt

    -- From `hb0_lt : (b0:ℝ) < upper_bound - 2` get `b0+2 < upper_bound < n`.
    have hb0plus2_ltR : (b0 : ℝ) + 2 < n_R := by
      have hb0plus2_ltU : (b0 : ℝ) + 2 < upper_bound := by linarith [hb0_lt]
      exact lt_trans hb0plus2_ltU hub_lt
    have hb0plus2_leZ : (b0 : ℤ) + 2 ≤ (n : ℤ) := by
      have hb0plus2_ltR' : ((b0 + 2 : ℤ) : ℝ) < (n : ℝ) := by
        simpa [n_R, Int.cast_add, Int.cast_ofNat, add_assoc, add_left_comm, add_comm] using hb0plus2_ltR
      have hb0plus2_ltZ : (b0 + 2 : ℤ) < (n : ℤ) := by
        exact_mod_cast hb0plus2_ltR'
      exact le_of_lt hb0plus2_ltZ
    have : (b_nat + 2 : ℤ) ≤ (n : ℤ) := by
      -- `(b_nat:ℤ)+2 = b0+2` since `b_nat = toNat b0` and `b0 ≥ 0`.
      simpa [hb_nat_eq, Nat.cast_add] using hb0plus2_leZ
    exact_mod_cast this

  obtain ⟨b, q, r, hb_choice, hr_le, hn_eq⟩ := exists_qr_with_remainder_le (s := s) (n := n) (b := b_nat) hs hb2_le_n

  have hb_odd : Odd b := by
    rcases hb_choice with rfl | rfl
    · exact hb_nat_odd
    · exact hb_nat_odd.add_even (by simp)

  refine ⟨b, q, r, hr_le, hb_odd, ?_, ?_, hn_eq⟩

  -- 4. Verify inequalities.
  -- We know b is roughly b0 or b0+2.
  -- b0 in (sqrt(6n/m), sqrt(8n/m)-2).
  -- So b in (sqrt(6n/m), sqrt(8n/m)).

  -- Inequality 1: b^2 < 4(2q+b)
  -- Equivalent to m*b^2 - (4m-8)b < 8(n-r).
  -- roughly m*b^2 < 8n.
  -- b < sqrt(8n/m) => m*b^2 < 8n.
  -- We need to handle the linear terms and r.

  -- Inequality 2: 3(2q+b) < b^2 + 2b + 4
  -- Equivalent to 6(n-r) < m*b^2 + (6-m)b + 4m.
  -- roughly 6n < m*b^2.
  -- b > sqrt(6n/m) => m*b^2 > 6n.

  -- We need to fill in the algebraic details connecting the real bounds to the integer inequalities.

  -- Refactor note (optional): split this proof into two lemmas mirroring Nathanson:
  -- - upper-bound lemma: `b < 2/3 + sqrt(8*(n/m)-8)` ⇒ `b^2 < 4a`
  -- - lower-bound lemma: `b > 1/2 + sqrt(6*(n/m)-3)` ⇒ `3a < b^2 + 2b + 4`
  · -- Inequality 1: `b^2 < 4*(2q+b)`.
    --
    -- Grokky move:
    -- \[
    --   b^2 < 4(2q+b)
    --   \;\Longleftrightarrow\;
    --   b^2 - 4b < 8q.
    -- \]
    apply (int_b2_lt_four_two_mul_q_add_b_iff b q).2

    -- Convert `b_nat = b0` into a real equality for rewriting.
    have hb_nat_eqR : (b_nat : ℝ) = (b0 : ℝ) := by
      simpa using congrArg (fun t : ℤ => (t : ℝ)) hb_nat_eq

    -- First: get the real upper bound `↑b < upper_bound` from the `b0` interval.
    have hbR_lt_upper : (b : ℝ) < upper_bound := by
      rcases hb_choice with rfl | rfl
      · -- `b = b_nat` so `↑b = b0 < upper_bound - 2 < upper_bound`.
        have hb0lt : (b_nat : ℝ) < upper_bound - 2 := by
          have : (b0 : ℝ) < upper_bound - 2 := hb0_lt
          simpa [hb_nat_eqR] using this
        have : (b_nat : ℝ) < upper_bound := by linarith
        simpa using this
      · -- `b = b_nat+2`, so `↑b = ↑b_nat + 2 < upper_bound`.
        have hb0lt : (b_nat : ℝ) < upper_bound - 2 := by
          have : (b0 : ℝ) < upper_bound - 2 := hb0_lt
          simpa [hb_nat_eqR] using this
        have : (b_nat : ℝ) + 2 < upper_bound := by linarith
        simpa [Nat.cast_add] using this

    -- Sign fence for squaring.
    have hb0' : b ≠ 0 := by
      rcases hb_odd with ⟨k, hk⟩
      have hbpos : 0 < b := by simp [hk]
      exact Nat.ne_of_gt hbpos
    have hb1 : (1 : ℕ) ≤ b := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hb0')
    have hbR_ge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    have hb_shift_nonneg : (0 : ℝ) ≤ (b : ℝ) - (2 / 3 : ℝ) := by nlinarith [hbR_ge1]

    -- Let `x = n/m` (reals).
    set x : ℝ := n_R / m_R

    -- From `b < upper_bound = 2/3 + sqrt(8x-8)`, get `b-2/3 < sqrt(8x-8)`.
    have hb_minus_lt : (b : ℝ) - (2 / 3 : ℝ) < Real.sqrt (8 * x - 8) := by
      have : (b : ℝ) < (2 / 3 : ℝ) + Real.sqrt (8 * x - 8) := by
        simpa [x, upper_bound] using hbR_lt_upper
      linarith

    -- In the large regime we have `x > 108`, hence `8x-8 ≥ 0`.
    have hA0 : (0 : ℝ) ≤ 8 * x - 8 := by
      have hnm_nat : 108 * m < n := Nat.lt_of_not_ge hmed
      have hnm_real : (108 : ℝ) * m_R < n_R := by
        simpa [n_R, m_R, Nat.cast_mul] using (show ((108 * m : ℕ) : ℝ) < (n : ℝ) from by
          exact_mod_cast hnm_nat)
      have hx108 : (108 : ℝ) < x := by
        have hm_ne : m_R ≠ 0 := ne_of_gt hm_pos
        have hmul : (108 : ℝ) * m_R < x * m_R := by
          simpa [x, hm_ne] using hnm_real
        have hmul' : m_R * (108 : ℝ) < m_R * x := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        exact lt_of_mul_lt_mul_left hmul' (le_of_lt hm_pos)
      nlinarith [le_of_lt hx108]

    have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (8 * x - 8) := Real.sqrt_nonneg _
    have hb_sq_lt : ((b : ℝ) - (2 / 3 : ℝ)) ^ 2 < 8 * x - 8 := by
      have : ((b : ℝ) - (2 / 3 : ℝ)) ^ 2 < (Real.sqrt (8 * x - 8)) ^ 2 := by
        nlinarith [hb_shift_nonneg, hb_minus_lt, hsqrt0]
      simpa [pow_two, Real.sq_sqrt hA0] using this

    -- Expand the square and rearrange: a bound on `b^2 - 4b`.
    have hquad : (b : ℝ) ^ 2 - 4 * (b : ℝ) < 8 * x - (8 / 3 : ℝ) * (b : ℝ) - (76 / 9 : ℝ) := by
      have hsq_exp : ((b : ℝ) - (2 / 3 : ℝ)) ^ 2 =
          (b : ℝ) ^ 2 - (4 / 3 : ℝ) * (b : ℝ) + (4 / 9 : ℝ) := by
        ring
      have hb_sq_lt' :
          (b : ℝ) ^ 2 - (4 / 3 : ℝ) * (b : ℝ) + (4 / 9 : ℝ) < 8 * x - 8 := by
        simpa [hsq_exp] using hb_sq_lt
      linarith [hb_sq_lt']

    -- Express `q` from `n = m*q + b + r` and bound `8q` below.
    have hn_eq' : n = m * q + b + r := by
      simpa [m, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc] using hn_eq
    have hx_eq : x = (q : ℝ) + ((b : ℝ) + (r : ℝ)) / m_R := by
      have hm_ne : m_R ≠ 0 := ne_of_gt hm_pos
      have hn_eqR : n_R = m_R * (q : ℝ) + ((b : ℝ) + (r : ℝ)) := by
        have : (n : ℝ) = ((m * q + b + r : ℕ) : ℝ) := by exact_mod_cast hn_eq'
        simpa [n_R, m_R, Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm] using this
      -- Divide the identity `n = m*q + (b+r)` by `m`.
      dsimp [x]
      calc
        n_R / m_R = (m_R * (q : ℝ) + ((b : ℝ) + (r : ℝ))) / m_R := by
          simp [hn_eqR]
        _ = (m_R * (q : ℝ)) / m_R + ((b : ℝ) + (r : ℝ)) / m_R := by
          simpa using (add_div (m_R * (q : ℝ)) ((b : ℝ) + (r : ℝ)) m_R)
        _ = (q : ℝ) + ((b : ℝ) + (r : ℝ)) / m_R := by
          simp [hm_ne]

    -- Bound `(b+r)/m ≤ b/3 + 1` using `m ≥ 3` and `r ≤ m`.
    have hr_le_m : (r : ℝ) / m_R ≤ 1 := by
      have hmpos : (0 : ℝ) < m_R := hm_pos
      have hr_le : (r : ℝ) ≤ (m : ℝ) := by
        have : r ≤ m := by
          have hm2 : m - 2 ≤ m := by omega
          -- `r ≤ m-2` because `r ≤ s-4` and `m = s-2`.
          have : r ≤ m - 2 := by simpa [m] using hr_le
          exact le_trans this hm2
        exact_mod_cast this
      have : (r : ℝ) / m_R ≤ (m : ℝ) / m_R :=
        div_le_div_of_nonneg_right hr_le (le_of_lt hmpos)
      simpa [m_R, div_self (ne_of_gt hmpos)] using this

    have hmR_ge3 : (3 : ℝ) ≤ m_R := by
      simpa [m_R] using (show (3 : ℝ) ≤ (m : ℝ) from by exact_mod_cast hm)
    have hb0R : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (Nat.zero_le b)
    have hb_div : (b : ℝ) / m_R ≤ (b : ℝ) / 3 := by
      have h1 : (1 : ℝ) / m_R ≤ (1 : ℝ) / 3 := by
        simpa [one_div] using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (3 : ℝ)) hmR_ge3)
      have : (b : ℝ) * ((1 : ℝ) / m_R) ≤ (b : ℝ) * ((1 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left h1 hb0R
      simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have hbr_div : ((b : ℝ) + (r : ℝ)) / m_R ≤ (b : ℝ) / 3 + 1 := by
      -- split and use bounds.
      have hadd : ((b : ℝ) + (r : ℝ)) / m_R = (b : ℝ) / m_R + (r : ℝ) / m_R := by
        simpa using (add_div (b : ℝ) (r : ℝ) m_R)
      -- combine the bounds `b/m ≤ b/3` and `r/m ≤ 1`.
      nlinarith [hadd, hb_div, hr_le_m]

    -- Turn the corridor bound into the needed comparison on the “error term”.
    have herr :
        8 * ((b : ℝ) + (r : ℝ)) / m_R ≤ (8 / 3 : ℝ) * (b : ℝ) + (76 / 9 : ℝ) := by
      -- since `8*(b/3 + 1) = (8/3)b + 8 ≤ (8/3)b + 76/9`.
      have htmp : 8 * (((b : ℝ) + (r : ℝ)) / m_R) ≤ 8 * ((b : ℝ) / 3 + 1) :=
        mul_le_mul_of_nonneg_left hbr_div (by norm_num)
      have hlin : 8 * ((b : ℝ) / 3 + 1) = (8 / 3 : ℝ) * (b : ℝ) + (8 : ℝ) := by ring
      have hconst : (8 : ℝ) ≤ (76 / 9 : ℝ) := by norm_num
      have h1 : 8 * (((b : ℝ) + (r : ℝ)) / m_R) ≤ (8 / 3 : ℝ) * (b : ℝ) + (8 : ℝ) := by
        -- rewrite the RHS of `htmp`.
        have : 8 * ((b : ℝ) / 3 + 1) = (8 / 3 : ℝ) * (b : ℝ) + (8 : ℝ) := hlin
        exact le_trans htmp (by simpa [this])
      have h2 : (8 / 3 : ℝ) * (b : ℝ) + (8 : ℝ) ≤ (8 / 3 : ℝ) * (b : ℝ) + (76 / 9 : ℝ) := by
        nlinarith [hconst]
      -- match the goal's left-hand shape.
      have h1' : 8 * ((b : ℝ) + (r : ℝ)) / m_R ≤ (8 / 3 : ℝ) * (b : ℝ) + (8 : ℝ) := by
        -- `8*(b+r)/m = 8*((b+r)/m)` (associate the division onto the second factor).
        have hrewrite :
            (8 : ℝ) * ((b : ℝ) + (r : ℝ)) / m_R = 8 * (((b : ℝ) + (r : ℝ)) / m_R) := by
          simpa [mul_assoc] using (mul_div_assoc (8 : ℝ) ((b : ℝ) + (r : ℝ)) m_R)
        simpa [hrewrite] using h1
      exact le_trans h1' h2

    -- Now `8q = 8x - 8*(b+r)/m` and compare with the quadratic bound.
    have hbqR : (b : ℝ) ^ 2 - 4 * (b : ℝ) < 8 * (q : ℝ) := by
      have hq_eq : (q : ℝ) = x - ((b : ℝ) + (r : ℝ)) / m_R := by nlinarith [hx_eq]
      -- `b^2-4b < 8x - (8/3)b - 76/9 ≤ 8x - 8(b+r)/m = 8q`.
      have haux : 8 * x - (8 / 3 : ℝ) * (b : ℝ) - (76 / 9 : ℝ) ≤ 8 * (q : ℝ) := by
        have hq8 : (8 : ℝ) * (q : ℝ) = 8 * x - 8 * (((b : ℝ) + (r : ℝ)) / m_R) := by
          nlinarith [hq_eq]
        nlinarith [herr, hq8]
      exact lt_of_lt_of_le hquad haux

    -- Cast back to ℤ.
    have hbqZ : (b : ℤ) ^ 2 - 4 * (b : ℤ) < 8 * (q : ℤ) := by
      exact_mod_cast hbqR
    simpa using hbqZ
  · -- Inequality 2: `3*(2q+b) < b^2 + 2b + 4`.
    -- Normalize to `6q < b^2 - b + 4`.
    apply (int_three_two_mul_q_add_b_lt_iff b q).2

    -- Convert `b_nat = b0` into a real equality for rewriting.
    have hb_nat_eqR : (b_nat : ℝ) = (b0 : ℝ) := by
      simpa using congrArg (fun t : ℤ => (t : ℝ)) hb_nat_eq

    -- Lower bound on `b` from the chosen interval (`b0 < b` if we shifted by `+2`).
    have hbR_gt_lower : lower_bound < (b : ℝ) := by
      rcases hb_choice with rfl | rfl
      · -- `b = b_nat = b0`
        have : lower_bound < (b0 : ℝ) := hb0_gt
        simpa [hb_nat_eqR] using this
      · -- `b = b_nat + 2`
        have : lower_bound < (b0 : ℝ) := hb0_gt
        have : lower_bound < (b0 : ℝ) + 2 := by linarith
        simpa [Nat.cast_add, hb_nat_eqR] using this

    -- Upper bound on `q`: since `n = m*q + b + r`, we have `m*q ≤ n`, hence `q ≤ n/m`.
    have hq_le_x : (q : ℝ) ≤ n_R / m_R := by
      have hn_eq' : n = m * q + b + r := by
        -- `m = s-2` by definition.
        simpa [m, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc] using hn_eq
      have hmq_le : (m : ℕ) * q ≤ n := by
        -- `m*q ≤ m*q + (b+r) = n`.
        have : (m : ℕ) * q ≤ (m : ℕ) * q + (b + r) := Nat.le_add_right _ _
        simpa [hn_eq', Nat.add_assoc] using this
      have hmul : (q : ℝ) * m_R ≤ n_R := by
        have : (m : ℝ) * (q : ℝ) ≤ n_R := by
          simpa [n_R] using (show ((m * q : ℕ) : ℝ) ≤ (n : ℝ) from by exact_mod_cast hmq_le)
        simpa [m_R, mul_assoc, mul_left_comm, mul_comm] using this
      have hmpos : (0 : ℝ) < m_R := hm_pos
      have hm_ne : m_R ≠ 0 := ne_of_gt hmpos
      have : (q : ℝ) * m_R / m_R ≤ n_R / m_R :=
        div_le_div_of_nonneg_right hmul (le_of_lt hmpos)
      -- `(q*m)/m = q`.
      simpa [hm_ne, mul_assoc, mul_left_comm, mul_comm] using this

    -- From `lower_bound < b`, derive `6*(n/m) < b^2 - b + 4` by squaring.
    have h6x : (6 : ℝ) * (n_R / m_R) < (b : ℝ) ^ 2 - (b : ℝ) + 4 := by
      -- `b - 1/2 > sqrt(6*(n/m)-3)`
      have hb0 : b ≠ 0 := by
        rcases hb_odd with ⟨k, hk⟩
        have hbpos : 0 < b := by
          -- `b = 2*k + 1` is positive.
          simp [hk]
        exact Nat.ne_of_gt hbpos
      have hb1 : (1 : ℕ) ≤ b := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hb0)
      have hbR_ge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
      have hb_shift_nonneg : (0 : ℝ) ≤ (b : ℝ) - (1 / 2 : ℝ) := by nlinarith [hbR_ge1]

      have hb_minus : (b : ℝ) - (1 / 2 : ℝ) > Real.sqrt (6 * (n_R / m_R) - 3) := by
        have : (1 / 2 : ℝ) + Real.sqrt (6 * (n_R / m_R) - 3) < (b : ℝ) := by
          simpa [lower_bound] using hbR_gt_lower
        linarith

      -- In the large regime we have `n/m > 108`, so certainly `6*(n/m)-3 ≥ 0`.
      have hB0 : (0 : ℝ) ≤ 6 * (n_R / m_R) - 3 := by
        have hnm_nat : 108 * m < n := Nat.lt_of_not_ge hmed
        have hnm_real : (108 : ℝ) * m_R < n_R := by
          simpa [n_R, m_R, Nat.cast_mul] using (show ((108 * m : ℕ) : ℝ) < (n : ℝ) from by
            exact_mod_cast hnm_nat)
        have hx108 : (108 : ℝ) < n_R / m_R := by
          have hm_ne : m_R ≠ 0 := ne_of_gt hm_pos
          have hmul : (108 : ℝ) * m_R < (n_R / m_R) * m_R := by
            simpa [hm_ne] using (show (108 : ℝ) * m_R < n_R from hnm_real)
          have hmul' : m_R * (108 : ℝ) < m_R * (n_R / m_R) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
          exact lt_of_mul_lt_mul_left hmul' (le_of_lt hm_pos)
        nlinarith [le_of_lt hx108]

      have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (6 * (n_R / m_R) - 3) := Real.sqrt_nonneg _
      have hb_sq : 6 * (n_R / m_R) - 3 < ((b : ℝ) - (1 / 2 : ℝ)) ^ 2 := by
        -- square both sides (both nonnegative)
        have : (Real.sqrt (6 * (n_R / m_R) - 3)) ^ 2 < ((b : ℝ) - (1 / 2 : ℝ)) ^ 2 := by
          nlinarith [hb_shift_nonneg, hb_minus, hsqrt0]
        simpa [pow_two, Real.sq_sqrt hB0] using this

      -- Expand `(b - 1/2)^2 = b^2 - b + 1/4` and rearrange.
      -- Use `2⁻¹`/`4⁻¹` so the rewrite matches simp's normal form.
      have hsq_exp :
          ((b : ℝ) - (2 : ℝ)⁻¹) ^ 2 = (b : ℝ) ^ 2 - (b : ℝ) + (4 : ℝ)⁻¹ := by
        ring
      have hb_sq' : 6 * (n_R / m_R) - 3 < (b : ℝ) ^ 2 - (b : ℝ) + (1 / 4 : ℝ) := by
        -- Rewrite `1/2` and `1/4` into `2⁻¹`/`4⁻¹` first, then apply `hsq_exp`.
        have hb_sq'' : 6 * (n_R / m_R) - 3 < ((b : ℝ) - (2 : ℝ)⁻¹) ^ 2 := by
          simpa [one_div] using hb_sq
        have : 6 * (n_R / m_R) - 3 < (b : ℝ) ^ 2 - (b : ℝ) + (4 : ℝ)⁻¹ := by
          simpa [hsq_exp] using hb_sq''
        simpa [one_div] using this
      -- Finish with a linear rearrangement.
      nlinarith [hb_sq']

    have : (6 : ℝ) * (q : ℝ) < (b : ℝ) ^ 2 - (b : ℝ) + 4 := by
      have : (6 : ℝ) * (q : ℝ) ≤ (6 : ℝ) * (n_R / m_R) := by nlinarith [hq_le_x]
      exact lt_of_le_of_lt this h6x
    -- Cast back to ℤ.
    have : 6 * (q : ℤ) < (b : ℤ) ^ 2 - (b : ℤ) + 4 := by
      exact_mod_cast this
    simpa using this
-/

/-!
### Nathanson parameter selection (large regime only)

Historically, this file experimented with a *uniform* parameter-selection lemma. That approach was
abandoned: the bounded regime needs separate handling (see `Experiments/NathansonWindowSearch.lean`
for counterexamples to naive uniform windows).

The proof path used by `cauchy_decomposition` relies only on this **large-regime** lemma, which is
analytic and self-contained.
-/

set_option maxHeartbeats 1200000 in
lemma nathanson_parameters_large (s : ℕ) (hs : 5 ≤ s) (n : ℕ) (_hn : 0 < n)
    (_hsmall0 : ¬ n ≤ s - 3) (hmed0 : ¬ n ≤ 108 * (s - 2)) :
    ∃ b q r : ℕ,
      r ≤ s - 4 ∧ Odd b ∧
        ((b : ℤ) ^ 2 < 4 * ((2 * q + b : ℕ) : ℤ)) ∧
        (3 * ((2 * q + b : ℕ) : ℤ) < (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4) ∧
        n = (s - 2) * q + b + r := by
  -- Large-ratio regime (`¬ n ≤ 108*(s-2)`): choose an odd `b` in a real interval and derive the
  -- required window inequalities.
  let m : ℕ := s - 2
  have hm : 3 ≤ m := by omega
  have hmed : ¬ n ≤ 108 * m := by simpa [m] using hmed0
  have hm_pos : 0 < (m : ℝ) := by
    rw [Nat.cast_pos]
    omega

  let n_R := (n : ℝ)
  let m_R := (m : ℝ)

  let lower_bound : ℝ := (1 / 2 : ℝ) + Real.sqrt (6 * (n_R / m_R) - 3)
  let upper_bound : ℝ := (2 / 3 : ℝ) + Real.sqrt (8 * (n_R / m_R) - 8)

  have h_gap : lower_bound + 4 < upper_bound := by
    have hnm_nat : 108 * m < n := Nat.lt_of_not_ge hmed
    have hnm_real : (108 : ℝ) * m_R < n_R := by
      simpa [n_R, m_R, Nat.cast_mul] using (show ((108 * m : ℕ) : ℝ) < (n : ℝ) from by
        exact_mod_cast hnm_nat)
    have hx : (108 : ℝ) < n_R / m_R := by
      have hm_ne : m_R ≠ 0 := ne_of_gt hm_pos
      have hmul : (108 : ℝ) * m_R < (n_R / m_R) * m_R := by
        simpa [hm_ne] using (show (108 : ℝ) * m_R < n_R from hnm_real)
      have hmul' : m_R * (108 : ℝ) < m_R * (n_R / m_R) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      exact lt_of_mul_lt_mul_left hmul' (le_of_lt hm_pos)
    simpa [lower_bound, upper_bound, n_R, m_R, mul_assoc, mul_left_comm, mul_comm, add_assoc,
      add_left_comm, add_comm] using (nathanson_gap_large (x := (n_R / m_R)) hx)

  have h_interval_len : lower_bound + 2 < upper_bound - 2 := by linarith [h_gap]
  obtain ⟨b0, hb0_odd, hb0_gt, hb0_lt⟩ :=
    GeometryOfNumbers.exists_odd_in_interval (L := lower_bound) (U := upper_bound - 2) h_interval_len

  have hb0_nonneg : 0 ≤ b0 := by
    have h_sqrt_nonneg : 0 ≤ Real.sqrt (6 * (n_R / m_R) - 3) := Real.sqrt_nonneg _
    have hlb_nonneg : 0 ≤ lower_bound := by
      dsimp [lower_bound]
      linarith
    have : 0 < b0 := by
      have : (0 : ℝ) < b0 := lt_of_le_of_lt hlb_nonneg hb0_gt
      exact_mod_cast this
    exact le_of_lt this

  let b_nat := b0.toNat
  have hb_nat_eq : (b_nat : ℤ) = b0 := Int.toNat_of_nonneg hb0_nonneg
  have hb_nat_odd : Odd b_nat := by
    rw [← Int.odd_coe_nat]
    convert hb0_odd

  have hb2_le_n : b_nat + 2 ≤ n := by
    have hm' : 3 ≤ m := hm
    have hnm : 108 * m < n := Nat.lt_of_not_ge hmed
    have h324 : 324 ≤ 108 * m := by nlinarith [hm']
    have hn324 : 324 < n := lt_of_le_of_lt h324 hnm
    have hn_large : 325 ≤ n := Nat.succ_le_iff.2 hn324
    have hnR0 : (0 : ℝ) ≤ n_R := by simp [n_R]
    have hnR14 : (14 : ℝ) ≤ n_R := by
      have : (14 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (le_trans (by decide : 14 ≤ 325) hn_large)
      simpa [n_R] using this

    have hm1 : (1 : ℝ) ≤ m_R := by
      have : (1 : ℕ) ≤ m := le_trans (by decide : 1 ≤ 3) hm'
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
      simpa [m_R] using this
    have hdiv : n_R / m_R ≤ n_R := div_le_self hnR0 hm1
    have hinside : 8 * (n_R / m_R) - 8 ≤ 8 * n_R := by nlinarith [hdiv]
    have hsqrt1 : Real.sqrt (8 * (n_R / m_R) - 8) ≤ Real.sqrt (8 * n_R) :=
      Real.sqrt_le_sqrt hinside

    have hsqrt2 : Real.sqrt (8 * n_R) ≤ n_R - 3 := by
      have hnonneg : 0 ≤ n_R - 3 := by linarith
      have hsq : 8 * n_R ≤ (n_R - 3) ^ 2 := by nlinarith [hnR14]
      exact (Real.sqrt_le_iff).2 ⟨hnonneg, by simpa [pow_two] using hsq⟩

    have hsqrt : Real.sqrt (8 * (n_R / m_R) - 8) ≤ n_R - 3 := le_trans hsqrt1 hsqrt2
    have hub_lt : (upper_bound : ℝ) < n_R := by
      dsimp [upper_bound]
      have hle :
          (2 / 3 : ℝ) + Real.sqrt (8 * (n_R / m_R) - 8) ≤ (2 / 3 : ℝ) + (n_R - 3) := by
        nlinarith [hsqrt]
      have hlt : (2 / 3 : ℝ) + (n_R - 3) < n_R := by linarith
      exact lt_of_le_of_lt hle hlt

    have hb0plus2_ltR : (b0 : ℝ) + 2 < n_R := by
      have hb0plus2_ltU : (b0 : ℝ) + 2 < upper_bound := by linarith [hb0_lt]
      exact lt_trans hb0plus2_ltU hub_lt
    have hb0plus2_leZ : (b0 : ℤ) + 2 ≤ (n : ℤ) := by
      have hb0plus2_ltR' : ((b0 + 2 : ℤ) : ℝ) < (n : ℝ) := by
        simpa [n_R, Int.cast_add, Int.cast_ofNat, add_assoc, add_left_comm, add_comm] using hb0plus2_ltR
      have hb0plus2_ltZ : (b0 + 2 : ℤ) < (n : ℤ) := by
        exact_mod_cast hb0plus2_ltR'
      exact le_of_lt hb0plus2_ltZ
    have : (b_nat + 2 : ℤ) ≤ (n : ℤ) := by
      simpa [hb_nat_eq, Nat.cast_add] using hb0plus2_leZ
    exact_mod_cast this

  obtain ⟨b, q, r, hb_choice, hr_le, hn_eq⟩ :=
    exists_qr_with_remainder_le (s := s) (n := n) (b := b_nat) hs hb2_le_n

  have hb_odd : Odd b := by
    rcases hb_choice with rfl | rfl
    · exact hb_nat_odd
    · exact hb_nat_odd.add_even (by simp)

  refine ⟨b, q, r, hr_le, hb_odd, ?_, ?_, hn_eq⟩

  · -- Inequality 1
    apply (int_b2_lt_four_two_mul_q_add_b_iff b q).2
    have hb_nat_eqR : (b_nat : ℝ) = (b0 : ℝ) := by
      simpa using congrArg (fun t : ℤ => (t : ℝ)) hb_nat_eq
    have hbR_lt_upper : (b : ℝ) < upper_bound := by
      rcases hb_choice with rfl | rfl
      ·
        have hb0lt : (b_nat : ℝ) < upper_bound - 2 := by
          have : (b0 : ℝ) < upper_bound - 2 := hb0_lt
          simpa [hb_nat_eqR] using this
        have : (b_nat : ℝ) < upper_bound := by linarith
        simpa using this
      ·
        have hb0lt : (b_nat : ℝ) < upper_bound - 2 := by
          have : (b0 : ℝ) < upper_bound - 2 := hb0_lt
          simpa [hb_nat_eqR] using this
        have : (b_nat : ℝ) + 2 < upper_bound := by linarith
        simpa [Nat.cast_add] using this

    have hb0' : b ≠ 0 := by
      rcases hb_odd with ⟨k, hk⟩
      have hbpos : 0 < b := by simp [hk]
      exact Nat.ne_of_gt hbpos
    have hb1 : (1 : ℕ) ≤ b := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hb0')
    have hbR_ge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    have hb_shift_nonneg : (0 : ℝ) ≤ (b : ℝ) - (2 / 3 : ℝ) := by nlinarith [hbR_ge1]

    set x : ℝ := n_R / m_R
    have hb_minus_lt : (b : ℝ) - (2 / 3 : ℝ) < Real.sqrt (8 * x - 8) := by
      have : (b : ℝ) < (2 / 3 : ℝ) + Real.sqrt (8 * x - 8) := by
        simpa [x, upper_bound] using hbR_lt_upper
      linarith

    have hA0 : (0 : ℝ) ≤ 8 * x - 8 := by
      have hnm_nat : 108 * m < n := Nat.lt_of_not_ge hmed
      have hnm_real : (108 : ℝ) * m_R < n_R := by
        simpa [n_R, m_R, Nat.cast_mul] using (show ((108 * m : ℕ) : ℝ) < (n : ℝ) from by
          exact_mod_cast hnm_nat)
      have hx108 : (108 : ℝ) < x := by
        have hm_ne : m_R ≠ 0 := ne_of_gt hm_pos
        have hmul : (108 : ℝ) * m_R < x * m_R := by
          simpa [x, hm_ne] using hnm_real
        have hmul' : m_R * (108 : ℝ) < m_R * x := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
        exact lt_of_mul_lt_mul_left hmul' (le_of_lt hm_pos)
      nlinarith [le_of_lt hx108]

    have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (8 * x - 8) := Real.sqrt_nonneg _
    have hb_sq_lt : ((b : ℝ) - (2 / 3 : ℝ)) ^ 2 < 8 * x - 8 := by
      have : ((b : ℝ) - (2 / 3 : ℝ)) ^ 2 < (Real.sqrt (8 * x - 8)) ^ 2 := by
        nlinarith [hb_shift_nonneg, hb_minus_lt, hsqrt0]
      simpa [pow_two, Real.sq_sqrt hA0] using this

    have hquad :
        (b : ℝ) ^ 2 - 4 * (b : ℝ) < 8 * x - (8 / 3 : ℝ) * (b : ℝ) - (76 / 9 : ℝ) := by
      have hsq_exp :
          ((b : ℝ) - (2 / 3 : ℝ)) ^ 2 = (b : ℝ) ^ 2 - (4 / 3 : ℝ) * (b : ℝ) + (4 / 9 : ℝ) := by
        ring
      have hb_sq_lt' :
          (b : ℝ) ^ 2 - (4 / 3 : ℝ) * (b : ℝ) + (4 / 9 : ℝ) < 8 * x - 8 := by
        simpa [hsq_exp] using hb_sq_lt
      linarith [hb_sq_lt']

    have hn_eq' : n = m * q + b + r := by
      simpa [m, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc] using hn_eq
    have hx_eq : x = (q : ℝ) + ((b : ℝ) + (r : ℝ)) / m_R := by
      have hm_ne : m_R ≠ 0 := ne_of_gt hm_pos
      have hn_eqR : n_R = m_R * (q : ℝ) + ((b : ℝ) + (r : ℝ)) := by
        have : (n : ℝ) = ((m * q + b + r : ℕ) : ℝ) := by exact_mod_cast hn_eq'
        simpa [n_R, m_R, Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm,
          mul_assoc, mul_left_comm, mul_comm] using this
      dsimp [x]
      calc
        n_R / m_R = (m_R * (q : ℝ) + ((b : ℝ) + (r : ℝ))) / m_R := by
          simp [hn_eqR]
        _ = (m_R * (q : ℝ)) / m_R + ((b : ℝ) + (r : ℝ)) / m_R := by
          simpa using (add_div (m_R * (q : ℝ)) ((b : ℝ) + (r : ℝ)) m_R)
        _ = (q : ℝ) + ((b : ℝ) + (r : ℝ)) / m_R := by
          simp [hm_ne]

    have hr_le_m : (r : ℝ) / m_R ≤ 1 := by
      have hmpos : (0 : ℝ) < m_R := hm_pos
      have hr_le' : (r : ℝ) ≤ (m : ℝ) := by
        have : r ≤ m := by
          have hm2 : m - 2 ≤ m := by omega
          have : r ≤ m - 2 := by simpa [m] using hr_le
          exact le_trans this hm2
        exact_mod_cast this
      have : (r : ℝ) / m_R ≤ (m : ℝ) / m_R :=
        div_le_div_of_nonneg_right hr_le' (le_of_lt hmpos)
      simpa [m_R, div_self (ne_of_gt hmpos)] using this

    have hmR_ge3 : (3 : ℝ) ≤ m_R := by
      simpa [m_R] using (show (3 : ℝ) ≤ (m : ℝ) from by exact_mod_cast hm)
    have hb0R : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (Nat.zero_le b)
    have hb_div : (b : ℝ) / m_R ≤ (b : ℝ) / 3 := by
      have h1 : (1 : ℝ) / m_R ≤ (1 : ℝ) / 3 := by
        simpa [one_div] using
          (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (3 : ℝ)) hmR_ge3)
      have : (b : ℝ) * ((1 : ℝ) / m_R) ≤ (b : ℝ) * ((1 : ℝ) / 3) :=
        mul_le_mul_of_nonneg_left h1 hb0R
      simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    have hbr_div : ((b : ℝ) + (r : ℝ)) / m_R ≤ (b : ℝ) / 3 + 1 := by
      have hadd : ((b : ℝ) + (r : ℝ)) / m_R = (b : ℝ) / m_R + (r : ℝ) / m_R := by
        simpa using (add_div (b : ℝ) (r : ℝ) m_R)
      nlinarith [hadd, hb_div, hr_le_m]

    have herr :
        8 * ((b : ℝ) + (r : ℝ)) / m_R ≤ (8 / 3 : ℝ) * (b : ℝ) + (76 / 9 : ℝ) := by
      have htmp : 8 * (((b : ℝ) + (r : ℝ)) / m_R) ≤ 8 * ((b : ℝ) / 3 + 1) :=
        mul_le_mul_of_nonneg_left hbr_div (by norm_num)
      have hlin : 8 * ((b : ℝ) / 3 + 1) = (8 / 3 : ℝ) * (b : ℝ) + (8 : ℝ) := by ring
      have hconst : (8 : ℝ) ≤ (76 / 9 : ℝ) := by norm_num
      have h1 : 8 * (((b : ℝ) + (r : ℝ)) / m_R) ≤ (8 / 3 : ℝ) * (b : ℝ) + (8 : ℝ) := by
        have : 8 * ((b : ℝ) / 3 + 1) = (8 / 3 : ℝ) * (b : ℝ) + (8 : ℝ) := hlin
        exact le_trans htmp (by simp [this])
      have h2 : (8 / 3 : ℝ) * (b : ℝ) + (8 : ℝ) ≤ (8 / 3 : ℝ) * (b : ℝ) + (76 / 9 : ℝ) := by
        nlinarith [hconst]
      have h1' : 8 * ((b : ℝ) + (r : ℝ)) / m_R ≤ (8 / 3 : ℝ) * (b : ℝ) + (8 : ℝ) := by
        have hrewrite :
            (8 : ℝ) * ((b : ℝ) + (r : ℝ)) / m_R = 8 * (((b : ℝ) + (r : ℝ)) / m_R) := by
          simpa [mul_assoc] using (mul_div_assoc (8 : ℝ) ((b : ℝ) + (r : ℝ)) m_R)
        simpa [hrewrite] using h1
      exact le_trans h1' h2

    have hbqR : (b : ℝ) ^ 2 - 4 * (b : ℝ) < 8 * (q : ℝ) := by
      have hq_eq : (q : ℝ) = x - ((b : ℝ) + (r : ℝ)) / m_R := by nlinarith [hx_eq]
      have haux : 8 * x - (8 / 3 : ℝ) * (b : ℝ) - (76 / 9 : ℝ) ≤ 8 * (q : ℝ) := by
        have hq8 : (8 : ℝ) * (q : ℝ) = 8 * x - 8 * (((b : ℝ) + (r : ℝ)) / m_R) := by
          nlinarith [hq_eq]
        nlinarith [herr, hq8]
      exact lt_of_lt_of_le hquad haux

    have hbqZ : (b : ℤ) ^ 2 - 4 * (b : ℤ) < 8 * (q : ℤ) := by
      exact_mod_cast hbqR
    simpa using hbqZ

  · -- Inequality 2
    apply (int_three_two_mul_q_add_b_lt_iff b q).2
    have hb_nat_eqR : (b_nat : ℝ) = (b0 : ℝ) := by
      simpa using congrArg (fun t : ℤ => (t : ℝ)) hb_nat_eq
    have hbR_gt_lower : lower_bound < (b : ℝ) := by
      rcases hb_choice with rfl | rfl
      ·
        have : lower_bound < (b0 : ℝ) := hb0_gt
        simpa [hb_nat_eqR] using this
      ·
        have : lower_bound < (b0 : ℝ) := hb0_gt
        have : lower_bound < (b0 : ℝ) + 2 := by linarith
        simpa [Nat.cast_add, hb_nat_eqR] using this

    have hq_le_x : (q : ℝ) ≤ n_R / m_R := by
      have hn_eq' : n = m * q + b + r := by
        simpa [m, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc] using hn_eq
      have hmq_le : (m : ℕ) * q ≤ n := by
        have h0 : (m : ℕ) * q ≤ (m : ℕ) * q + (b + r) := Nat.le_add_right _ _
        have hn_eq'' : n = (m * q) + (b + r) := by
          -- reassociate `m*q + b + r` as `m*q + (b+r)`
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hn_eq'
        have hn_eq''' : (m * q) + (b + r) = n := hn_eq''.symm
        exact le_trans h0 (le_of_eq hn_eq''')
      have hmul : (q : ℝ) * m_R ≤ n_R := by
        have : (m : ℝ) * (q : ℝ) ≤ n_R := by
          simpa [n_R] using (show ((m * q : ℕ) : ℝ) ≤ (n : ℝ) from by exact_mod_cast hmq_le)
        simpa [m_R, mul_assoc, mul_left_comm, mul_comm] using this
      have hmpos : (0 : ℝ) < m_R := hm_pos
      have hm_ne : m_R ≠ 0 := ne_of_gt hmpos
      have : (q : ℝ) * m_R / m_R ≤ n_R / m_R :=
        div_le_div_of_nonneg_right hmul (le_of_lt hmpos)
      simpa [hm_ne, mul_assoc, mul_left_comm, mul_comm] using this

    have h6x : (6 : ℝ) * (n_R / m_R) < (b : ℝ) ^ 2 - (b : ℝ) + 4 := by
      have hb0' : b ≠ 0 := by
        rcases hb_odd with ⟨k, hk⟩
        have hbpos : 0 < b := by simp [hk]
        exact Nat.ne_of_gt hbpos
      have hb1 : (1 : ℕ) ≤ b := Nat.succ_le_iff.2 (Nat.pos_of_ne_zero hb0')
      have hbR_ge1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
      have hb_shift_nonneg : (0 : ℝ) ≤ (b : ℝ) - (1 / 2 : ℝ) := by nlinarith [hbR_ge1]
      have hb_minus : (b : ℝ) - (1 / 2 : ℝ) > Real.sqrt (6 * (n_R / m_R) - 3) := by
        have : (1 / 2 : ℝ) + Real.sqrt (6 * (n_R / m_R) - 3) < (b : ℝ) := by
          simpa [lower_bound] using hbR_gt_lower
        linarith
      have hB0 : (0 : ℝ) ≤ 6 * (n_R / m_R) - 3 := by
        have hnm_nat : 108 * m < n := Nat.lt_of_not_ge hmed
        have hnm_real : (108 : ℝ) * m_R < n_R := by
          simpa [n_R, m_R, Nat.cast_mul] using (show ((108 * m : ℕ) : ℝ) < (n : ℝ) from by
            exact_mod_cast hnm_nat)
        have hx108 : (108 : ℝ) < n_R / m_R := by
          have hm_ne : m_R ≠ 0 := ne_of_gt hm_pos
          have hmul : (108 : ℝ) * m_R < (n_R / m_R) * m_R := by
            simpa [hm_ne] using (show (108 : ℝ) * m_R < n_R from hnm_real)
          have hmul' : m_R * (108 : ℝ) < m_R * (n_R / m_R) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
          exact lt_of_mul_lt_mul_left hmul' (le_of_lt hm_pos)
        nlinarith [le_of_lt hx108]

      have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (6 * (n_R / m_R) - 3) := Real.sqrt_nonneg _
      have hb_sq : 6 * (n_R / m_R) - 3 < ((b : ℝ) - (1 / 2 : ℝ)) ^ 2 := by
        have : (Real.sqrt (6 * (n_R / m_R) - 3)) ^ 2 < ((b : ℝ) - (1 / 2 : ℝ)) ^ 2 := by
          nlinarith [hb_shift_nonneg, hb_minus, hsqrt0]
        simpa [pow_two, Real.sq_sqrt hB0] using this

      have hsq_exp :
          ((b : ℝ) - (2 : ℝ)⁻¹) ^ 2 = (b : ℝ) ^ 2 - (b : ℝ) + (4 : ℝ)⁻¹ := by
        ring
      have hb_sq' : 6 * (n_R / m_R) - 3 < (b : ℝ) ^ 2 - (b : ℝ) + (1 / 4 : ℝ) := by
        have hb_sq'' : 6 * (n_R / m_R) - 3 < ((b : ℝ) - (2 : ℝ)⁻¹) ^ 2 := by
          simpa [one_div] using hb_sq
        have : 6 * (n_R / m_R) - 3 < (b : ℝ) ^ 2 - (b : ℝ) + (4 : ℝ)⁻¹ := by
          simpa [hsq_exp] using hb_sq''
        simpa [one_div] using this
      nlinarith [hb_sq']

    have : (6 : ℝ) * (q : ℝ) < (b : ℝ) ^ 2 - (b : ℝ) + 4 := by
      have : (6 : ℝ) * (q : ℝ) ≤ (6 : ℝ) * (n_R / m_R) := by nlinarith [hq_le_x]
      exact lt_of_le_of_lt this h6x
    have : 6 * (q : ℤ) < (b : ℤ) ^ 2 - (b : ℤ) + 4 := by
      exact_mod_cast this
    simpa using this


set_option maxHeartbeats 600000

/-- If `x^2 + y^2 + z^2 ≡ 3 (mod 8)`, then each of `x,y,z` is odd.

We implement this as a small finite check in `ZMod 4`: a sum of three squares is `3` iff each square
is `1`, which forces each term to be odd.
-/
lemma odd_of_sum_three_squares_mod8_three (x y z N : ℕ)
    (hxyz : x ^ 2 + y ^ 2 + z ^ 2 = N) (hN8 : N % 8 = 3) :
    Odd x ∧ Odd y ∧ Odd z := by
  have hN_mod4 : N % 4 = 3 := by
    have h8 : N ≡ 3 [MOD 8] := by
      have : N % 8 = 3 % 8 := by simpa using hN8
      simpa [Nat.ModEq] using this
    have h4 : N ≡ 3 [MOD 4] := Nat.ModEq.of_dvd (m := 4) (n := 8) (by decide : 4 ∣ 8) h8
    simpa [Nat.ModEq] using h4

  haveI : NeZero (4 : ℕ) := ⟨by decide⟩
  have hN_zmod4 : (N : ZMod 4) = (3 : ZMod 4) := by
    apply (ZMod.val_injective 4)
    have hNv : (N : ZMod 4).val = 3 := by
      simp [ZMod.val_natCast, hN_mod4]
    have h3v : (3 : ZMod 4).val = 3 := by
      simpa using (ZMod.val_natCast_of_lt (n := 4) (a := 3) (by decide : 3 < 4))
    simp [hNv, h3v]

  have hmod4 :
      ((x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = (3 : ZMod 4) := by
    have hcast : ((x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ZMod 4) = (N : ZMod 4) := by
      simp [hxyz]
    simpa [pow_two, Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm, hN_zmod4] using hcast

  have hsq :
      ((x : ZMod 4) ^ 2 = 1) ∧ ((y : ZMod 4) ^ 2 = 1) ∧ ((z : ZMod 4) ^ 2 = 1) := by
    have h :
        ∀ X Y Z : ZMod 4,
          X ^ 2 + Y ^ 2 + Z ^ 2 = 3 → (X ^ 2 = 1 ∧ Y ^ 2 = 1 ∧ Z ^ 2 = 1) := by
      decide
    exact h (x : ZMod 4) (y : ZMod 4) (z : ZMod 4) hmod4

  have odd_of_sq1 : ∀ n : ℕ, ((n : ZMod 4) ^ 2 = 1) → Odd n := by
    intro n hn
    rcases Nat.even_or_odd n with hn_even | hn_odd
    · rcases hn_even with ⟨k, rfl⟩
      have h22 : ((2 : ZMod 4) * (2 : ZMod 4)) = 0 := by decide
      have h0' : ((2 * k : ℕ) : ZMod 4) ^ 2 = 0 := by
        simp [pow_two, mul_left_comm, mul_comm, h22]
      have h0 : ((k + k : ℕ) : ZMod 4) ^ 2 = 0 := by
        simpa [two_mul] using h0'
      have : (0 : ZMod 4) = 1 := by
        simpa using (h0.symm.trans hn)
      exact False.elim ((by decide : (0 : ZMod 4) ≠ 1) this)
    · exact hn_odd

  refine ⟨odd_of_sq1 x hsq.1, odd_of_sq1 y hsq.2.1, odd_of_sq1 z hsq.2.2⟩

/-- For odd `b,x,y,z`, we can choose a sign `±z` so that `4 ∣ (b+x+y±z)`.

This is the “sign choice” step in the Nathanson/Cauchy four-square packaging.
-/
lemma exists_sign_zpm_dvd4_of_odds (b x y z : ℕ) (hb : Odd b) (hx : Odd x) (hy : Odd y) (hz : Odd z) :
    ∃ zpm : ℤ,
      (zpm = (z : ℤ) ∨ zpm = -(z : ℤ)) ∧
        ((4 : ℤ) ∣ (b : ℤ) + (x : ℤ) + (y : ℤ) + zpm) := by
  -- Work modulo 4: each odd residue is `1` or `3`, so `b+x+y` is `1` or `3` and we can choose `±z`
  -- to cancel it.
  let b4 : ZMod 4 := (b : ZMod 4)
  let x4 : ZMod 4 := (x : ZMod 4)
  let y4 : ZMod 4 := (y : ZMod 4)
  let z4 : ZMod 4 := (z : ZMod 4)

  have sq1_of_odd : ∀ n : ℕ, Odd n → ((n : ZMod 4) ^ 2 = 1) := by
    intro n hn
    rcases hn with ⟨k, rfl⟩
    have h4 : (4 : ZMod 4) = 0 := by decide
    have hsq :
        ((2 * k + 1 : ℕ) : ZMod 4) ^ 2 =
          (4 : ZMod 4) * ((k * (k + 1) : ℕ) : ZMod 4) + 1 := by
      simp [pow_two, mul_add, add_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      ring_nf
    simpa [h4] using (hsq.trans (by simp [h4]))

  have hb_sq1 : b4 ^ 2 = 1 := by simpa [b4] using sq1_of_odd b hb
  have hx_sq1 : x4 ^ 2 = 1 := by simpa [x4] using sq1_of_odd x hx
  have hy_sq1 : y4 ^ 2 = 1 := by simpa [y4] using sq1_of_odd y hy
  have hz_sq1 : z4 ^ 2 = 1 := by simpa [z4] using sq1_of_odd z hz

  have sq1_cases : ∀ t : ZMod 4, t ^ 2 = 1 → (t = 1 ∨ t = 3) := by
    intro t ht
    fin_cases t
    · cases (by simpa using ht)
    · exact Or.inl rfl
    · cases (by simpa using ht)
    · exact Or.inr rfl

  have hb4_cases : b4 = 1 ∨ b4 = 3 := sq1_cases b4 hb_sq1
  have hx4_cases : x4 = 1 ∨ x4 = 3 := sq1_cases x4 hx_sq1
  have hy4_cases : y4 = 1 ∨ y4 = 3 := sq1_cases y4 hy_sq1
  have hz4_cases : z4 = 1 ∨ z4 = 3 := sq1_cases z4 hz_sq1

  let sum3 : ZMod 4 := b4 + x4 + y4
  have hsum3_cases : sum3 = 1 ∨ sum3 = 3 := by
    rcases hb4_cases with hb1 | hb3
    · rcases hx4_cases with hx1 | hx3
      · rcases hy4_cases with hy1 | hy3
        · have h : (1 : ZMod 4) + 1 + 1 = 3 := by decide
          exact Or.inr (by simpa [sum3, hb1, hx1, hy1, add_assoc, add_left_comm, add_comm] using h)
        · have h : (1 : ZMod 4) + 1 + 3 = 1 := by decide
          exact Or.inl (by simpa [sum3, hb1, hx1, hy3, add_assoc, add_left_comm, add_comm] using h)
      · rcases hy4_cases with hy1 | hy3
        · have h : (1 : ZMod 4) + 3 + 1 = 1 := by decide
          exact Or.inl (by simpa [sum3, hb1, hx3, hy1, add_assoc, add_left_comm, add_comm] using h)
        · have h : (1 : ZMod 4) + 3 + 3 = 3 := by decide
          exact Or.inr (by simpa [sum3, hb1, hx3, hy3, add_assoc, add_left_comm, add_comm] using h)
    · rcases hx4_cases with hx1 | hx3
      · rcases hy4_cases with hy1 | hy3
        · have h : (3 : ZMod 4) + 1 + 1 = 1 := by decide
          exact Or.inl (by simpa [sum3, hb3, hx1, hy1, add_assoc, add_left_comm, add_comm] using h)
        · have h : (3 : ZMod 4) + 1 + 3 = 3 := by decide
          exact Or.inr (by simpa [sum3, hb3, hx1, hy3, add_assoc, add_left_comm, add_comm] using h)
      · rcases hy4_cases with hy1 | hy3
        · have h : (3 : ZMod 4) + 3 + 1 = 3 := by decide
          exact Or.inr (by simpa [sum3, hb3, hx3, hy1, add_assoc, add_left_comm, add_comm] using h)
        · have h : (3 : ZMod 4) + 3 + 3 = 1 := by decide
          exact Or.inl (by simpa [sum3, hb3, hx3, hy3, add_assoc, add_left_comm, add_comm] using h)

  by_cases hsum_eq : sum3 = z4
  · -- If `b+x+y ≡ z`, pick `-z`.
    refine ⟨-(z : ℤ), Or.inr rfl, ?_⟩
    have hzmod : (((b : ℤ) + (x : ℤ) + (y : ℤ) - (z : ℤ) : ℤ) : ZMod 4) = 0 := by
      have : sum3 - z4 = 0 := sub_eq_zero.2 hsum_eq
      simpa [sum3, b4, x4, y4, z4, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    have : ((4 : ℤ) ∣ (b : ℤ) + (x : ℤ) + (y : ℤ) - (z : ℤ)) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd ((b : ℤ) + (x : ℤ) + (y : ℤ) - (z : ℤ)) 4).1 hzmod
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  · -- Otherwise, `b+x+y+z ≡ 0 (mod 4)`, so pick `+z`.
    refine ⟨(z : ℤ), Or.inl rfl, ?_⟩
    have hsum_add : sum3 + z4 = 0 := by
      rcases hsum3_cases with hs1 | hs3 <;> rcases hz4_cases with hz1 | hz3
      · exfalso; exact hsum_eq (by simp [hs1, hz1])
      · have : (1 : ZMod 4) + 3 = 0 := by decide
        simpa [hs1, hz3] using this
      · have : (3 : ZMod 4) + 1 = 0 := by decide
        simpa [hs3, hz1] using this
      · exfalso; exact hsum_eq (by simp [hs3, hz3])
    have hzmod : (((b : ℤ) + (x : ℤ) + (y : ℤ) + (z : ℤ) : ℤ) : ZMod 4) = 0 := by
      simpa [sum3, b4, x4, y4, z4, add_assoc, add_left_comm, add_comm] using hsum_add
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd ((b : ℤ) + (x : ℤ) + (y : ℤ) + (z : ℤ)) 4).1 hzmod

/-- If `t` is even, then `4 ∣ 2*t`. -/
lemma dvd_four_two_mul_of_even (t : ℤ) (ht : Even t) : (4 : ℤ) ∣ 2 * t := by
  rcases ht with ⟨k, rfl⟩
  refine ⟨k, ?_⟩
  ring

/-- If `4 ∣ a` and `4 ∣ b` then `4 ∣ a - b`. -/
lemma dvd_four_sub_of_dvd_four {a b : ℤ} (ha : (4 : ℤ) ∣ a) (hb : (4 : ℤ) ∣ b) : (4 : ℤ) ∣ a - b := by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  refine ⟨ka - kb, ?_⟩
  ring

/-- Hadamard linear identity: if the Hadamard numerators are `4`-multiples, then `b = s+t+u+v`. -/
lemma hadamard_linear_identity (b Snum Tnum Unum Vnum sZ tZ uZ vZ : ℤ)
    (h4ne : (4 : ℤ) ≠ 0)
    (hs : Snum = 4 * sZ) (ht : Tnum = 4 * tZ) (hu : Unum = 4 * uZ) (hv : Vnum = 4 * vZ)
    (hsum : Snum + Tnum + Unum + Vnum = 4 * b) :
    b = sZ + tZ + uZ + vZ := by
  calc
    b = (4 * b) / 4 := by simp [h4ne]
    _ = (Snum + Tnum + Unum + Vnum) / 4 := by simp [hsum]
    _ = (4 * sZ + 4 * tZ + 4 * uZ + 4 * vZ) / 4 := by simp [hs, ht, hu, hv]
    _ = sZ + tZ + uZ + vZ := by
      have : (4 * sZ + 4 * tZ + 4 * uZ + 4 * vZ) = 4 * (sZ + tZ + uZ + vZ) := by ring
      simp [this, h4ne]

/-- Hadamard square identity: the Hadamard transform preserves the sum of squares (up to scaling). -/
lemma hadamard_square_identity (b x y z : ℤ) :
    (b + x + y + z) ^ 2 + (b + x - y - z) ^ 2 + (b - x + y - z) ^ 2 + (b - x - y + z) ^ 2 =
      4 * (b ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) := by
  simp [pow_two]
  ring

/-- If the Hadamard numerators are `4`-multiples and satisfy the Hadamard square identity, cancel
one factor of `4` to recover the sum-of-squares identity for the divided terms. -/
lemma hadamard_sum_sq_cancel (Snum Tnum Unum Vnum sZ tZ uZ vZ rhs : ℤ)
    (h4ne : (4 : ℤ) ≠ 0)
    (hs : Snum = 4 * sZ) (ht : Tnum = 4 * tZ) (hu : Unum = 4 * uZ) (hv : Vnum = 4 * vZ)
    (hhad : Snum ^ 2 + Tnum ^ 2 + Unum ^ 2 + Vnum ^ 2 = 4 * rhs) :
    4 * (sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2) = rhs := by
  have h1 :
      Snum ^ 2 + Tnum ^ 2 + Unum ^ 2 + Vnum ^ 2 =
        16 * (sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2) := by
    simp [hs, ht, hu, hv, pow_two]
    ring_nf
  have h2 : 16 * (sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2) = 4 * rhs :=
    h1.symm.trans hhad
  have h2' :
      (4 : ℤ) * (4 * (sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2)) = (4 : ℤ) * rhs := by
    calc
      (4 : ℤ) * (4 * (sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2))
          = (16 : ℤ) * (sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2) := by ring
      _ = (4 : ℤ) * rhs := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using h2
  exact mul_left_cancel₀ h4ne h2'

/-- Derive `a = s^2+t^2+u^2+v^2` from:

- `x^2+y^2+z^2 = 4a - b^2` (as integers),
- `4*(s^2+...+v^2) = b^2 + x^2 + y^2 + z^2`,

by cancelling a factor of `4`. -/
lemma hadamard_derive_a_eq_sum_sq (a b : ℕ) (x y z sZ tZ uZ vZ : ℤ)
    (h4ne : (4 : ℤ) ≠ 0)
    (hxyzZ : x ^ 2 + y ^ 2 + z ^ 2 = 4 * (a : ℤ) - (b : ℤ) ^ 2)
    (hsum_sq : 4 * (sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2) = (b : ℤ) ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) :
    (a : ℤ) = sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2 := by
  have hRHS : (b : ℤ) ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 4 * (a : ℤ) := by
    -- Rearranged: `b^2 + (x^2+y^2+z^2) = 4a`.
    have htmp := congrArg (fun t : ℤ => (b : ℤ) ^ 2 + t) hxyzZ
    have htmp' := htmp
    ring_nf at htmp'
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using htmp'
  have h4eq : (4 : ℤ) * (sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2) = (4 : ℤ) * (a : ℤ) := by
    simpa [hRHS] using hsum_sq.trans hRHS
  exact (mul_left_cancel₀ h4ne h4eq).symm

/-- Cauchy/CS inequality in `ℤ`:
\[
  (p+q+r)^2 \le 3(p^2+q^2+r^2).
\]

We keep it as a named lemma because it is the key “nonnegativity driver” in `cauchy_lemma`. -/
lemma cauchy_three_squares_sum_le (p q r : ℤ) :
    (p + q + r) ^ 2 ≤ 3 * (p ^ 2 + q ^ 2 + r ^ 2) := by
  have hnn : 0 ≤ (p - q) ^ 2 + (q - r) ^ 2 + (r - p) ^ 2 := by
    exact
      add_nonneg (add_nonneg (sq_nonneg (p - q)) (sq_nonneg (q - r)))
        (sq_nonneg (r - p))
  have hdiff : 0 ≤ 3 * (p ^ 2 + q ^ 2 + r ^ 2) - (p + q + r) ^ 2 := by
    -- `3*sumSq - sum^2 = (p-q)^2 + (q-r)^2 + (r-p)^2`
    have :
        3 * (p ^ 2 + q ^ 2 + r ^ 2) - (p + q + r) ^ 2
          = (p - q) ^ 2 + (q - r) ^ 2 + (r - p) ^ 2 := by
      ring
    simpa [this] using hnn
  exact (sub_nonneg).1 hdiff

/-- Core nonnegativity step in Nathanson/Cauchy:

Given `b = w+x+y+z` and `a = w^2+x^2+y^2+z^2`, the window inequality
\[
  3a < b^2 + 2b + 4
\]
forces `w ≥ 0`. -/
lemma cauchy_component_nonneg (a b : ℕ) (h3a_lt : 3 * (a : ℤ) < (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4)
    (w x y z : ℤ) (hsum : (b : ℤ) = w + x + y + z) (hsq : (a : ℤ) = w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2) :
    0 ≤ w := by
  by_contra hw0
  have hwlt : w < 0 := lt_of_not_ge hw0
  rcases Int.eq_negSucc_of_lt_zero hwlt with ⟨k, hk⟩
  let K : ℤ := (k.succ : ℤ)
  have hKpos : (1 : ℤ) ≤ K := by
    -- `K = (k+1)` in ℤ
    dsimp [K]
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
  have hw : w = -K := by
    -- `Int.negSucc k = - (k+1)`
    simpa [K, Int.negSucc_eq] using hk

  have hsum3 : x + y + z = (b : ℤ) - w := by
    -- linear rearrangement of `hsum`
    linarith [hsum]

  have hcs3 : (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) :=
    cauchy_three_squares_sum_le x y z

  -- Lower bound `3a ≥ 3w^2 + (x+y+z)^2` using C-S on the remaining three terms.
  have h3a_ge : 3 * (a : ℤ) ≥ 3 * (w ^ 2) + (x + y + z) ^ 2 := by
    -- from `hsq` and `hcs3` (no `linarith` needed)
    have hsq' : 3 * (a : ℤ) = 3 * (w ^ 2) + 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
      have := congrArg (fun t : ℤ => 3 * t) hsq
      simpa [mul_add, add_assoc, add_left_comm, add_comm] using this
    have hle0 :
        (x + y + z) ^ 2 + 3 * (w ^ 2) ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) + 3 * (w ^ 2) := by
      exact add_le_add_left hcs3 (3 * (w ^ 2))
    have hle :
        3 * (w ^ 2) + (x + y + z) ^ 2 ≤ 3 * (w ^ 2) + 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
      -- just commute the added term
      simpa [add_assoc, add_left_comm, add_comm] using hle0
    have hle' : 3 * (w ^ 2) + (x + y + z) ^ 2 ≤ 3 * (a : ℤ) := by
      -- rewrite the RHS using `hsq'`
      exact le_trans hle (by simpa using (le_of_eq hsq'.symm))
    simpa [ge_iff_le] using hle'

  -- Now show `3w^2 + (b - w)^2 ≥ b^2 + 2b + 4` for `w = -(k+1)`.
  have hbnn : (0 : ℤ) ≤ (b : ℤ) := by exact_mod_cast (Nat.zero_le b)
  have hbase :
      3 * (w ^ 2) + ((b : ℤ) - w) ^ 2 ≥ (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4 := by
    -- rewrite using `w = -K` and reduce to `K ≥ 1`.
    have hrew :
        3 * (w ^ 2) + ((b : ℤ) - w) ^ 2 = (b : ℤ) ^ 2 + 2 * (b : ℤ) * K + 4 * (K ^ 2) := by
      -- Avoid `simp` heartbeats: rewrite `w`, expand squares, then `ring`.
      rw [hw]
      ring_nf
    -- `b^2 + 2*b + 4 ≤ b^2 + 2*b*K + 4*K^2` if `b ≥ 0` and `K ≥ 1`.
    have hmono :
        (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4 ≤ (b : ℤ) ^ 2 + 2 * (b : ℤ) * K + 4 * (K ^ 2) := by
      have hb2 : 0 ≤ (2 : ℤ) * (b : ℤ) := by
        exact mul_nonneg (by decide : (0 : ℤ) ≤ 2) hbnn
      have hbterm : 2 * (b : ℤ) ≤ 2 * (b : ℤ) * K := by
        -- multiply `1 ≤ K` by the nonnegative factor `2*b`
        have := mul_le_mul_of_nonneg_left hKpos hb2
        -- `(2*b)*1 = 2*b`
        simpa [mul_one, mul_assoc] using this
      have hKnonneg : (0 : ℤ) ≤ K := le_trans (by decide : (0 : ℤ) ≤ 1) hKpos
      have hKsq : (1 : ℤ) ≤ K ^ 2 := by
        -- `1 ≤ K` ⇒ `1 ≤ K*K`
        have : (1 : ℤ) * (1 : ℤ) ≤ K * K := by
          exact mul_le_mul hKpos hKpos (by decide : (0 : ℤ) ≤ 1) hKnonneg
        simpa [pow_two] using this
      have h4term : (4 : ℤ) ≤ 4 * (K ^ 2) := by
        have h := mul_le_mul_of_nonneg_left hKsq (by decide : (0 : ℤ) ≤ 4)
        -- `h : 4 * 1 ≤ 4 * (K^2)`
        have h' := h
        rw [mul_one] at h'
        exact h'
      -- add the three component inequalities
      have h12 :
          (b : ℤ) ^ 2 + 2 * (b : ℤ) ≤ (b : ℤ) ^ 2 + 2 * (b : ℤ) * K := by
        -- start from the “wrong order” and commute the `+` once (no `simp` loop)
        have h12' :
            2 * (b : ℤ) + (b : ℤ) ^ 2 ≤ 2 * (b : ℤ) * K + (b : ℤ) ^ 2 := by
          exact add_le_add_left hbterm ((b : ℤ) ^ 2)
        -- commute both sides
        have h12'' := h12'
        -- LHS: `2*b + b^2` → `b^2 + 2*b`
        rw [add_comm (2 * (b : ℤ)) ((b : ℤ) ^ 2)] at h12''
        -- RHS: `2*b*K + b^2` → `b^2 + 2*b*K`
        rw [add_comm (2 * (b : ℤ) * K) ((b : ℤ) ^ 2)] at h12''
        exact h12''
      have h123 :
          (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4 ≤ (b : ℤ) ^ 2 + 2 * (b : ℤ) * K + 4 * (K ^ 2) := by
        simpa [add_assoc] using add_le_add h12 h4term
      exact h123
    -- rewrite the RHS using `hrew` (avoid a `simp` pass over a large expression)
    have hmono' :
        (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4 ≤ 3 * (w ^ 2) + ((b : ℤ) - w) ^ 2 := by
      calc
        (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4
            ≤ (b : ℤ) ^ 2 + 2 * (b : ℤ) * K + 4 * (K ^ 2) := hmono
        _ = 3 * (w ^ 2) + ((b : ℤ) - w) ^ 2 := by
              exact hrew.symm
    exact (ge_iff_le).2 hmono'

  -- Put it together and contradict the hypothesis `h3a_lt`.
  have hsum3' : (x + y + z) ^ 2 = ((b : ℤ) - w) ^ 2 := by
    simp [hsum3]
  have h3a_le : 3 * (w ^ 2) + ((b : ℤ) - w) ^ 2 ≤ 3 * (a : ℤ) := by
    have h' := h3a_ge
    rw [hsum3'] at h'
    exact (ge_iff_le).1 h'
  have hbase_le :
      (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4 ≤ 3 * (w ^ 2) + ((b : ℤ) - w) ^ 2 :=
    (ge_iff_le).1 hbase
  have hcontra : (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4 ≤ 3 * (a : ℤ) :=
    le_trans hbase_le h3a_le
  exact (not_lt_of_ge hcontra) h3a_lt

/-- Final step for `cauchy_lemma`: turn a nonnegative `ℤ` 4-tuple into the requested `ℕ` witnesses,
reusing the already-proved linear and quadratic identities in `ℤ`. -/
lemma cauchy_finalize_nat (a b : ℕ) (sZ tZ uZ vZ : ℤ)
    (hs_nonneg : 0 ≤ sZ) (ht_nonneg : 0 ≤ tZ) (hu_nonneg : 0 ≤ uZ) (hv_nonneg : 0 ≤ vZ)
    (ha_sqZ : (a : ℤ) = sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2)
    (hb_linZ : (b : ℤ) = sZ + tZ + uZ + vZ) :
    ∃ x1 x2 x3 x4 : ℕ,
      a = x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 ∧ b = x1 + x2 + x3 + x4 := by
  -- Convert the ℤ-solution to ℕ (since all components are nonnegative).
  let x1 : ℕ := Int.toNat sZ
  let x2 : ℕ := Int.toNat tZ
  let x3 : ℕ := Int.toNat uZ
  let x4 : ℕ := Int.toNat vZ

  have hx1 : (x1 : ℤ) = sZ := by simpa [x1] using (Int.toNat_of_nonneg hs_nonneg)
  have hx2 : (x2 : ℤ) = tZ := by simpa [x2] using (Int.toNat_of_nonneg ht_nonneg)
  have hx3 : (x3 : ℤ) = uZ := by simpa [x3] using (Int.toNat_of_nonneg hu_nonneg)
  have hx4 : (x4 : ℤ) = vZ := by simpa [x4] using (Int.toNat_of_nonneg hv_nonneg)

  have ha_sq_nat : a = x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 := by
    -- prove in ℤ then cast back
    have : (a : ℤ) = ((x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 : ℕ) : ℤ) := by
      -- rewrite `ha_sqZ` using the `xᵢ` casts
      calc
        (a : ℤ) = sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2 := ha_sqZ
        _ = (x1 : ℤ) ^ 2 + (x2 : ℤ) ^ 2 + (x3 : ℤ) ^ 2 + (x4 : ℤ) ^ 2 := by
              simp [hx1, hx2, hx3, hx4]
        _ = ((x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 : ℕ) : ℤ) := by
              -- normalize `↑(n^2)` vs `(↑n)^2` and the casted sum
              simp [pow_two, Nat.cast_add, Nat.cast_mul, add_assoc]
    exact_mod_cast this

  have hb_lin_nat : b = x1 + x2 + x3 + x4 := by
    have : (b : ℤ) = ((x1 + x2 + x3 + x4 : ℕ) : ℤ) := by
      calc
        (b : ℤ) = sZ + tZ + uZ + vZ := hb_linZ
        _ = (x1 : ℤ) + (x2 : ℤ) + (x3 : ℤ) + (x4 : ℤ) := by
              simp [hx1, hx2, hx3, hx4, add_assoc]
        _ = ((x1 + x2 + x3 + x4 : ℕ) : ℤ) := by
              simp [Nat.cast_add, add_assoc]
    exact_mod_cast this

  refine ⟨x1, x2, x3, x4, ?_, ?_⟩
  · exact ha_sq_nat
  · exact hb_lin_nat

/-- Cauchy’s lemma.

This is the lemma quoted in the standard proof sketch: if `a,b` are odd positive integers in the
interval window
\[
  b^2 < 4a,\qquad 3a < b^2 + 2b + 4,
\]
then there exist nonnegative integers \(x_1,\dots,x_4\) such that
\[
  a = x_1^2+x_2^2+x_3^2+x_4^2,\qquad b = x_1+x_2+x_3+x_4.
\]

We keep it as a single lemma boundary so the rest of `cauchy_decomposition` is *pure algebra*. -/
lemma cauchy_lemma (a b : ℕ) :
    Odd a →
    Odd b →
    ((b : ℤ) ^ 2 < 4 * (a : ℤ)) →
    (3 * (a : ℤ) < (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4) →
    ∃ x1 x2 x3 x4 : ℕ,
      a = x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 ∧ b = x1 + x2 + x3 + x4 := by
  intro ha hb hb2_lt h3a_lt

  -- 1. Construct the deficit N = 4a - b^2.
  have h_bound : (b : ℤ) ^ 2 ≤ 4 * (a : ℤ) := le_of_lt hb2_lt
  -- We need strict inequality for non-zero squares? Not necessarily.
  -- But 4a - b^2 = 3 mod 8 implies it's not 0.

  let N_Z : ℤ := 4 * (a : ℤ) - (b : ℤ) ^ 2
  have hN_nonneg : 0 ≤ N_Z := sub_nonneg.2 h_bound
  lift N_Z to ℕ using hN_nonneg with N hN_def

  -- 2. Check N ≡ 3 (mod 8).
  have hN_mod8 : N % 8 = 3 := by
    -- Do the modular arithmetic in `ZMod 8`, then extract a `Nat` statement via `.val`.
    have h8 : (8 : ZMod 8) = 0 := by decide

    -- First, rewrite the lifted `N` definition in `ZMod 8`.
    have h_mod : (N : ZMod 8) = 4 * (a : ZMod 8) - (b : ZMod 8) ^ 2 := by
      -- `hN_def : (N : ℤ) = 4*a - b^2`. Cast it to `ZMod 8`.
      have hcast : ((N : ℤ) : ZMod 8) = (N_Z : ZMod 8) := by
        simpa using congrArg (fun t : ℤ => (t : ZMod 8)) hN_def
      -- Unfold `N_Z` and normalize casts.
      simpa [N_Z, pow_two] using hcast

    -- For odd `b`, we have `b^2 ≡ 1 (mod 8)`.
    have hb2_1 : (b : ZMod 8) ^ 2 = 1 := by
      rcases hb with ⟨k, rfl⟩
      have hsq :
          ((2 * k + 1 : ℕ) : ZMod 8) ^ 2 =
            (4 : ZMod 8) * ((k * (k + 1) : ℕ) : ZMod 8) + 1 := by
        -- `(2k+1)^2 = 4*k*(k+1) + 1`
        simp [pow_two, mul_add, add_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
        ring_nf
      -- `k*(k+1)` is even.
      have hk_even : Even (k * (k + 1)) := Nat.even_mul_succ_self k
      rcases hk_even with ⟨m, hm⟩
      have hm' : ((k * (k + 1) : ℕ) : ZMod 8) = ((m + m : ℕ) : ZMod 8) := by
        simpa using congrArg (fun t : ℕ => (t : ZMod 8)) hm
      -- Finish.
      calc
        ((2 * k + 1 : ℕ) : ZMod 8) ^ 2
            = (4 : ZMod 8) * ((k * (k + 1) : ℕ) : ZMod 8) + 1 := hsq
        _ = (4 : ZMod 8) * ((m + m : ℕ) : ZMod 8) + 1 := by simp [hm']
        _ = (8 : ZMod 8) * (m : ZMod 8) + 1 := by
              simp [Nat.cast_add]
              ring_nf
        _ = 0 + 1 := by simp [h8]
        _ = 1 := by simp

    -- For odd `a`, we have `4a ≡ 4 (mod 8)`.
    have h4a_4 : 4 * (a : ZMod 8) = 4 := by
      rcases ha with ⟨k, rfl⟩
      calc
        (4 : ZMod 8) * ((2 * k + 1 : ℕ) : ZMod 8)
            = (8 : ZMod 8) * (k : ZMod 8) + 4 := by
              simp [Nat.cast_add, Nat.cast_mul]
              ring_nf
        _ = 0 + 4 := by simp [h8]
        _ = 4 := by simp

    -- Now compute in `ZMod 8`, then take `.val` to get a `Nat` congruence.
    have hz : (N : ZMod 8) = (3 : ZMod 8) := by
      -- `4 - 1 = 3` in `ZMod 8`.
      calc
        (N : ZMod 8) = (4 : ZMod 8) - 1 := by simp [h_mod, hb2_1, h4a_4]
        _ = (3 : ZMod 8) := by decide

    have hzval : (N : ZMod 8).val = (3 : ZMod 8).val := congrArg ZMod.val hz
    -- `val_natCast` connects `.val` to `Nat` mod.
    simpa [ZMod.val_natCast] using hzval

  -- 3. Use Legendre for N.
  -- We need `sum_three_squares_of_three_mod_eight`.
  -- Ensure it's imported (GeometryOfNumbers.Legendre.Main).
  obtain ⟨x, y, z, hxyz⟩ := GeometryOfNumbers.sum_three_squares_of_three_mod_eight N hN_mod8

  -- 4. x, y, z are odd.
  have hodd : Odd x ∧ Odd y ∧ Odd z :=
    odd_of_sum_three_squares_mod8_three x y z N hxyz hN_mod8
  have hx_odd : Odd x := hodd.1
  have hy_odd : Odd y := hodd.2.1
  have hz_odd : Odd z := hodd.2.2

  -- 5. Sign choice for `±z` so that `b + x + y ± z ≡ 0 (mod 4)` (Nathanson 1987).
  have hzpm_dvd4 :
      ∃ zpm : ℤ,
        (zpm = (z : ℤ) ∨ zpm = -(z : ℤ)) ∧
          ((4 : ℤ) ∣ (b : ℤ) + (x : ℤ) + (y : ℤ) + zpm) :=
    exists_sign_zpm_dvd4_of_odds b x y z hb hx_odd hy_odd hz_odd

  -- With that sign choice, define `s,t,u,v` as in Nathanson and prove:
  --   `a = s^2 + t^2 + u^2 + v^2`,  `b = s + t + u + v`,
  -- and then show nonnegativity from `h3a_lt` (so we can convert to ℕ).
  rcases hzpm_dvd4 with ⟨zpm, hzpm, hdiv4⟩

  -- Define the four integers (Nathanson 1987):
  --   s = (b + x + y + zpm)/4,  t = (b + x - y - zpm)/4,
  --   u = (b - x + y - zpm)/4,  v = (b - x - y + zpm)/4.
  --
  -- We keep everything in `ℤ` until we prove nonnegativity.
  let Snum : ℤ := (b : ℤ) + (x : ℤ) + (y : ℤ) + zpm
  have hSnum_dvd : (4 : ℤ) ∣ Snum := by
    -- `hdiv4` is already the divisibility condition.
    simpa [Snum, add_assoc, add_left_comm, add_comm] using hdiv4

  have hx_oddZ : Odd (x : ℤ) := by
    simpa [Int.odd_coe_nat] using hx_odd
  have hy_oddZ : Odd (y : ℤ) := by
    simpa [Int.odd_coe_nat] using hy_odd
  have hz_oddZ : Odd (z : ℤ) := by
    simpa [Int.odd_coe_nat] using hz_odd

  have hzpm_oddZ : Odd zpm := by
    rcases hzpm with rfl | rfl
    · exact hz_oddZ
    · simpa using hz_oddZ.neg

  have hyzpm_even : Even ((y : ℤ) + zpm) :=
    hy_oddZ.add_odd hzpm_oddZ

  have hxzpm_even : Even ((x : ℤ) + zpm) := by
    -- odd + odd = even
    simpa using (hx_oddZ.add_odd hzpm_oddZ)

  have hxy_even : Even ((x : ℤ) + (y : ℤ)) := by
    -- odd + odd = even
    simpa using (hx_oddZ.add_odd hy_oddZ)

  -- Divisibility for the other three numerators follows from `Snum` by subtracting a multiple of `4`.
  let Tnum : ℤ := (b : ℤ) + (x : ℤ) - (y : ℤ) - zpm
  let Unum : ℤ := (b : ℤ) - (x : ℤ) + (y : ℤ) - zpm
  let Vnum : ℤ := (b : ℤ) - (x : ℤ) - (y : ℤ) + zpm

  have hTnum_dvd : (4 : ℤ) ∣ Tnum := by
    -- Tnum = Snum - 2*(y+zpm)
    have : Tnum = Snum - 2 * ((y : ℤ) + zpm) := by
      simp [Tnum, Snum]
      ring
    have hsub : (4 : ℤ) ∣ Snum - 2 * ((y : ℤ) + zpm) := by
      refine dvd_four_sub_of_dvd_four hSnum_dvd ?_
      exact dvd_four_two_mul_of_even ((y : ℤ) + zpm) hyzpm_even
    simpa [this] using hsub

  have hUnum_dvd : (4 : ℤ) ∣ Unum := by
    -- Unum = Snum - 2*(x+zpm)
    have : Unum = Snum - 2 * ((x : ℤ) + zpm) := by
      simp [Unum, Snum]
      ring
    have hsub : (4 : ℤ) ∣ Snum - 2 * ((x : ℤ) + zpm) := by
      refine dvd_four_sub_of_dvd_four hSnum_dvd ?_
      exact dvd_four_two_mul_of_even ((x : ℤ) + zpm) hxzpm_even
    simpa [this] using hsub

  have hVnum_dvd : (4 : ℤ) ∣ Vnum := by
    -- Vnum = Snum - 2*(x+y)
    have : Vnum = Snum - 2 * ((x : ℤ) + (y : ℤ)) := by
      simp [Vnum, Snum]
      ring
    have hsub : (4 : ℤ) ∣ Snum - 2 * ((x : ℤ) + (y : ℤ)) := by
      refine dvd_four_sub_of_dvd_four hSnum_dvd ?_
      exact dvd_four_two_mul_of_even ((x : ℤ) + (y : ℤ)) hxy_even
    simpa [this] using hsub

  let sZ : ℤ := Snum / 4
  let tZ : ℤ := Tnum / 4
  let uZ : ℤ := Unum / 4
  let vZ : ℤ := Vnum / 4

  -- For divisible numerators, we can recover `Snum = 4*(Snum/4)` etc.
  have h4ne : (4 : ℤ) ≠ 0 := by decide
  have hs : Snum = 4 * sZ := by
    rcases hSnum_dvd with ⟨k, hk⟩
    simp [sZ, hk, h4ne]
  have ht : Tnum = 4 * tZ := by
    rcases hTnum_dvd with ⟨k, hk⟩
    simp [tZ, hk, h4ne]
  have hu : Unum = 4 * uZ := by
    rcases hUnum_dvd with ⟨k, hk⟩
    simp [uZ, hk, h4ne]
  have hv : Vnum = 4 * vZ := by
    rcases hVnum_dvd with ⟨k, hk⟩
    simp [vZ, hk, h4ne]

  -- Linear identity: `b = s+t+u+v`.
  have hb_linZ : (b : ℤ) = sZ + tZ + uZ + vZ := by
    have hsum : Snum + Tnum + Unum + Vnum = 4 * (b : ℤ) := by
      simp [Snum, Tnum, Unum, Vnum]
      ring
    simpa using
      (hadamard_linear_identity (b := (b : ℤ))
        (Snum := Snum) (Tnum := Tnum) (Unum := Unum) (Vnum := Vnum)
        (sZ := sZ) (tZ := tZ) (uZ := uZ) (vZ := vZ)
        h4ne hs ht hu hv hsum)

  -- Square identity: `a = s^2 + t^2 + u^2 + v^2`.
  have hzpm_sq : zpm ^ 2 = (z : ℤ) ^ 2 := by
    rcases hzpm with rfl | rfl
    · rfl
    · simp [pow_two]

  have hxyzZ : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = 4 * (a : ℤ) - (b : ℤ) ^ 2 := by
    have hcast : ((x ^ 2 + y ^ 2 + z ^ 2 : ℕ) : ℤ) = (N : ℤ) := by
      exact_mod_cast hxyz
    have hxys : (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = (N : ℤ) := by
      simpa [pow_two, Nat.cast_add, Nat.cast_mul, add_assoc, add_left_comm, add_comm] using hcast
    calc
      (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = (N : ℤ) := hxys
      _ = N_Z := by simpa using hN_def
      _ = 4 * (a : ℤ) - (b : ℤ) ^ 2 := by rfl

  have hhadamard :
      Snum ^ 2 + Tnum ^ 2 + Unum ^ 2 + Vnum ^ 2 =
        4 * ((b : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2) := by
    have hbase :
        Snum ^ 2 + Tnum ^ 2 + Unum ^ 2 + Vnum ^ 2 =
          4 * ((b : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + zpm ^ 2) := by
      simpa [Snum, Tnum, Unum, Vnum] using
        (hadamard_square_identity (b := (b : ℤ)) (x := (x : ℤ)) (y := (y : ℤ)) (z := zpm))
    -- Squares kill the sign: rewrite `zpm^2` as `z^2`.
    have hzpm_sq' :
        (b : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + zpm ^ 2 =
          (b : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 := by
      simp [hzpm_sq]
    calc
      Snum ^ 2 + Tnum ^ 2 + Unum ^ 2 + Vnum ^ 2
          = 4 * ((b : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + zpm ^ 2) := hbase
      _ = 4 * ((b : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2) := by
            simp [hzpm_sq']

  have hsum_sq :
      4 * (sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2)
        = (b : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 := by
    simpa using
      (hadamard_sum_sq_cancel (Snum := Snum) (Tnum := Tnum) (Unum := Unum) (Vnum := Vnum)
        (sZ := sZ) (tZ := tZ) (uZ := uZ) (vZ := vZ)
        (rhs := (b : ℤ) ^ 2 + (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2)
        h4ne hs ht hu hv hhadamard)

  have ha_sqZ : (a : ℤ) = sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2 := by
    -- Use the extracted “cancel factor 4” spine.
    simpa using
      (hadamard_derive_a_eq_sum_sq (a := a) (b := b)
        (x := (x : ℤ)) (y := (y : ℤ)) (z := (z : ℤ))
        (sZ := sZ) (tZ := tZ) (uZ := uZ) (vZ := vZ)
        h4ne hxyzZ hsum_sq)

  -- Prove nonnegativity of `sZ,tZ,uZ,vZ` from `h3a_lt`, then convert to ℕ and finish using
  -- `ha_sqZ` + `hb_linZ`. A key inequality we use is:
  -- \[
  --   (x+y+z)^2 \le 3(x^2+y^2+z^2).
  -- \]
  have hs_nonneg : 0 ≤ sZ :=
    cauchy_component_nonneg (a := a) (b := b) h3a_lt sZ tZ uZ vZ hb_linZ ha_sqZ
  have ht_nonneg : 0 ≤ tZ :=
    cauchy_component_nonneg (a := a) (b := b) h3a_lt tZ sZ uZ vZ
      (by
        have hswap : sZ + tZ + uZ + vZ = tZ + sZ + uZ + vZ := by ring
        exact hb_linZ.trans hswap)
      (by
        have hswap : sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2 = tZ ^ 2 + sZ ^ 2 + uZ ^ 2 + vZ ^ 2 := by
          ring
        exact ha_sqZ.trans hswap)
  have hu_nonneg : 0 ≤ uZ :=
    cauchy_component_nonneg (a := a) (b := b) h3a_lt uZ sZ tZ vZ
      (by
        have hperm : sZ + tZ + uZ + vZ = uZ + sZ + tZ + vZ := by ring
        exact hb_linZ.trans hperm)
      (by
        have hperm :
            sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2 = uZ ^ 2 + sZ ^ 2 + tZ ^ 2 + vZ ^ 2 := by
          ring
        exact ha_sqZ.trans hperm)
  have hv_nonneg : 0 ≤ vZ :=
    cauchy_component_nonneg (a := a) (b := b) h3a_lt vZ sZ tZ uZ
      (by
        have hperm : sZ + tZ + uZ + vZ = vZ + sZ + tZ + uZ := by ring
        exact hb_linZ.trans hperm)
      (by
        have hperm :
            sZ ^ 2 + tZ ^ 2 + uZ ^ 2 + vZ ^ 2 = vZ ^ 2 + sZ ^ 2 + tZ ^ 2 + uZ ^ 2 := by
          ring
        exact ha_sqZ.trans hperm)

  exact cauchy_finalize_nat (a := a) (b := b) (sZ := sZ) (tZ := tZ) (uZ := uZ) (vZ := vZ)
    hs_nonneg ht_nonneg hu_nonneg hv_nonneg ha_sqZ hb_linZ

set_option maxHeartbeats 200000

/-!
### Medium-case lookup tables for `cauchy_decomposition`

The Cauchy/Nathanson “window inequalities” (the route through `cauchy_lemma`) are **not** uniform in
the bounded regime \(n \le 108\,(s-2)\): there are concrete counterexamples (e.g. `s=5, n=5`).

However, `cauchy_decomposition` itself is still true there.  For now, we bridge this bounded regime
with a small, explicitly precomputed lookup table:

- write \(m := s-2\), \(n = m q + \mathrm{rem}\) with `q = n / m` and `rem = n % m` (so `q ≤ 108`);
- choose indices \(t,u,v,w\) so that

\[
\sum_{x \in \{t,u,v,w\}} P(s,x) = mQ + B
\]

with \(Q \in \{q, q-1\}\) and \(B\) small, and then take \(r := n - (mQ + B)\).

The tables below were generated by a brute search over small indices (bounded by 20), ensuring the
simple remainder bounds needed to keep \(r \le s-4 = m-2\).

This is intentionally “table-driven” and local: it does not reintroduce a false statement like the
old `nathanson_parameters_medium`.
-/

/-  (disabled)

This block was an attempted table-driven medium-case bridge for `cauchy_decomposition`.
It is currently incomplete (and was causing typechecking failures), so it is disabled
until we can land the full table + proof in a single coherent change.

It has since been superseded by the generated modules:
- `GeometryOfNumbers.Cauchy.MediumTablesSmall` (direct polygonal decompositions for `5 ≤ s ≤ 23`), and
- `GeometryOfNumbers.Cauchy.MediumTablesMge22` (triangular tables + algebra for `s-2 ≥ 22`).


private def cauchyTriPred (t : ℕ) : ℕ :=
  t * (t - 1) / 2

private def cauchyTriPredSum4 (t u v w : ℕ) : ℕ :=
  cauchyTriPred t + cauchyTriPred u + cauchyTriPred v + cauchyTriPred w

private def cauchyBSum4 (t u v w : ℕ) : ℕ :=
  t + u + v + w

private lemma polygonal_eq_linear (s : ℕ) (t : ℕ) :
    polygonal s t = t + (s - 2) * cauchyTriPred t := by
  -- Push the `/2` past the outer factor `s-2` using that `t*(t-1)` is even.
  have ht : 2 ∣ t * (t - 1) := (Nat.even_mul_pred_self t).two_dvd
  dsimp [GeometryOfNumbers.polygonal, cauchyTriPred]
  -- rewrite `((s-2)*t*(t-1))/2` as `(s-2)*((t*(t-1))/2)`
  have hdiv :
      (s - 2) * t * (t - 1) / 2 = (s - 2) * (t * (t - 1) / 2) := by
    -- `Nat.mul_div_assoc` expects the divisor to divide the right factor.
    -- First normalize the LHS into `((s-2) * (t*(t-1))) / 2`.
    calc
      (s - 2) * t * (t - 1) / 2
          = (s - 2) * (t * (t - 1)) / 2 := by
              simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = (s - 2) * (t * (t - 1) / 2) := by
              simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
                (Nat.mul_div_assoc (s - 2) (t * (t - 1)) ht)
  simp [hdiv, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

-- Generated lookup tables (q in 1..108, small remainder in 0..21).
-- (Generated by a bounded brute-force search over indices 0..20.)
private def cauchyMediumDefault (q : Fin 109) : Nat × Nat × Nat × Nat × Nat :=
  match q.1 with
  | 1 => (2, 0, 0, 0, 2)
  | 2 => (4, 0, 0, 2, 2)
  | 3 => (3, 0, 0, 0, 3)
  | 4 => (5, 0, 0, 2, 3)
  | 5 => (7, 0, 2, 2, 3)
  | 6 => (4, 0, 0, 0, 4)
  | 7 => (6, 0, 0, 2, 4)
  | 8 => (8, 0, 2, 2, 4)
  | 9 => (7, 0, 0, 3, 4)
  | 10 => (5, 0, 0, 0, 5)
  | 11 => (7, 0, 0, 2, 5)
  | 12 => (8, 0, 0, 4, 4)
  | 13 => (8, 0, 0, 3, 5)
  | 14 => (10, 0, 2, 3, 5)
  | 15 => (6, 0, 0, 0, 6)
  | 16 => (8, 0, 0, 2, 6)
  | 17 => (10, 0, 2, 2, 6)
  | 18 => (9, 0, 0, 3, 6)
  | 19 => (11, 0, 2, 3, 6)
  | 20 => (10, 0, 0, 5, 5)
  | 21 => (7, 0, 0, 0, 7)
  | 22 => (9, 0, 0, 2, 7)
  | 23 => (11, 0, 2, 2, 7)
  | 24 => (10, 0, 0, 3, 7)
  | 25 => (11, 0, 0, 5, 6)
  | 26 => (13, 0, 2, 5, 6)
  | 27 => (11, 0, 0, 4, 7)
  | 28 => (8, 0, 0, 0, 8)
  | 29 => (10, 0, 0, 2, 8)
  | 30 => (12, 0, 0, 6, 6)
  | 31 => (11, 0, 0, 3, 8)
  | 32 => (13, 0, 2, 3, 8)
  | 33 => (15, 0, 3, 6, 6)
  | 34 => (12, 0, 0, 4, 8)
  | 35 => (14, 0, 2, 4, 8)
  | 36 => (9, 0, 0, 0, 9)
  | 37 => (11, 0, 0, 2, 9)
  | 38 => (13, 0, 0, 5, 8)
  | 39 => (12, 0, 0, 3, 9)
  | 40 => (14, 0, 2, 3, 9)
  | 41 => (16, 0, 3, 5, 8)
  | 42 => (13, 0, 0, 4, 9)
  | 43 => (14, 0, 0, 6, 8)
  | 44 => (16, 0, 2, 6, 8)
  | 45 => (10, 0, 0, 0, 10)
  | 46 => (12, 0, 0, 2, 10)
  | 47 => (14, 0, 2, 2, 10)
  | 48 => (13, 0, 0, 3, 10)
  | 49 => (15, 0, 0, 7, 8)
  | 50 => (17, 0, 2, 7, 8)
  | 51 => (14, 0, 0, 4, 10)
  | 52 => (16, 0, 2, 4, 10)
  | 53 => (18, 2, 2, 4, 10)
  | 54 => (17, 0, 3, 4, 10)
  | 55 => (11, 0, 0, 0, 11)
  | 56 => (13, 0, 0, 2, 11)
  | 57 => (15, 0, 2, 2, 11)
  | 58 => (14, 0, 0, 3, 11)
  | 59 => (16, 0, 2, 3, 11)
  | 60 => (16, 0, 0, 6, 10)
  | 61 => (15, 0, 0, 4, 11)
  | 62 => (17, 0, 2, 4, 11)
  | 63 => (19, 0, 3, 6, 10)
  | 64 => (17, 0, 0, 8, 9)
  | 65 => (16, 0, 0, 5, 11)
  | 66 => (12, 0, 0, 0, 12)
  | 67 => (14, 0, 0, 2, 12)
  | 68 => (16, 0, 2, 2, 12)
  | 69 => (15, 0, 0, 3, 12)
  | 70 => (17, 0, 0, 6, 11)
  | 71 => (19, 0, 2, 6, 11)
  | 72 => (16, 0, 0, 4, 12)
  | 73 => (18, 0, 0, 8, 10)
  | 74 => (20, 0, 2, 8, 10)
  | 75 => (19, 0, 3, 4, 12)
  | 76 => (17, 0, 0, 5, 12)
  | 77 => (19, 0, 2, 5, 12)
  | 78 => (13, 0, 0, 0, 13)
  | 79 => (15, 0, 0, 2, 13)
  | 80 => (17, 0, 2, 2, 13)
  | 81 => (16, 0, 0, 3, 13)
  | 82 => (18, 0, 2, 3, 13)
  | 83 => (19, 0, 0, 8, 11)
  | 84 => (17, 0, 0, 4, 13)
  | 85 => (19, 0, 2, 4, 13)
  | 86 => (21, 2, 2, 4, 13)
  | 87 => (19, 0, 0, 7, 12)
  | 88 => (18, 0, 0, 5, 13)
  | 89 => (20, 0, 2, 5, 13)
  | 90 => (20, 0, 0, 10, 10)
  | 91 => (14, 0, 0, 0, 14)
  | 92 => (16, 0, 0, 2, 14)
  | 93 => (18, 0, 2, 2, 14)
  | 94 => (17, 0, 0, 3, 14)
  | 95 => (19, 0, 2, 3, 14)
  | 96 => (21, 2, 2, 3, 14)
  | 97 => (18, 0, 0, 4, 14)
  | 98 => (20, 0, 2, 4, 14)
  | 99 => (20, 0, 0, 7, 13)
  | 100 => (21, 0, 0, 10, 11)
  | 101 => (19, 0, 0, 5, 14)
  | 102 => (21, 0, 0, 9, 12)
  | 103 => (22, 0, 4, 4, 14)
  | 104 => (22, 0, 3, 5, 14)
  | 105 => (15, 0, 0, 0, 15)
  | 106 => (17, 0, 0, 2, 15)
  | 107 => (19, 0, 2, 2, 15)
  | 108 => (18, 0, 0, 3, 15)
  | _ => (0,0,0,0,0)

private def cauchyMediumSpecial (q : Fin 109) (rem : Fin 22) : Bool × Nat × Nat × Nat × Nat × Nat :=
  match q.1, rem.1 with
  | 1, 0 => (true, 2, 0, 0, 1, 1)
  | 1, 1 => (true, 3, 0, 1, 1, 1)
  | 1, 2 => (false, 2, 0, 0, 0, 2)
  | 1, 3 => (false, 2, 0, 0, 0, 2)
  | 1, 4 => (false, 2, 0, 0, 0, 2)
  | 1, 5 => (false, 2, 0, 0, 0, 2)
  | 1, 6 => (false, 2, 0, 0, 0, 2)
  | 1, 7 => (false, 2, 0, 0, 0, 2)
  | 1, 8 => (false, 2, 0, 0, 0, 2)
  | 1, 9 => (false, 2, 0, 0, 0, 2)
  | 1, 10 => (false, 2, 0, 0, 0, 2)
  | 1, 11 => (false, 2, 0, 0, 0, 2)
  | 1, 12 => (false, 2, 0, 0, 0, 2)
  | 1, 13 => (false, 2, 0, 0, 0, 2)
  | 1, 14 => (false, 2, 0, 0, 0, 2)
  | 1, 15 => (false, 2, 0, 0, 0, 2)
  | 1, 16 => (false, 2, 0, 0, 0, 2)
  | 1, 17 => (false, 2, 0, 0, 0, 2)
  | 1, 18 => (false, 2, 0, 0, 0, 2)
  | 1, 19 => (false, 2, 0, 0, 0, 2)
  | 1, 20 => (false, 2, 0, 0, 0, 2)
  | 1, 21 => (false, 2, 0, 0, 0, 2)
  | _, _ => (false, 0,0,0,0,0)

private lemma cauchyMediumDefault_spec :
    ∀ q : Fin 109,
      q.1 ≠ 0 →
        let (b, t, u, v, w) := cauchyMediumDefault q
        cauchyTriPredSum4 t u v w = q.1 ∧
        cauchyBSum4 t u v w = b ∧
        1 ≤ b ∧ b ≤ 22 := by
  native_decide

private lemma cauchyMediumSpecial_spec :
    ∀ q : Fin 109,
      q.1 ≠ 0 →
        ∀ rem : Fin 22,
          let (mode, b, t, u, v, w) := cauchyMediumSpecial q rem
          let (b0, t0, u0, v0, w0) := cauchyMediumDefault q
          rem.1 < b0 →
            ((mode = false ∧
                cauchyTriPredSum4 t u v w = q.1 ∧
                cauchyBSum4 t u v w = b ∧
                1 ≤ b ∧ b ≤ rem.1)
              ∨
              (mode = true ∧
                cauchyTriPredSum4 t u v w = q.1 - 1 ∧
                cauchyBSum4 t u v w = b ∧
                b ≥ rem.1 + 2)) := by
  native_decide

-/

/-!
### Bounded-medium bridge (computational, but finite)

To avoid a giant hand-written table, we prove the required bounded-medium existence by a *finite*
`native_decide` search over small indices.

Key point: in the medium branch we only need `q = n/(s-2) ≤ 108`, and we can restrict candidate
indices `t,u,v,w` to a small fixed bound (here `≤ 20`) because `t*(t-1)/2` grows quadratically.
-/

/- (disabled; proof attempt in progress)

private def cauchyTriPred (t : ℕ) : ℕ :=
  t * (t - 1) / 2

private def cauchyTriPredSum4 (t u v w : ℕ) : ℕ :=
  cauchyTriPred t + cauchyTriPred u + cauchyTriPred v + cauchyTriPred w

private def cauchyBSum4 (t u v w : ℕ) : ℕ :=
  t + u + v + w

private lemma polygonal_eq_linear (s : ℕ) (t : ℕ) :
    polygonal s t = t + (s - 2) * cauchyTriPred t := by
  have ht : 2 ∣ t * (t - 1) := (Nat.even_mul_pred_self t).two_dvd
  -- Push the `/2` past the outer factor `s-2` using divisibility.
  have hdiv : (s - 2) * (t * (t - 1)) / 2 = (s - 2) * ((t * (t - 1)) / 2) :=
    Nat.mul_div_assoc (s - 2) ht
  -- Now rewrite the polygonal definition and normalize products.
  dsimp [GeometryOfNumbers.polygonal, cauchyTriPred]
  -- `simp` knows how to reassociate the products; we guide it with `hdiv`.
  -- The only nontrivial step is the `mul_div_assoc` rewrite above.
  calc
    t + (s - 2) * t * (t - 1) / 2
        = t + ((s - 2) * (t * (t - 1)) / 2) := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = t + (s - 2) * ((t * (t - 1)) / 2) := by
            simp [hdiv]
    _ = t + (s - 2) * (t * (t - 1) / 2) := by rfl

private lemma cauchyMediumDefault_exists :
    ∀ q : Fin 109,
      q.1 ≠ 0 →
        ∃ t u v w : Fin 21,
          cauchyTriPredSum4 t.1 u.1 v.1 w.1 = q.1 ∧
          1 ≤ cauchyBSum4 t.1 u.1 v.1 w.1 ∧
          cauchyBSum4 t.1 u.1 v.1 w.1 ≤ 22 := by
  native_decide

private lemma cauchyMediumSpecial_exists :
    ∀ q : Fin 109,
      q.1 ≠ 0 →
        ∀ rem : Fin 22,
          ∃ mode : Bool,
            ∃ t u v w : Fin 21,
              (mode = false ∧
                  cauchyTriPredSum4 t.1 u.1 v.1 w.1 = q.1 ∧
                  1 ≤ cauchyBSum4 t.1 u.1 v.1 w.1 ∧
                  cauchyBSum4 t.1 u.1 v.1 w.1 ≤ rem.1)
                ∨
                (mode = true ∧
                  cauchyTriPredSum4 t.1 u.1 v.1 w.1 = q.1 - 1 ∧
                  cauchyBSum4 t.1 u.1 v.1 w.1 ≥ rem.1 + 2 ∧
                  cauchyBSum4 t.1 u.1 v.1 w.1 ≤ rem.1 + 3) := by
  native_decide

-/

theorem cauchy_decomposition (s : ℕ) (hs : 5 ≤ s) (n : ℕ) :
    ∃ t u v w r : ℕ,
      r ≤ s - 4 ∧ polygonal s t + polygonal s u + polygonal s v + polygonal s w + r = n := by
  classical
  have hs3 : 3 ≤ s := le_trans (by decide : (3 : ℕ) ≤ 5) hs
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨0, 0, 0, 0, 0, ?_, ?_⟩
    · exact Nat.zero_le (s - 4)
    · simp

  /-
  ### Cauchy/Nathanson proof skeleton (what is done vs missing)

  The “Cauchy route” reduces the polygonal decomposition to finding parameters `b q r` such that

  \[
    n = (s-2)q + b + r,\quad r \le s-4,\quad b\ \text{odd},
  \]

  plus two window inequalities (involving \(a = 2q+b\)) that allow `cauchy_lemma` to produce a
  4-square representation \(a = \sum x_i^2\) with \(b = \sum x_i\).

  What we currently have:
  - **Small** regime `n ≤ s-3`: handled by `nathanson_parameters_small`.
  - **Large** regime `n > 108*(s-2)`: handled analytically by `nathanson_parameters_large`.

  What is still missing:
  - The bounded **medium** regime `n ≤ 108*(s-2)` (with `¬ n ≤ s-3`). The Nathanson window
    inequalities do **not** hold uniformly here (e.g. `s=5,n=5`), so this branch needs a different
    argument than `cauchy_lemma`.
  -/

  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  -- IMPORTANT: do **not** call `nathanson_parameters` here.
  --
  -- That lemma currently depends on `nathanson_parameters_medium`, which is known to be false
  -- as stated (see `Experiments/NathansonWindowSearch.lean`; e.g. `s=5, n=5` has no such
  -- `(b,q,r)` satisfying the Cauchy window inequalities).
  --
  -- Instead, we:
  -- - handle the genuinely small regime via `nathanson_parameters_small`, and
  -- - force the analytic proof onto the large branch via `nathanson_parameters_large`.
  -- The bounded “medium” band remains an explicit gap to be closed by a different argument.
  by_cases hsmall : n ≤ s - 3
  ·
    rcases nathanson_parameters_small s hs n hn_pos hsmall with
      ⟨b, q, r, hr, hb_odd, hb2_lt, h3a_lt, hn⟩
    -- continue with the common postprocessing
    -- (the rest of the proof is shared verbatim)
    -- NOTE: we keep this as a local `have` to reuse the block below.
    have hparams :
        ∃ b q r : ℕ,
          r ≤ s - 4 ∧ Odd b ∧
            ((b : ℤ) ^ 2 < 4 * ((2 * q + b : ℕ) : ℤ)) ∧
            (3 * ((2 * q + b : ℕ) : ℤ) < (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4) ∧
            n = (s - 2) * q + b + r :=
      ⟨b, q, r, hr, hb_odd, hb2_lt, h3a_lt, hn⟩
    rcases hparams with ⟨b, q, r, hr, hb_odd, hb2_lt, h3a_lt, hn⟩
    -- fall through to shared tail
    -- (duplicated once; acceptable until we refactor the shared tail into a lemma)
    let a : ℕ := 2 * q + b
    have ha_odd : Odd a := by
      have heven : Even (2 * q) := ⟨q, by simp [two_mul]⟩
      simpa [a, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hb_odd.add_even heven
    rcases cauchy_lemma a b ha_odd hb_odd (by simpa [a] using hb2_lt) (by simpa [a] using h3a_lt) with
      ⟨x1, x2, x3, x4, ha_sq, hb_lin⟩
    have hpoly :
        polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4
          = (s - 2) * q + b := by
      have hId := GeometryOfNumbers.cauchy_polygonal_identity (s := s) hs3 x1 x2 x3 x4
      have ha_sq' :
          ((x1 : ℤ) ^ 2 + (x2 : ℤ) ^ 2 + (x3 : ℤ) ^ 2 + (x4 : ℤ) ^ 2) = (a : ℤ) := by
        have h : (a : ℤ) = ((x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 : ℕ) : ℤ) := by
          exact_mod_cast ha_sq
        simpa [pow_two, add_assoc, add_left_comm, add_comm] using h.symm
      have hb_lin' : ((x1 : ℤ) + (x2 : ℤ) + (x3 : ℤ) + (x4 : ℤ)) = (b : ℤ) := by
        have h : (b : ℤ) = ((x1 + x2 + x3 + x4 : ℕ) : ℤ) := by
          exact_mod_cast hb_lin
        simpa [add_assoc, add_left_comm, add_comm] using h.symm
      have haZ : (a : ℤ) = (2 * q + b : ℕ) := by rfl
      have h2 :
          (2 * (polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4) : ℤ)
            = (2 * ((s - 2) * q + b) : ℤ) := by
        dsimp at hId
        have : (2 * (polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4) : ℤ)
            =
          (((s : ℤ) - 2) * (a : ℤ) + ((2 : ℤ) - ((s : ℤ) - 2)) * (b : ℤ)) := by
          simpa [ha_sq', hb_lin'] using hId
        calc
          (2 * (polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4) : ℤ)
              = ((s : ℤ) - 2) * (a : ℤ) + ((2 : ℤ) - ((s : ℤ) - 2)) * (b : ℤ) := this
          _ = ((s : ℤ) - 2) * ((2 * q + b : ℕ) : ℤ) + ((4 : ℤ) - s) * (b : ℤ) := by
                simp [haZ, sub_eq_add_neg, add_left_comm, add_comm]
          _ = (2 * ((s - 2) * q + b) : ℤ) := by
                simp [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
                  sub_eq_add_neg, add_comm, mul_comm]
                ring_nf
      have hs2 : 2 ≤ s := le_trans (by decide : (2 : ℕ) ≤ 3) hs3
      let P : ℕ := polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4
      let Q : ℕ := (s - 2) * q + b
      have h2' : ((2 * P : ℕ) : ℤ) = ((2 * Q : ℕ) : ℤ) := by
        have hs_sub : ((s - 2 : ℕ) : ℤ) = (s : ℤ) - 2 := Int.ofNat_sub hs2
        have hQZ : ((Q : ℕ) : ℤ) = ((s : ℤ) - 2) * (q : ℤ) + (b : ℤ) := by
          simp [Q, Nat.cast_add, Nat.cast_mul, hs_sub, sub_eq_add_neg, add_comm, mul_comm]
        have hPZ : ((P : ℕ) : ℤ) =
            (polygonal s x1 : ℤ) + (polygonal s x2 : ℤ) + (polygonal s x3 : ℤ) + (polygonal s x4 : ℤ) := by
          simp [P, Nat.cast_add, add_assoc, add_left_comm, add_comm]
        calc
          ((2 * P : ℕ) : ℤ) = 2 * ((P : ℕ) : ℤ) := by simp [Nat.cast_mul]
          _ = 2 * ((polygonal s x1 : ℤ) + (polygonal s x2 : ℤ) + (polygonal s x3 : ℤ) + (polygonal s x4 : ℤ)) := by
                simp [hPZ, add_assoc]
          _ = 2 * (((s : ℤ) - 2) * (q : ℤ) + (b : ℤ)) := by
                simpa [P, Q, Nat.cast_add, Nat.cast_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
                  mul_assoc, mul_left_comm, mul_comm] using h2
          _ = 2 * ((Q : ℕ) : ℤ) := by simp [hQZ, add_comm]
          _ = ((2 * Q : ℕ) : ℤ) := by simp [Nat.cast_mul]
      have h2nat : 2 * P = 2 * Q := Int.ofNat.inj h2'
      have hpoly' : P = Q := by
        simpa [P, Q] using (Nat.mul_left_cancel (by decide : 0 < 2) h2nat)
      simpa [P, Q] using hpoly'
    refine ⟨x1, x2, x3, x4, r, hr, ?_⟩
    have : polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4 + r
        = (s - 2) * q + b + r := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg (fun t => t + r) hpoly
    simpa [hn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

  -- From here on, we are in the `¬n ≤ s-3` regime.
  have hn_pos' : 0 < n := hn_pos
  by_cases hmed : n ≤ 108 * (s - 2)
  ·
    -- Medium (bounded) regime: do **not** use the Cauchy/Nathanson window inequalities.
    --
    -- Instead, discharge this band by finite search tables:
    -- - for `5 ≤ s ≤ 23`, we have a direct table of polygonal decompositions;
    -- - for `s ≥ 24` (i.e. `m := s-2 ≥ 22`), we use a smaller triangular-sum table combined with
    --   the identity `polygonal s t = t + (s-2) * (t*(t-1)/2)`.
    have hn_ne0 : n ≠ 0 := by exact hn0
    by_cases hs23 : s ≤ 23
    ·
      exact cauchy_decomposition_medium_small_le23 s hs hs23 n hn_ne0 (by simpa using hsmall) hmed
    ·
      have hs24 : 24 ≤ s := Nat.succ_le_of_lt (Nat.lt_of_not_ge hs23)
      have hm22 : 22 ≤ s - 2 := by
        -- `24 ≤ s` ⇒ `22 ≤ s-2`.
        simpa using Nat.sub_le_sub_right hs24 2
      exact
        cauchy_decomposition_medium_mge22 s hs n hn_pos' (by simpa using hsmall) hmed hm22
    /-  (disabled attempt; medium-branch bridge work-in-progress)
    -- We handle this bounded regime by a finite `native_decide` search over small indices.
    let m : ℕ := s - 2
    have hm_pos : 0 < m := by
      have : (3 : ℕ) ≤ m := by
        -- `5 ≤ s` ⇒ `3 ≤ s-2`.
        simpa [m] using Nat.sub_le_sub_right hs 2
      omega
    let qNat : ℕ := n / m
    let remNat : ℕ := n % m
    have hn_decomp : m * qNat + remNat = n := by
      simpa [qNat, remNat] using (Nat.div_add_mod n m)
    have hm_le_n : m ≤ n := by
      -- `¬ n ≤ s-3` ⇒ `s-2 ≤ n`
      have : s - 2 ≤ n := by omega
      simpa [m] using this
    have hq_pos : qNat ≠ 0 := by
      have : 0 < qNat := Nat.div_pos hm_le_n hm_pos
      exact Nat.ne_of_gt this
    have hq_le : qNat ≤ 108 := by
      -- `(n/m)*m ≤ n ≤ 108*m` ⇒ `n/m ≤ 108`
      have hmul1 : qNat * m ≤ n := by
        simpa [qNat, Nat.mul_comm] using (Nat.mul_div_le n m)
      have hmul2 : qNat * m ≤ 108 * m := le_trans hmul1 (by simpa [m] using hmed)
      exact Nat.le_of_mul_le_mul_right hmul2 hm_pos
    let qFin : Fin 109 := ⟨qNat, Nat.lt_succ_of_le hq_le⟩

    by_cases hrem_small : remNat < 22
    ·
      -- Small remainder: solve by the finite special search (either `Q=q` or `Q=q-1`).
      let remFin : Fin 22 := ⟨remNat, hrem_small⟩
      rcases cauchyMediumSpecial_exists qFin (by simpa [qFin, qNat] using hq_pos) remFin with
        ⟨mode, t, u, v, w, hcases⟩
      have ht : ℕ := t.1
      have hu : ℕ := u.1
      have hv : ℕ := v.1
      have hw : ℕ := w.1
      let bNat : ℕ := cauchyBSum4 ht hu hv hw
      have hpoly_sum :
          polygonal s ht + polygonal s hu + polygonal s hv + polygonal s hw
            = (s - 2) * (cauchyTriPredSum4 ht hu hv hw) + bNat := by
        -- Expand each polygonal as a linear function of `s-2`.
        simp [bNat, cauchyBSum4, cauchyTriPredSum4, polygonal_eq_linear,
          Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_assoc, Nat.mul_left_comm,
          Nat.mul_comm]

      cases hcases with
      | inl hqcase =>
          -- mode = false: `Q=qNat`, and `bNat ≤ remNat`.
          rcases hqcase with ⟨hmode, hQ, hb1, hb_le⟩
          have hb_le_rem : bNat ≤ remNat := by
            simpa [bNat, ht, hu, hv, hw, remFin] using hb_le
          let r : ℕ := remNat - bNat
          have hr : r ≤ s - 4 := by
            -- `r = rem-b` with `rem < m` and `b ≥ 1` ⇒ `r ≤ m-2 = s-4`.
            have hrem_lt_m : remNat < m := Nat.mod_lt n hm_pos
            have hb_pos : 1 ≤ bNat := by
              simpa [bNat, ht, hu, hv, hw] using hb1
            have : remNat - bNat ≤ m - 2 := by omega
            simpa [m, r] using this
          refine ⟨ht, hu, hv, hw, r, hr, ?_⟩
          -- Finish by rewriting in the `q*m + rem` normal form.
          have hQ' : cauchyTriPredSum4 ht hu hv hw = qNat := by
            simpa [qFin, qNat] using hQ
          have hpoly_sum' :
              polygonal s ht + polygonal s hu + polygonal s hv + polygonal s hw
                = (s - 2) * qNat + bNat := by
            simpa [hQ'] using hpoly_sum
          have : (s - 2) * qNat + bNat + r = (s - 2) * qNat + remNat := by
            simp [r, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.sub_add_cancel hb_le_rem]
          -- commutate `q*m` to `qNat*m`
          have hn_decomp' : (s - 2) * qNat + remNat = n := by
            simpa [m, qNat, remNat, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn_decomp
          calc
            polygonal s ht + polygonal s hu + polygonal s hv + polygonal s hw + r
                = (s - 2) * qNat + bNat + r := by
                    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg (fun x => x + r) hpoly_sum'
            _ = (s - 2) * qNat + remNat := this
            _ = n := hn_decomp'
      | inr hqcase =>
          -- mode = true: `Q=qNat-1`, and `bNat ≥ remNat+2`.
          rcases hqcase with ⟨hmode, hQ, hb_ge, hb_le⟩
          let r : ℕ := m + remNat - bNat
          have hr : r ≤ s - 4 := by
            have hb_ge' : bNat ≥ remNat + 2 := by simpa [bNat, ht, hu, hv, hw, remFin] using hb_ge
            have : m + remNat - bNat ≤ m - 2 := by omega
            simpa [m, r] using this
          refine ⟨ht, hu, hv, hw, r, hr, ?_⟩
          have hQ' : cauchyTriPredSum4 ht hu hv hw = qNat - 1 := by
            simpa [qFin, qNat] using hQ
          have hpoly_sum' :
              polygonal s ht + polygonal s hu + polygonal s hv + polygonal s hw
                = (s - 2) * (qNat - 1) + bNat := by
            simpa [hQ'] using hpoly_sum
          have hn_decomp' : (s - 2) * qNat + remNat = n := by
            simpa [m, qNat, remNat, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn_decomp
          -- `(s-2)*(q-1) + b + (m+rem-b) = (s-2)*q + rem`
          calc
            polygonal s ht + polygonal s hu + polygonal s hv + polygonal s hw + r
                = (s - 2) * (qNat - 1) + bNat + r := by
                    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg (fun x => x + r) hpoly_sum'
            _ = (s - 2) * qNat + remNat := by
                    -- We need a *real* subtraction (not truncated), so we use the `b ≤ rem+3` bound
                    -- coming from `cauchyMediumSpecial_exists` and the fact `m = s-2 ≥ 3`.
                    have hq_ge1 : 1 ≤ qNat := Nat.succ_le_iff.2 (Nat.div_pos hm_le_n hm_pos)
                    have hb_le_small : bNat ≤ remNat + 3 := by
                      simpa [bNat, ht, hu, hv, hw, remFin] using hb_le
                    have hm_ge3 : 3 ≤ m := by
                      simpa [m] using Nat.sub_le_sub_right hs 2
                    have hb_le_total : bNat ≤ m + remNat := by omega
                    have hb_cancel : bNat + (m + remNat - bNat) = m + remNat := by
                      calc
                        bNat + (m + remNat - bNat) = (m + remNat - bNat) + bNat := by
                          ac_rfl
                        _ = m + remNat := Nat.sub_add_cancel hb_le_total
                    have hm_mul_pred :
                        m * (qNat - 1) + m = m * qNat := by
                      calc
                        m * (qNat - 1) + m = m * (qNat - 1) + m * 1 := by simp
                        _ = m * ((qNat - 1) + 1) := by simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
                        _ = m * qNat := by simpa [Nat.sub_add_cancel hq_ge1]
                    -- Now assemble:
                    --   m*(q-1) + b + (m+rem-b) = m*(q-1) + (m+rem) = m*q + rem.
                    -- and rewrite `m = s-2`.
                    calc
                      (s - 2) * (qNat - 1) + bNat + r
                          = m * (qNat - 1) + bNat + (m + remNat - bNat) := by
                                simp [r, m, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
                      _ = m * (qNat - 1) + (m + remNat) := by
                                simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hb_cancel]
                      _ = (m * qNat) + remNat := by
                                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, hm_mul_pred]
                      _ = (s - 2) * qNat + remNat := by
                                simp [m]
            _ = n := hn_decomp'
    ·
      -- Large remainder: use the default existence (gives `bNat ≤ 22 ≤ remNat`).
      rcases cauchyMediumDefault_exists qFin (by simpa [qFin, qNat] using hq_pos) with
        ⟨t, u, v, w, hQ, hb1, hb22⟩
      have ht : ℕ := t.1
      have hu : ℕ := u.1
      have hv : ℕ := v.1
      have hw : ℕ := w.1
      let bNat : ℕ := cauchyBSum4 ht hu hv hw
      have hb_le_22 : bNat ≤ 22 := by simpa [bNat, ht, hu, hv, hw] using hb22
      have hb_pos : 1 ≤ bNat := by simpa [bNat, ht, hu, hv, hw] using hb1
      have hb_le_rem : bNat ≤ remNat := by
        have hrem_ge : 22 ≤ remNat := le_of_not_gt hrem_small
        exact le_trans hb_le_22 hrem_ge
      let r : ℕ := remNat - bNat
      have hr : r ≤ s - 4 := by
        have hrem_lt_m : remNat < m := Nat.mod_lt n hm_pos
        have : remNat - bNat ≤ m - 2 := by omega
        simpa [m, r] using this
      refine ⟨ht, hu, hv, hw, r, hr, ?_⟩
      have hQ' : cauchyTriPredSum4 ht hu hv hw = qNat := by
        simpa [qFin, qNat] using hQ
      have hpoly_sum :
          polygonal s ht + polygonal s hu + polygonal s hv + polygonal s hw
            = (s - 2) * qNat + bNat := by
        -- same linearization as above
        have :
            polygonal s ht + polygonal s hu + polygonal s hv + polygonal s hw
              = (s - 2) * (cauchyTriPredSum4 ht hu hv hw) + bNat := by
          simp [bNat, cauchyBSum4, cauchyTriPredSum4, polygonal_eq_linear,
            Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.mul_assoc, Nat.mul_left_comm,
            Nat.mul_comm]
        simpa [hQ'] using this
      have hn_decomp' : (s - 2) * qNat + remNat = n := by
        simpa [m, qNat, remNat, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn_decomp
      calc
        polygonal s ht + polygonal s hu + polygonal s hv + polygonal s hw + r
            = (s - 2) * qNat + bNat + r := by
                simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg (fun x => x + r) hpoly_sum
        _ = (s - 2) * qNat + remNat := by
              simp [r, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.sub_add_cancel hb_le_rem]
        _ = n := hn_decomp'
    -/
  ·
    rcases nathanson_parameters_large s hs n hn_pos' (by simpa using hsmall) (by simpa using hmed) with
      ⟨b, q, r, hr, hb_odd, hb2_lt, h3a_lt, hn⟩
    -- shared tail (same as above)
    let a : ℕ := 2 * q + b
    have ha_odd : Odd a := by
      have heven : Even (2 * q) := ⟨q, by simp [two_mul]⟩
      simpa [a, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hb_odd.add_even heven
    rcases cauchy_lemma a b ha_odd hb_odd (by simpa [a] using hb2_lt) (by simpa [a] using h3a_lt) with
      ⟨x1, x2, x3, x4, ha_sq, hb_lin⟩
    have hpoly :
        polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4
          = (s - 2) * q + b := by
      have hId := GeometryOfNumbers.cauchy_polygonal_identity (s := s) hs3 x1 x2 x3 x4
      have ha_sq' :
          ((x1 : ℤ) ^ 2 + (x2 : ℤ) ^ 2 + (x3 : ℤ) ^ 2 + (x4 : ℤ) ^ 2) = (a : ℤ) := by
        have h : (a : ℤ) = ((x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 : ℕ) : ℤ) := by
          exact_mod_cast ha_sq
        simpa [pow_two, add_assoc, add_left_comm, add_comm] using h.symm
      have hb_lin' : ((x1 : ℤ) + (x2 : ℤ) + (x3 : ℤ) + (x4 : ℤ)) = (b : ℤ) := by
        have h : (b : ℤ) = ((x1 + x2 + x3 + x4 : ℕ) : ℤ) := by
          exact_mod_cast hb_lin
        simpa [add_assoc, add_left_comm, add_comm] using h.symm
      have haZ : (a : ℤ) = (2 * q + b : ℕ) := by rfl
      have h2 :
          (2 * (polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4) : ℤ)
            = (2 * ((s - 2) * q + b) : ℤ) := by
        dsimp at hId
        have : (2 * (polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4) : ℤ)
            =
          (((s : ℤ) - 2) * (a : ℤ) + ((2 : ℤ) - ((s : ℤ) - 2)) * (b : ℤ)) := by
          simpa [ha_sq', hb_lin'] using hId
        calc
          (2 * (polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4) : ℤ)
              = ((s : ℤ) - 2) * (a : ℤ) + ((2 : ℤ) - ((s : ℤ) - 2)) * (b : ℤ) := this
          _ = ((s : ℤ) - 2) * ((2 * q + b : ℕ) : ℤ) + ((4 : ℤ) - s) * (b : ℤ) := by
                simp [haZ, sub_eq_add_neg, add_left_comm, add_comm]
          _ = (2 * ((s - 2) * q + b) : ℤ) := by
                simp [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
                  sub_eq_add_neg, add_comm, mul_comm]
                ring_nf
      have hs2 : 2 ≤ s := le_trans (by decide : (2 : ℕ) ≤ 3) hs3
      let P : ℕ := polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4
      let Q : ℕ := (s - 2) * q + b
      have h2' : ((2 * P : ℕ) : ℤ) = ((2 * Q : ℕ) : ℤ) := by
        have hs_sub : ((s - 2 : ℕ) : ℤ) = (s : ℤ) - 2 := Int.ofNat_sub hs2
        have hQZ : ((Q : ℕ) : ℤ) = ((s : ℤ) - 2) * (q : ℤ) + (b : ℤ) := by
          simp [Q, Nat.cast_add, Nat.cast_mul, hs_sub, sub_eq_add_neg, add_comm, mul_comm]
        have hPZ : ((P : ℕ) : ℤ) =
            (polygonal s x1 : ℤ) + (polygonal s x2 : ℤ) + (polygonal s x3 : ℤ) + (polygonal s x4 : ℤ) := by
          simp [P, Nat.cast_add, add_assoc, add_left_comm, add_comm]
        calc
          ((2 * P : ℕ) : ℤ) = 2 * ((P : ℕ) : ℤ) := by simp [Nat.cast_mul]
          _ = 2 * ((polygonal s x1 : ℤ) + (polygonal s x2 : ℤ) + (polygonal s x3 : ℤ) + (polygonal s x4 : ℤ)) := by
                simp [hPZ, add_assoc]
          _ = 2 * (((s : ℤ) - 2) * (q : ℤ) + (b : ℤ)) := by
                simpa [P, Q, Nat.cast_add, Nat.cast_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
                  mul_assoc, mul_left_comm, mul_comm] using h2
          _ = 2 * ((Q : ℕ) : ℤ) := by simp [hQZ, add_comm]
          _ = ((2 * Q : ℕ) : ℤ) := by simp [Nat.cast_mul]
      have h2nat : 2 * P = 2 * Q := Int.ofNat.inj h2'
      have hpoly' : P = Q := by
        simpa [P, Q] using (Nat.mul_left_cancel (by decide : 0 < 2) h2nat)
      simpa [P, Q] using hpoly'
    refine ⟨x1, x2, x3, x4, r, hr, ?_⟩
    have : polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4 + r
        = (s - 2) * q + b + r := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg (fun t => t + r) hpoly
    simpa [hn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  /-
  (Historical) This was the old shared “postprocessing tail” when `cauchy_decomposition` used
  `nathanson_parameters` directly.

  We now branch explicitly to avoid the false `nathanson_parameters_medium` path, so this tail
  should not execute. We keep it for now as a reference while we work out a correct medium-branch
  argument.

  let a : ℕ := 2 * q + b
  have ha_odd : Odd a := by
    -- `2*q` is even, so `Odd b` ⇒ `Odd (2*q + b)`.
    have heven : Even (2 * q) := ⟨q, by simp [two_mul]⟩
    simpa [a, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hb_odd.add_even heven

  rcases cauchy_lemma a b ha_odd hb_odd (by simpa [a] using hb2_lt) (by simpa [a] using h3a_lt) with
    ⟨x1, x2, x3, x4, ha_sq, hb_lin⟩

  -- Pure algebra: turn `(a = Σ x_i^2, b = Σ x_i)` into a polygonal sum via the Cauchy identity.
  have hpoly :
      polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4
        = (s - 2) * q + b := by
    -- Use the already-proved identity in ℤ, then pull back to ℕ.
    have hId := GeometryOfNumbers.cauchy_polygonal_identity (s := s) hs3 x1 x2 x3 x4
    -- Rewrite `Σ x_i^2` and `Σ x_i` using `ha_sq` and `hb_lin`, and `a = 2q + b`.
    have ha_sq' : ((x1 : ℤ) ^ 2 + (x2 : ℤ) ^ 2 + (x3 : ℤ) ^ 2 + (x4 : ℤ) ^ 2) = (a : ℤ) := by
      -- Cast the Nat equality `ha_sq` into ℤ, then normalize casts/powers.
      have h : (a : ℤ) = ((x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x4 ^ 2 : ℕ) : ℤ) := by
        exact_mod_cast ha_sq
      -- Turn `↑(x^2)` into `(↑x)^2` and expand the casted sum.
      simpa [pow_two, add_assoc, add_left_comm, add_comm] using h.symm
    have hb_lin' : ((x1 : ℤ) + (x2 : ℤ) + (x3 : ℤ) + (x4 : ℤ)) = (b : ℤ) := by
      have h : (b : ℤ) = ((x1 + x2 + x3 + x4 : ℕ) : ℤ) := by
        exact_mod_cast hb_lin
      simpa [add_assoc, add_left_comm, add_comm] using h.symm
    -- `a = 2q + b` by definition.
    have ha_def : (a : ℤ) = (2 * q + b : ℕ) := by
      -- keep it in ℕ (then cast)
      rfl
    -- Normalize the identity.
    -- After substitution we get: `2*sumP = ((s-2):ℤ)*(2q+b) + (4-s)*b = 2*((s-2)*q + b)`.
    have h2 :
        (2 * (polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4) : ℤ)
          = (2 * ((s - 2) * q + b) : ℤ) := by
      -- Expand the Cauchy identity and simplify in ℤ.
      -- (This is a computation lemma; we keep it blunt and let `ring` do the algebra.)
      -- NOTE: `hId` uses `m := (s:ℤ)-2`.
      dsimp at hId
      -- substitute the square and linear sums
      have : (2 * (polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4) : ℤ)
          =
        (((s : ℤ) - 2) * (a : ℤ) + ((2 : ℤ) - ((s : ℤ) - 2)) * (b : ℤ)) := by
        -- from `hId` + rewriting
        simpa [ha_sq', hb_lin'] using hId
      -- now rewrite `a` and finish by ring arithmetic
      -- `a = 2*q + b` in ℕ, so also in ℤ.
      have haZ : (a : ℤ) = (2 * q + b : ℕ) := by
        rfl
      -- push through and normalize
      -- `((s:ℤ)-2) * (2q+b) + (4-s)*b = 2*((s-2)*q + b)`
      -- (Note `((2:ℤ)-((s:ℤ)-2)) = 4 - s`.)
      calc
        (2 * (polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4) : ℤ)
            = ((s : ℤ) - 2) * (a : ℤ) + ((2 : ℤ) - ((s : ℤ) - 2)) * (b : ℤ) := this
        _ = ((s : ℤ) - 2) * ((2 * q + b : ℕ) : ℤ) + ((4 : ℤ) - s) * (b : ℤ) := by
              simp [haZ, sub_eq_add_neg, add_left_comm, add_comm]
        _ = (2 * ((s - 2) * q + b) : ℤ) := by
              -- Close with ring arithmetic in ℤ, after expanding `Nat.cast_add/mul`.
              -- (Otherwise `ring_nf` tends to get stuck on terms like `↑(2*q+b)`.)
              simp [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
                sub_eq_add_neg, add_comm, mul_comm]
              ring_nf
    -- Convert the ℤ identity into an `Int.ofNat` identity, then use injectivity.
    -- (Our `simp` steps tend to normalize `((2 * n : ℕ) : ℤ)` into `2 * (n : ℤ)`,
    -- so we re-package both sides explicitly as `Int.ofNat`.)
    have hs2 : 2 ≤ s := le_trans (by decide : (2 : ℕ) ≤ 3) hs3
    let P : ℕ := polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4
    let Q : ℕ := (s - 2) * q + b
    have h2' : ((2 * P : ℕ) : ℤ) = ((2 * Q : ℕ) : ℤ) := by
      -- rewrite casts on both sides and use `h2`
      have hs_sub : ((s - 2 : ℕ) : ℤ) = (s : ℤ) - 2 := Int.ofNat_sub hs2
      have hQZ : ((Q : ℕ) : ℤ) = ((s : ℤ) - 2) * (q : ℤ) + (b : ℤ) := by
        -- `Q = (s-2)*q + b`
        simp [Q, Nat.cast_add, Nat.cast_mul, hs_sub, sub_eq_add_neg, add_comm, mul_comm]
      have hPZ : ((P : ℕ) : ℤ) = (polygonal s x1 : ℤ) + (polygonal s x2 : ℤ) +
            (polygonal s x3 : ℤ) + (polygonal s x4 : ℤ) := by
        simp [P, Nat.cast_add, add_assoc, add_left_comm, add_comm]
      -- Now: `((2*P):ℤ) = 2*PZ` and similarly for Q, then use `h2`.
      calc
        ((2 * P : ℕ) : ℤ) = 2 * ((P : ℕ) : ℤ) := by
            simp [Nat.cast_mul]
        _ = 2 * ((polygonal s x1 : ℤ) + (polygonal s x2 : ℤ) + (polygonal s x3 : ℤ) + (polygonal s x4 : ℤ)) := by
            simp [hPZ, add_assoc]
        _ = 2 * (((s : ℤ) - 2) * (q : ℤ) + (b : ℤ)) := by
            simpa [P, Q, Nat.cast_add, Nat.cast_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
              mul_assoc, mul_left_comm, mul_comm] using h2
        _ = 2 * ((Q : ℕ) : ℤ) := by
            simp [hQZ, add_comm]
        _ = ((2 * Q : ℕ) : ℤ) := by
            simp [Nat.cast_mul]

    have h2nat : 2 * P = 2 * Q := Int.ofNat.inj h2'
    -- unwrap `P,Q`
    simpa [P, Q] using (Nat.mul_left_cancel (by decide : 0 < 2) h2nat)

  -/

/-- A “local shape lemma” for the Cauchy route:

This is the algebraic rearrangement of `cauchy_polygonal_identity` that we actually use when we
choose a 4-square representation and then want to *solve for* the quadratic piece.

It is proved in `Experiments/CauchyIdentityScratch.lean` and duplicated here so the main
proof can depend on it without importing experiment modules. -/
lemma cauchy_polygonal_identity_rearranged
    (s : ℕ) (hs : 3 ≤ s) (t u v w : ℕ) :
    let m : ℤ := (s : ℤ) - 2
    m * ((t : ℤ) ^ 2 + (u : ℤ) ^ 2 + (v : ℤ) ^ 2 + (w : ℤ) ^ 2) =
      (2 * (polygonal s t + polygonal s u + polygonal s v + polygonal s w) : ℤ)
        + ((m - 2) * ((t : ℤ) + (u : ℤ) + (v : ℤ) + (w : ℤ))) := by
  have h :=
    GeometryOfNumbers.cauchy_polygonal_identity (s := s) hs t u v w
  dsimp at h ⊢
  linarith

/-!
### Note on removed scaffolding

Earlier iterations kept “proposed sub-lemmas” here as a planning aid. They were unused and made the
file read as unfinished even though the main theorem is proved, so they were removed.
-/

/-- **Padding lemma** for the `s ≥ 5` branch:

If you can write \(n\) as a sum of four `s`-gonal numbers, then you can write it as a sum of `s`
`s`-gonal numbers by padding the remaining `s-4` slots with `0`.

This isolates the “index bookkeeping” (Fin sums) from the actual number theory in
`cauchy_decomposition`. -/
theorem fermat_polygonal_ge5_of_cauchy_decomposition
    (s : ℕ) (hs : 5 ≤ s) (n : ℕ)
    (h : ∃ t u v w r : ℕ, r ≤ s - 4 ∧ polygonal s t + polygonal s u + polygonal s v + polygonal s w + r = n) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  classical
  have hs4 : 4 ≤ s := le_trans (by decide : (4 : ℕ) ≤ 5) hs
  rcases h with ⟨t, u, v, w, r, hr, htuvw⟩
  have hs4r : 4 + r ≤ s := by
    -- from `r ≤ s-4` we get `4+r ≤ 4+(s-4) = s`
    have : 4 + r ≤ 4 + (s - 4) := Nat.add_le_add_left hr 4
    simpa [Nat.add_sub_of_le hs4, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
  rcases Nat.exists_eq_add_of_le hs4r with ⟨k, rfl⟩

  -- Fill a `Fin (4+r+k)`-indexed family:
  -- - first 4 entries are `t,u,v,w`
  -- - next `r` entries are `1` (so their polygonal value is `1`)
  -- - remainder are `0`
  let first4 : Fin 4 → ℕ := ![t, u, v, w]
  let terms : Fin (4 + r + k) → ℕ := fun i =>
    if h0 : (i : ℕ) < 4 then
      first4 ⟨(i : ℕ), h0⟩
    else if h1 : (i : ℕ) < 4 + r then
      1
    else
      0
  refine ⟨terms, ?_⟩

  -- Split the sum into the first `4+r` indices and the trailing `k` indices (which are zero).
  have htrunc :
      ∀ j : Fin k, polygonal (4 + r + k) (terms (Fin.natAdd (4 + r) j)) = 0 := by
    intro j
    -- For `i = (4+r)+j`, both `i < 4` and `i < 4+r` are false.
    have hj0 : ¬ (4 + r + (j : ℕ) < 4) := by omega
    have hj1 : ¬ (4 + r + (j : ℕ) < 4 + r) := by
      -- `4+r ≤ 4+r+j`
      exact Nat.not_lt.2 (Nat.le_add_right (4 + r) (j : ℕ))
    simp [terms, Fin.natAdd, hj0, hj1]

  -- Now the `Fin.sum_univ_add` lemma does the bookkeeping for us.
  have hsum :
      (∑ i : Fin (4 + r + k), polygonal (4 + r + k) (terms i))
        = (∑ i : Fin (4 + r), polygonal (4 + r + k) (terms (Fin.castAdd k i))) := by
    simp [Fin.sum_univ_add, htrunc]

  -- On `Fin.castAdd`, we are always in the “first `4+r`” region, so the last `if` is false.
  have hterms_cast :
      ∀ i : Fin (4 + r), terms (Fin.castAdd k i) =
        if h0 : (i : ℕ) < 4 then first4 ⟨(i : ℕ), h0⟩ else 1 := by
    intro i
    have hi : ((Fin.castAdd k i : Fin (4 + r + k)) : ℕ) < 4 + r := by
      simp [Fin.castAdd]
    by_cases h0 : (i : ℕ) < 4
    · simp [terms, h0]
    · simp [terms, h0]

  -- Split the remaining `Fin (4+r)` sum into the first 4 terms and the next `r` terms.
  have hsum4r :
      (∑ i : Fin (4 + r), polygonal (4 + r + k) (terms (Fin.castAdd k i)))
        =
        (∑ i : Fin 4, polygonal (4 + r + k) (first4 i))
          + (∑ _i : Fin r, polygonal (4 + r + k) 1) := by
    -- Use `Fin.sum_univ_add` at size `4+r`.
    -- The `Fin.castAdd r` part corresponds to indices `< 4`; the `Fin.natAdd 4` part corresponds
    -- to indices `4 ..< 4+r` and those are all `1`.
    have hfirst :
        ∀ i : Fin 4, terms (Fin.castAdd k (Fin.castAdd r i)) = first4 i := by
      intro i
      have hi0 : (i : ℕ) < 4 := i.isLt
      -- reuse `hterms_cast` with `i' := Fin.castAdd r i : Fin (4+r)`
      simpa [hterms_cast, hi0, Fin.castAdd] using (hterms_cast (i := (Fin.castAdd r i)))
    have hones :
        ∀ j : Fin r, terms (Fin.castAdd k (Fin.natAdd 4 j)) = 1 := by
      intro j
      have hj0 : ¬ ((Fin.natAdd 4 j : Fin (4 + r)) : ℕ) < 4 := by
        simp [Fin.natAdd]
      have hj1 : ((Fin.natAdd 4 j : Fin (4 + r)) : ℕ) < 4 + r := by
        simp [Fin.natAdd, Nat.add_comm]
      -- `hj1` is automatic, but we keep it explicit.
      simp [terms]
    -- Put the split together.
    simp [Fin.sum_univ_add, hfirst, hones, Nat.add_left_comm, Nat.add_comm]

  -- Put it together.
  calc
    (∑ i : Fin (4 + r + k), polygonal (4 + r + k) (terms i))
        = (∑ i : Fin (4 + r), polygonal (4 + r + k) (terms (Fin.castAdd k i))) := hsum
    _ = (∑ i : Fin 4, polygonal (4 + r + k) (first4 i))
          + (∑ _i : Fin r, polygonal (4 + r + k) 1) := hsum4r
    _ = (polygonal (4 + r + k) t + polygonal (4 + r + k) u + polygonal (4 + r + k) v + polygonal (4 + r + k) w)
          + r := by
          -- Expand the `Fin 4` sum and compute the `Fin r` sum using `polygonal_one`.
          simp [first4, Fin.sum_univ_four, Nat.add_left_comm, Nat.add_comm]
    _ = n := by
          -- `htuvw : polygonal s t + ... + polygonal s w + r = n` (with `s = 4+r+k`).
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using htuvw

theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  classical
  rcases lt_or_eq_of_le hs with hs_gt3 | rfl
  · have hs4 : 4 ≤ s := Nat.succ_le_of_lt hs_gt3
    rcases lt_or_eq_of_le hs4 with hs_gt4 | rfl
    · -- s ≥ 5: Cauchy's proof route.
      have h_s5 : 5 ≤ s := Nat.succ_le_of_lt hs_gt4
      -- Once `cauchy_decomposition` is proved, this branch is just padding + index bookkeeping.
      -- The previous attempt at the bookkeeping is useful as a sketch, but we keep it out of the
      -- elaboration path until the underlying number-theory step is in place.
      refine fermat_polygonal_ge5_of_cauchy_decomposition s h_s5 n ?_
      exact cauchy_decomposition s h_s5 n
    · -- s = 4: Lagrange's Four-Square Theorem.
      obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares n
      use ![a, b, c, d]
      simp [polygonal_four_eq_sq]
      rw [← habcd]
      simp [Fin.sum_univ_succ]
      ring
  · -- s = 3: Gauss's Triangular Number Theorem.
    obtain ⟨a, b, c, habc⟩ := gauss_triangular n
    use ![a, b, c]
    dsimp [triangular] at habc
    rw [← habc]
    simp [Fin.sum_univ_succ]
    ring

end GeometryOfNumbers