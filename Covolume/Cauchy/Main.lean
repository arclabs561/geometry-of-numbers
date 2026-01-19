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
  rcases Covolume.sum_three_squares_of_three_mod_eight m hm8 with ⟨x, y, z, hxyz⟩

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
-- TODO boundary (from `PROOF_ROADMAP.md`):
-- Cauchy/Nathanson reduction should prove that for `s ≥ 5`, every `n` is a sum of `s` `s`-gonal
-- numbers, with a construction where *at most four* of the terms are not `0` or `1`.
-- This is the remaining “Cauchy lemma” stage of the Fermat polygonal theorem in this repo.

/-- Nathanson-style parameter selection (stub).

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
    (x - 2) % m = (m * q + (m - 3)) % m := by simpa [hxsub]
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

lemma nathanson_parameters (s : ℕ) (hs : 5 ≤ s) (n : ℕ) (hn : 0 < n) :
    ∃ b q r : ℕ,
      r ≤ s - 4 ∧ Odd b ∧
        ((b : ℤ) ^ 2 < 4 * ((2 * q + b : ℕ) : ℤ)) ∧
        (3 * ((2 * q + b : ℕ) : ℤ) < (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4) ∧
        n = (s - 2) * q + b + r := by
  sorry

/-- Cauchy’s lemma (stub).

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
  sorry

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
  ### Cauchy/Nathanson proof skeleton (leaves only two hard lemmas)

  The “real work” is split into:

  1. `nathanson_parameters`: choose `b q r` with `Odd b`, `r ≤ s-4`, and
     \[
       n = (s-2)q + b + r
     \]
     plus the two key inequalities needed for Cauchy’s lemma with \(a = 2q+b\).

  2. `cauchy_lemma`: from those inequalities (and oddness) obtain
     \[
       a = x_1^2+x_2^2+x_3^2+x_4^2,\quad b = x_1+x_2+x_3+x_4.
     \]

  Everything after that is **pure algebra** via `cauchy_polygonal_identity`.
  -/

  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  rcases nathanson_parameters s hs n hn_pos with ⟨b, q, r, hr, hb_odd, hb2_lt, h3a_lt, hn⟩
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
    have hId := Covolume.cauchy_polygonal_identity (s := s) hs3 x1 x2 x3 x4
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

  refine ⟨x1, x2, x3, x4, r, hr, ?_⟩
  -- finish using `hn : n = (s-2)*q + b + r`
  -- and `hpoly : Σ P(s,xi) = (s-2)*q + b`.
  -- reorder sums to match exactly
  have : polygonal s x1 + polygonal s x2 + polygonal s x3 + polygonal s x4 + r
      = (s - 2) * q + b + r := by
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using congrArg (fun t => t + r) hpoly
  simpa [hn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this

/-- A “local shape lemma” for the Cauchy route:

This is the algebraic rearrangement of `cauchy_polygonal_identity` that we actually use when we
choose a 4-square representation and then want to *solve for* the quadratic piece.

It is proved in `Covolume/Experiments/CauchyIdentityScratch.lean` and duplicated here so the main
proof can depend on it without importing experiment modules. -/
lemma cauchy_polygonal_identity_rearranged
    (s : ℕ) (hs : 3 ≤ s) (t u v w : ℕ) :
    let m : ℤ := (s : ℤ) - 2
    m * ((t : ℤ) ^ 2 + (u : ℤ) ^ 2 + (v : ℤ) ^ 2 + (w : ℤ) ^ 2) =
      (2 * (polygonal s t + polygonal s u + polygonal s v + polygonal s w) : ℤ)
        + ((m - 2) * ((t : ℤ) + (u : ℤ) + (v : ℤ) + (w : ℤ))) := by
  have h :=
    Covolume.cauchy_polygonal_identity (s := s) hs t u v w
  dsimp at h ⊢
  linarith

/-- Proposed “sub-lemma 1” (stub): an odd integer parameter with clean bounds.

This is just `exists_odd_in_interval`, but returns the value in `ℤ` plus *both* strict inequalities,
so downstream steps can rewrite without re-proving floor bounds.

In the full Cauchy argument, this `b` will be the knob used to control a linear correction term. -/
lemma cauchy_choose_odd_parameter
    (L U : ℝ) (hLU : L + 2 < U) :
    ∃ b : ℤ, Odd b ∧ L < (b : ℝ) ∧ (b : ℝ) < U := by
  exact exists_odd_in_interval (L := L) (U := U) hLU

/-- Proposed “sub-lemma 2” (stub): a 4-square representation for a chosen integer.

We will eventually choose a specific `N` as a function of `s,n` and an interval-picked parameter,
then call `Nat.sum_four_squares` to obtain `a,b,c,d` with `a^2+b^2+c^2+d^2 = N`. -/
lemma cauchy_four_squares (N : ℕ) :
    ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = N := by
  rcases Nat.sum_four_squares N with ⟨a, b, c, d, habcd⟩
  exact ⟨a, b, c, d, habcd⟩

/-- Proposed “sub-lemma 3” (stub): from a 4-square datum, produce a “near miss” polygonal sum in ℤ.

This is the place where `cauchy_polygonal_identity_rearranged` gets applied.
We keep it as a stub until we commit to the precise choice of `N` and the correction strategy. -/
lemma cauchy_near_miss_from_four_squares
    (_s : ℕ) (_hs : 5 ≤ _s) (_a _b _c _d : ℕ) :
    True := by
  trivial

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

end Covolume
