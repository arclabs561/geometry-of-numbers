import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import Covolume.Legendre.Exceptions
import Covolume.Legendre.Ankeny

namespace Covolume

/-!
## Legendre “easy direction”

We prove the modular obstruction:
\[
  x^2 + y^2 + z^2 = n \;\Rightarrow\; n \neq 4^a(8k+7).
\]

Two finite-ring facts drive the proof:

- In `ZMod 4`, `1 + y^2 + z^2 ≠ 0` for all `y,z`. (Checked by `decide`.)
  This implies: if `4 ∣ x^2+y^2+z^2` then `x,y,z` are even, hence we can divide the representation by `4`.

- In `ZMod 8`, `x^2 + y^2 + z^2 ≠ 7` for all `x,y,z`. (Checked by `decide`.)
  This rules out the `8k+7` base case after descending.
-/

private lemma zmod4_sq_eq_one_of_odd (x : ℕ) (hx : Odd x) : ((x : ZMod 4) ^ 2) = 1 := by
  rcases hx with ⟨m, rfl⟩
  -- `(2m+1)^2 = 4*(m*(m+1)) + 1`, and `4 = 0` in `ZMod 4`.
  -- First normalize the coercion `(2*m+1 : ℕ) ↦ ZMod 4`.
  have hcast : ((2 * m + 1 : ℕ) : ZMod 4) = (2 * (m : ZMod 4) + 1) := by
    simp [Nat.cast_add, Nat.cast_mul]
  calc
    (((2 * m + 1 : ℕ) : ZMod 4) ^ 2)
        = ((2 * (m : ZMod 4) + 1) ^ 2) := by simpa [hcast]
    _ = (4 : ZMod 4) * (m : ZMod 4) * ((m : ZMod 4) + 1) + 1 := by ring
    _ = 1 := by
          -- `4 = 0` in `ZMod 4`.
          have h4 : (4 : ZMod 4) = 0 := by
            simpa using (ZMod.natCast_self 4)
          simpa [h4]

private lemma zmod4_one_add_sq_add_sq_ne0 : ∀ y z : ZMod 4, (1 + y ^ 2 + z ^ 2) ≠ 0 := by
  decide

private lemma zmod8_sum_three_sq_ne7 : ∀ x y z : ZMod 8, (x ^ 2 + y ^ 2 + z ^ 2) ≠ 7 := by
  decide

private lemma even_of_sum_three_squares_eq_mul_four {x y z m : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 * m) : Even x ∧ Even y ∧ Even z := by
  -- If any variable is odd, reduce mod 4 and contradict the finite check in `ZMod 4`.
  have hx : Even x := by
    rcases Nat.even_or_odd x with hx | hx
    · exact hx
    · have hx1 : ((x : ZMod 4) ^ 2) = 1 := zmod4_sq_eq_one_of_odd x hx
      have hcast := congrArg (fun n : ℕ => (n : ZMod 4)) h
      -- In `ZMod 4`, `4*m = 0`.
      have h0 : ((x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
      have : (1 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        -- replace `x^2` by `1`
        simpa [hx1, add_assoc, add_left_comm, add_comm] using h0
      exact False.elim ((zmod4_one_add_sq_add_sq_ne0 (y := (y : ZMod 4)) (z := (z : ZMod 4))) this)
  have hy : Even y := by
    rcases Nat.even_or_odd y with hy | hy
    · exact hy
    · have hy1 : ((y : ZMod 4) ^ 2) = 1 := zmod4_sq_eq_one_of_odd y hy
      have hcast := congrArg (fun n : ℕ => (n : ZMod 4)) (by
        simpa [add_assoc, add_left_comm, add_comm] using h)
      have h0 : ((y : ZMod 4) ^ 2 + (x : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
      have : (1 + (x : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        simpa [hy1, add_assoc, add_left_comm, add_comm] using h0
      exact False.elim ((zmod4_one_add_sq_add_sq_ne0 (y := (x : ZMod 4)) (z := (z : ZMod 4))) this)
  have hz : Even z := by
    rcases Nat.even_or_odd z with hz | hz
    · exact hz
    · have hz1 : ((z : ZMod 4) ^ 2) = 1 := zmod4_sq_eq_one_of_odd z hz
      have hcast := congrArg (fun n : ℕ => (n : ZMod 4)) (by
        simpa [add_assoc, add_left_comm, add_comm] using h)
      have h0 : ((z : ZMod 4) ^ 2 + (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2) = 0 := by
        simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
      have : (1 + (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2) = 0 := by
        simpa [hz1, add_assoc, add_left_comm, add_comm] using h0
      exact False.elim ((zmod4_one_add_sq_add_sq_ne0 (y := (x : ZMod 4)) (z := (y : ZMod 4))) this)
  exact ⟨hx, hy, hz⟩

private lemma descend_four {x y z m : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 * m) :
    ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = m := by
  have hev := even_of_sum_three_squares_eq_mul_four (x := x) (y := y) (z := z) (m := m) h
  rcases hev.1 with ⟨x', rfl⟩
  rcases hev.2.1 with ⟨y', rfl⟩
  rcases hev.2.2 with ⟨z', rfl⟩
  -- Factor out the `4` on the LHS and cancel.
  have hfactor :
      (x' + x') ^ 2 + (y' + y') ^ 2 + (z' + z') ^ 2 = 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) := by
    -- expand squares and collect `4`
    simp [pow_two]
    ring
  have hmul : 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) = 4 * m := by
    calc
      4 * (x' ^ 2 + y' ^ 2 + z' ^ 2)
          = (x' + x') ^ 2 + (y' + y') ^ 2 + (z' + z') ^ 2 := by
                simpa [hfactor] using hfactor.symm
      _ = 4 * m := by simpa using h
  have hcancel : x' ^ 2 + y' ^ 2 + z' ^ 2 = m :=
    Nat.mul_left_cancel (show 0 < 4 from by decide) hmul
  exact ⟨x', y', z', hcancel⟩

private lemma descend_four_pow {a x y z t : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 ^ a * t) :
    ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = t := by
  induction a generalizing x y z with
  | zero =>
      refine ⟨x, y, z, ?_⟩
      simpa using h
  | succ a ih =>
      have h' : x ^ 2 + y ^ 2 + z ^ 2 = 4 * (4 ^ a * t) := by
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
      rcases descend_four (x := x) (y := y) (z := z) (m := 4 ^ a * t) h' with ⟨x1, y1, z1, h1⟩
      exact ih (x := x1) (y := y1) (z := z1) h1

/-- If `n` is not a three-square exception, then after removing a maximal power of `4` we get a
reduced factor `t` with `t % 8 ≠ 7`. This is the mod-8 obstruction that remains after `4`-descent. -/
lemma exists_four_pow_mul_reduced (n : ℕ) (hn0 : n ≠ 0) (h : ¬ is_three_square_exception n) :
    ∃ a t : ℕ, n = 4 ^ a * t ∧ (¬ 4 ∣ t) ∧ t % 8 ≠ 7 := by
  classical
  -- Write `n = 2^k * m` with `2 ∤ m`.
  obtain ⟨k, m, hm2, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 2 (by decide : (2 : ℕ) ≠ 1)
  -- Split off powers of `4 = 2^2` from `2^k`.
  let a : ℕ := k / 2
  let b : ℕ := k % 2
  have hk : k = 2 * a + b := by
    -- `k = 2*(k/2) + k%2`
    simpa [a, b] using (Nat.div_add_mod k 2).symm
  have hb_lt : b < 2 := Nat.mod_lt k (by decide : 0 < 2)
  have hb : b = 0 ∨ b = 1 := by
    omega
  have hpow : 2 ^ k = 4 ^ a * 2 ^ b := by
    -- `2^k = 2^(2*a+b) = 2^(2*a) * 2^b = (2^2)^a * 2^b = 4^a * 2^b`
    calc
      2 ^ k = 2 ^ (2 * a + b) := by simp [hk]
      _ = 2 ^ (2 * a) * 2 ^ b := by simp [pow_add]
      _ = (2 ^ 2) ^ a * 2 ^ b := by simp [pow_mul]
      _ = 4 ^ a * 2 ^ b := by simp [pow_two]
  -- Define the reduced factor `t := 2^b * m`.
  let t : ℕ := 2 ^ b * m
  have hn' : n = 4 ^ a * t := by
    -- `n = 2^k * m = (4^a * 2^b) * m = 4^a * (2^b * m)`
    calc
      n = 2 ^ k * m := hnm
      _ = (4 ^ a * 2 ^ b) * m := by simp [hpow, Nat.mul_assoc]
      _ = 4 ^ a * (2 ^ b * m) := by ring_nf
      _ = 4 ^ a * t := by rfl
  have ht4 : ¬ 4 ∣ t := by
    -- Since `t = 2^b * m` with `b ∈ {0,1}` and `2 ∤ m`, we have `4 ∤ t`.
    rcases hb with hb0 | hb1
    · -- `b = 0` so `t = m`, and `4 ∣ m → 2 ∣ m`, contradicting `hm2`.
      have ht : t = m := by simp [t, hb0]
      intro h4t
      have h4m : 4 ∣ m := by simpa [ht] using h4t
      have h2m : 2 ∣ m := dvd_trans (by exact ⟨2, rfl⟩) h4m
      exact hm2 h2m
    · -- `b = 1` so `t = 2*m`. If `4 ∣ 2*m` then `2 ∣ m`, contradicting `hm2`.
      have ht : t = 2 * m := by simp [t, hb1]
      intro h4t
      have h4tm : 4 ∣ 2 * m := by simpa [ht] using h4t
      rcases h4tm with ⟨k, hk⟩
      have hk' : 2 * m = 2 * (2 * k) := by
        have h4 : 4 * k = 2 * (2 * k) := by ring
        exact hk.trans h4
      have hm_eq : m = 2 * k := Nat.mul_left_cancel (show 0 < 2 from by decide) hk'
      have h2m : 2 ∣ m := ⟨k, hm_eq⟩
      exact hm2 h2m

  refine ⟨a, t, hn', ht4, ?_⟩
  intro ht7
  -- If `t % 8 = 7`, then `t = 8*(t/8)+7`, hence `n` is an exception: contradiction.
  have ht_eq : t = 8 * (t / 8) + 7 := by
    have := (Nat.div_add_mod t 8).symm
    -- `t = 8*(t/8) + t%8`, then rewrite `t%8` to `7`.
    simpa [ht7, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using this
  apply h
  refine ⟨a, t / 8, ?_⟩
  -- `n = 4^a * (8*(t/8)+7)`
  calc
    n = 4 ^ a * t := hn'
    _ = 4 ^ a * (8 * (t / 8) + 7) := by
          -- Apply `ht_eq` under multiplication (avoid rewriting `t` inside `t/8`).
          simpa using congrArg (fun r : ℕ => 4 ^ a * r) ht_eq

/-- Necessary condition: representation as a sum of three squares implies n is not an exception. -/
theorem not_exception_of_sum_three_squares (n : ℕ) (h : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) :
    ¬ is_three_square_exception n := by
  rcases h with ⟨x, y, z, hxyz⟩
  intro hex
  rcases hex with ⟨a, k, hn⟩
  -- descend `4^a` to get a representation of `8*k+7`
  have hdesc : ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = 8 * k + 7 := by
    refine descend_four_pow (a := a) (x := x) (y := y) (z := z) (t := 8 * k + 7) ?_
    simpa [hn, hxyz, mul_assoc, mul_left_comm, mul_comm]
  rcases hdesc with ⟨x', y', z', h'⟩
  -- reduce mod 8 and contradict the finite check in `ZMod 8`
  have hcast := congrArg (fun n : ℕ => (n : ZMod 8)) h'
  have : ((x' : ZMod 8) ^ 2 + (y' : ZMod 8) ^ 2 + (z' : ZMod 8) ^ 2) = (7 : ZMod 8) := by
    -- `8*k` vanishes in `ZMod 8`.
    simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
  exact (zmod8_sum_three_sq_ne7 (x := (x' : ZMod 8)) (y := (y' : ZMod 8)) (z := (z' : ZMod 8))) this

/-- Sufficient condition: n not an exception implies representation as a sum of three squares. -/
theorem sum_three_squares_of_not_exception (n : ℕ) (h : ¬ is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  by_cases hn0 : n = 0
  · subst hn0
    refine ⟨0, 0, 0, by simp⟩
  obtain ⟨a, t, hn, _ht4, ht7⟩ := exists_four_pow_mul_reduced n hn0 h
  -- After peeling off powers of `4`, the remaining factor `t` satisfies `t % 8 ≠ 7`.
  --
  -- We currently have a complete proof for the residue class `t % 8 = 3` via Ankeny.
  -- The remaining reduced residue classes are `t % 8 ∈ {1,2,5,6}`; those are still TODO.
  by_cases ht3 : t % 8 = 3
  · have ht_rep : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = t :=
      sum_three_squares_of_three_mod_eight t ht3
    have hn_rep :
        ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = (2 ^ a) ^ 2 * t :=
      sum_three_squares_mul_sq (2 ^ a) t ht_rep
    rcases hn_rep with ⟨x, y, z, hxyz⟩
    refine ⟨x, y, z, ?_⟩
    have hpow : (2 ^ a) ^ 2 = 4 ^ a := by
      -- `(2^a)^2 = 2^(a*2)` and `4^a = (2^2)^a = 2^(2*a)`.
      -- Keep it explicit to avoid `simp` loops in downstream glue.
      calc
        (2 ^ a) ^ 2 = 2 ^ (a * 2) := by simp [pow_mul]
        _ = 2 ^ (2 * a) := by simp [Nat.mul_comm]
        _ = (2 ^ 2) ^ a := by simp [pow_mul]
        _ = 4 ^ a := by simp [pow_two]
    calc
      x ^ 2 + y ^ 2 + z ^ 2 = (2 ^ a) ^ 2 * t := hxyz
      _ = 4 ^ a * t := by simpa [hpow]
      _ = n := hn.symm
  ·
    -- Now `t % 8 ≠ 3`. Since we also have `t % 8 ≠ 7`, the only possible residues are:
    -- `t % 8 ∈ {0,1,2,4,5,6}`.
    --
    -- Moreover, `4 ∣ t` is impossible by construction (returned by `exists_four_pow_mul_reduced`),
    -- hence `t % 8` cannot be `0` or `4`. That leaves exactly:
    -- `t % 8 ∈ {1,2,5,6}`.
    have ht3_ne : t % 8 ≠ 3 := ht3
    have ht7_ne : t % 8 ≠ 7 := ht7
    have ht_lt : t % 8 < 8 := Nat.mod_lt t (by decide : 0 < 8)
    -- We prefer an explicit finite split here so the remaining proof obligations are visible.
    interval_cases hmod : t % 8
    · -- 0
      -- If `t % 8 = 0` then `8 ∣ t` hence `4 ∣ t`, contradiction.
      have h4 : 4 ∣ t := by
        have h8 : 8 ∣ t := Nat.dvd_of_mod_eq_zero hmod
        exact dvd_trans (by exact ⟨2, rfl⟩) h8
      exact (_ht4 h4).elim
    · -- 1
      -- TODO: prove the `t % 8 = 1` case.
      -- Candidate routes:
      -- - direct residue lemma for `1 mod 8`,
      -- - or a reduction to the `3 mod 8` case via a small arithmetic transform.
      sorry
    · -- 2
      -- TODO: prove the `t % 8 = 2` case.
      sorry
    · -- 3 (contradicts ht3)
      exact (ht3_ne (by simpa using hmod)).elim
    · -- 4
      -- If `t % 8 = 4` then `4 ∣ t`, contradiction.
      have ht_eq : t = 8 * (t / 8) + 4 := by
        -- `t = 8*(t/8) + t%8` and `t%8 = 4`.
        have := (Nat.div_add_mod t 8).symm
        -- `8*(t/8) + t%8 = t`
        -- rewrite `t%8` using `hmod`
        simpa [hmod, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
      have h4 : 4 ∣ t := by
        -- `4 ∣ 8*(t/8)` and `4 ∣ 4`, hence `4 ∣ t`.
        have h48 : 4 ∣ 8 := by decide
        have h4a : 4 ∣ 8 * (t / 8) := dvd_mul_of_dvd_left h48 _
        have h44 : 4 ∣ 4 := by exact dvd_rfl
        -- use the decomposition `t = 8*(t/8) + 4` without `simp` (can loop)
        rw [ht_eq]
        exact dvd_add h4a h44
      exact (_ht4 h4).elim
    · -- 5
      -- TODO: prove the `t % 8 = 5` case.
      sorry
    · -- 6
      -- TODO: prove the `t % 8 = 6` case.
      sorry
    · -- 7 (contradicts ht7)
      exact (ht7_ne (by simpa using hmod)).elim

end Covolume
