import PolygonalNumberTheorem.Basic
import PolygonalNumberTheorem.SumThreeSquares
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

open Nat Real
open BigOperators

namespace PolygonalNumberTheorem

/-!
Small “interval → integer” lemmas.

These are deliberately separate from the square-root algebra. The goal is to
keep the `floor` / casting story stable and reusable.
-/

/-- If a real interval has length `> 2`, it contains an odd integer. -/
lemma exists_odd_in_interval {L U : ℝ} (hLU : L + 2 < U) :
    ∃ b : ℤ, Odd b ∧ L < (b : ℝ) ∧ (b : ℝ) < U := by
  let k : ℤ := Int.floor L
  let b0 : ℤ := k + 1
  let b1 : ℤ := k + 2
  have hLb0 : L < (b0 : ℝ) := by
    -- `L < ⌊L⌋ + 1`
    simpa [b0, k, Int.cast_add, Int.cast_one] using (Int.lt_floor_add_one L)
  have hb1_le : (b1 : ℝ) ≤ L + 2 := by
    -- `⌊L⌋ ≤ L`, hence `⌊L⌋ + 2 ≤ L + 2`.
    have : (Int.floor L : ℝ) ≤ L := Int.floor_le L
    have : (Int.floor L : ℝ) + 2 ≤ L + 2 := by linarith
    simpa [b1, k, Int.cast_add, Int.cast_one] using this
  have hb1_ltU : (b1 : ℝ) < U := lt_of_le_of_lt hb1_le (by linarith)
  have hb0_ltU : (b0 : ℝ) < U := by
    have : (b0 : ℝ) < (b1 : ℝ) := by
      -- `b0 < b1` in ℤ, then cast
      have : b0 < b1 := by omega
      exact_mod_cast this
    exact lt_trans this hb1_ltU
  -- Choose the odd one among consecutive integers `b0` and `b1`.
  by_cases hb0_odd : Odd b0
  · exact ⟨b0, hb0_odd, hLb0, hb0_ltU⟩
  · -- If `b0` is not odd, then `b0 % 2 = 0`, hence `(b0+1) % 2 = 1` and `b1` is odd.
    have hb0_mod : b0 % 2 = 0 := (Int.not_odd_iff).1 hb0_odd
    have hb1_mod : b1 % 2 = 1 := by
      -- `b1 = b0 + 1`
      have : b1 = b0 + 1 := by omega
      -- compute mod 2
      -- `((b0+1) % 2) = (b0%2 + 1%2) % 2`
      -- and `1 % 2 = 1`
      -- omega can finish this arithmetic.
      omega
    have hb1_odd : Odd b1 := (Int.odd_iff).2 hb1_mod
    have hLb1 : L < (b1 : ℝ) := by
      have : (b0 : ℝ) < (b1 : ℝ) := by
        have : b0 < b1 := by omega
        exact_mod_cast this
      exact lt_trans hLb0 this
    exact ⟨b1, hb1_odd, hLb1, hb1_ltU⟩

/-
Notes / scratchpad (kept as breadcrumbs; not part of the final story yet):

We tried to fill in:
- an explicit `length_gt_two` inequality (interval length > 2) using `Real.sqrt` monotonicity
- a floor-based lemma `exists_odd_in_interval`

Those attempts hit a few recurring problems:
- `sqrt_lt_sqrt_iff` / `sqrt_le_sqrt` lemma shape mismatch (different variants in Mathlib)
- `floor` casting: `Int.lt_floor_add_one` gives `L < (⌊L⌋ : ℝ) + 1`, not `L < ((⌊L⌋+1) : ℝ)` directly
- `sqrt` ambiguity (`Nat.sqrt` vs `Real.sqrt`) if `open Nat Real` is on and literals are not typed

For now we revert these to `sorry` to restore a clean build, and we’ll reintroduce them
in a small isolated file once we’ve identified the exact Mathlib lemmas to use.
-/

/-- Upper bound for `b` in Cauchy's condition. -/
noncomputable def cauchy_b_ub (a : ℝ) : ℝ := Real.sqrt (4 * a)

/-- Lower bound for `b` in Cauchy's condition. -/
noncomputable def cauchy_b_lb (a : ℝ) : ℝ := Real.sqrt (3 * a - 3) - 1

/-- For `a ≥ 3`, the interval `(cauchy_b_lb a, cauchy_b_ub a)` contains an odd integer. -/
lemma exists_odd_in_cauchy_interval (a : ℝ) (ha : 3 ≤ a) :
    ∃ b : ℤ, Odd b ∧ cauchy_b_lb a < (b : ℝ) ∧ (b : ℝ) < cauchy_b_ub a := by
  -- The interval length is `ub - lb = (√(4a) - (√(3a-3)-1)) = √(4a) - √(3a-3) + 1`.
  -- This is strictly > 2 except at `a = 4`, where it equals 2 but still contains `3`.
  by_cases h4 : a = 4
  · subst h4
    refine ⟨3, by decide, ?_, ?_⟩
    · -- `cauchy_b_lb 4 = 2`
      have hsqrt : Real.sqrt (3 * (4 : ℝ) - 3) = (3 : ℝ) := by
        calc
          Real.sqrt (3 * (4 : ℝ) - 3) = Real.sqrt ((3 : ℝ) ^ 2) := by norm_num
          _ = (3 : ℝ) := by simp
      -- goal: `cauchy_b_lb 4 < 3`
      dsimp [cauchy_b_lb]
      -- reduce to `2 < 3`
      simp [hsqrt]
    · -- `cauchy_b_ub 4 = 4`
      have hsqrt : Real.sqrt (4 * (4 : ℝ)) = (4 : ℝ) := by
        calc
          Real.sqrt (4 * (4 : ℝ)) = Real.sqrt ((4 : ℝ) ^ 2) := by norm_num
          _ = (4 : ℝ) := by simp
      dsimp [cauchy_b_ub]
      simp [hsqrt]
      norm_num
  · -- show `lb + 2 < ub`, then use `exists_odd_in_interval`
    have hnonneg1 : 0 ≤ 3 * a - 3 := by nlinarith [ha]
    have hnonneg2 : 0 ≤ 4 * a := by nlinarith [ha]
    have hpos_sq : 0 < (a - 4) ^ 2 := by
      have : a - 4 ≠ 0 := (sub_ne_zero).2 h4
      exact sq_pos_of_ne_zero this
    have hkey : (cauchy_b_lb a) + 2 < cauchy_b_ub a := by
      -- rewrite to `√(3a-3)+1 < √(4a)`
      have hx0 : 0 ≤ Real.sqrt (3 * a - 3) + 1 := by
        nlinarith [Real.sqrt_nonneg (3 * a - 3)]
      -- use `Real.lt_sqrt` to square once: `x < √y ↔ x^2 < y`
      have : (Real.sqrt (3 * a - 3) + 1) ^ 2 < 4 * a := by
        -- reduce to `√(3a-3) < (a+2)/2`, then to `(a-4)^2 > 0`.
        have hy0 : 0 ≤ (a + 2) / 2 := by nlinarith [ha]
        have hpoly : 3 * a - 3 < ((a + 2) / 2) ^ 2 := by
          -- Multiply by 4: `12a-12 < (a+2)^2`, and the difference is `(a-4)^2`.
          have : 12 * a - 12 < (a + 2) ^ 2 := by
            -- `(a+2)^2 - (12a-12) = (a-4)^2`
            have : (a + 2) ^ 2 - (12 * a - 12) = (a - 4) ^ 2 := by ring
            -- turn `0 < (a-4)^2` into the desired inequality
            have : 0 < (a + 2) ^ 2 - (12 * a - 12) := by simpa [this] using hpos_sq
            linarith
          -- divide by 4 (positive)
          nlinarith
        have hsqrt : Real.sqrt (3 * a - 3) < (a + 2) / 2 :=
          (Real.sqrt_lt hnonneg1 hy0).2 hpoly
        have h2sqrt : 2 * Real.sqrt (3 * a - 3) < a + 2 := by nlinarith
        -- expand `(√x+1)^2`
        calc
          (Real.sqrt (3 * a - 3) + 1) ^ 2
              = (Real.sqrt (3 * a - 3)) ^ 2 + 2 * Real.sqrt (3 * a - 3) + 1 := by ring
          _ = (3 * a - 3) + 2 * Real.sqrt (3 * a - 3) + 1 := by
                simp [Real.sq_sqrt hnonneg1]
          _ < (3 * a - 3) + (a + 2) + 1 := by nlinarith
          _ = 4 * a := by ring
      have : Real.sqrt (3 * a - 3) + 1 < Real.sqrt (4 * a) := by
        -- `x < √y` from `x^2 < y`
        exact (Real.lt_sqrt hx0).2 (by simpa using this)
      -- unwrap the `lb`/`ub` without letting `simp` rewrite square roots
      dsimp [cauchy_b_lb, cauchy_b_ub]
      -- goal is `√(3a-3) - 1 + 2 < √(4a)`
      nlinarith [this]
    -- apply the generic lemma with L = lb, U = ub
    simpa [cauchy_b_lb, cauchy_b_ub] using (exists_odd_in_interval (L := cauchy_b_lb a) (U := cauchy_b_ub a) hkey)

/-- For `a ≥ 3`, there exists an odd `b` satisfying Cauchy's conditions. -/
lemma exists_cauchy_b (a : ℤ) (ha : 3 ≤ a) :
    ∃ b : ℤ, 0 < a ∧ 0 < b ∧ Odd b ∧ (b : ℝ) ^ 2 < 4 * (a : ℝ) ∧
      (b : ℝ) ^ 2 + 2 * (b : ℝ) + 4 > 3 * (a : ℝ) := by
  have haR : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have ha_pos : 0 < a := lt_of_lt_of_le (by decide : (0 : ℤ) < 3) ha
  -- Pick `b` from the Cauchy interval on reals.
  obtain ⟨b, hb_odd, hbL, hbU⟩ := exists_odd_in_cauchy_interval (a := (a : ℝ)) haR
  have hx_nonneg : 0 ≤ 3 * (a : ℝ) - 3 := by nlinarith [haR]
  have hbR_pos : (0 : ℝ) < (b : ℝ) := by
    -- `b > cauchy_b_lb a` and `cauchy_b_lb a > 0` for `a ≥ 3`.
    have : (0 : ℝ) < cauchy_b_lb (a : ℝ) := by
      -- `cauchy_b_lb a = √(3a-3) - 1` and `3a-3 ≥ 6`, so `√(3a-3) > 1`.
      have h6 : (6 : ℝ) ≤ 3 * (a : ℝ) - 3 := by nlinarith [haR]
      have : (1 : ℝ) < Real.sqrt (3 * (a : ℝ) - 3) := by
        -- `1 < √y` from `1^2 < y`
        have : (1 : ℝ) ^ 2 < 3 * (a : ℝ) - 3 := by nlinarith [h6]
        exact (Real.lt_sqrt (by nlinarith)).2 (by simpa using this)
      dsimp [cauchy_b_lb]
      nlinarith [this]
    exact lt_trans this hbL
  have hb_pos : 0 < b := by
    exact_mod_cast hbR_pos
  -- Upper inequality: `b < √(4a)` ⇒ `b^2 < 4a`
  have hb_sq_lt : (b : ℝ) ^ 2 < 4 * (a : ℝ) := by
    -- `Real.lt_sqrt` requires `0 ≤ b`
    have hbR_nonneg : (0 : ℝ) ≤ (b : ℝ) := le_of_lt hbR_pos
    have : ((b : ℝ) ^ 2) < 4 * (a : ℝ) := (Real.lt_sqrt hbR_nonneg).1 hbU
    simpa using this
  -- Lower inequality: `√(3a-3) - 1 < b` ⇒ `3a < b^2 + 2b + 4`
  have hb_big : (b : ℝ) ^ 2 + 2 * (b : ℝ) + 4 > 3 * (a : ℝ) := by
    have hb1_nonneg : (0 : ℝ) ≤ (b : ℝ) + 1 := by nlinarith [hbR_pos]
    have hsqrt_lt : Real.sqrt (3 * (a : ℝ) - 3) < (b : ℝ) + 1 := by
      -- from `cauchy_b_lb a < b`, i.e. `√(3a-3) - 1 < b`
      dsimp [cauchy_b_lb] at hbL
      linarith
    have hsq : 3 * (a : ℝ) - 3 < ((b : ℝ) + 1) ^ 2 :=
      (Real.sqrt_lt hx_nonneg hb1_nonneg).1 hsqrt_lt
    -- expand and rearrange
    nlinarith [hsq]
  refine ⟨b, ha_pos, hb_pos, hb_odd, hb_sq_lt, ?_⟩
  simpa [gt_iff_lt] using hb_big

/-- Given N, m, b, r, define the target sum of squares a. -/
def cauchy_a (m N : ℕ) (b : ℤ) (r : ℕ) : ℤ := b + 2 * ((N : ℤ) - b - r) / (m : ℤ)

/-- The set `{b+r | b ∈ {b1, b1+2}, 0 ≤ r ≤ m-2}` covers all residues mod `m` for `m ≥ 4`. -/
lemma residues_covered_m_ge_4 (m : ℕ) (hm : 4 ≤ m) (b1 : ℤ) (x : ℤ) :
    ∃ b ∈ ({b1, b1 + 2} : Set ℤ), ∃ r : ℕ, r ≤ m - 2 ∧ (b + r : ℤ) ≡ x [ZMOD m] := by
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  have hm_ne0_nat : m ≠ 0 := Nat.ne_of_gt hm_pos
  have hm_ne0_int : (m : ℤ) ≠ 0 := by exact_mod_cast hm_ne0_nat
  -- Let `r` be the natural remainder in `[0, m)`.
  let r : ℕ := (x - b1).natMod m
  have hr_lt : r < m := Int.natMod_lt (m := x - b1) hm_ne0_nat
  -- Convert the nat remainder back to the corresponding integer remainder.
  have hr_coe : (r : ℤ) = (x - b1) % (m : ℤ) := by
    -- `r = ((x-b1) % m).toNat` by definition; the integer remainder is nonnegative.
    have hnonneg : 0 ≤ (x - b1) % (m : ℤ) := Int.emod_nonneg _ hm_ne0_int
    -- `Int.ofNat (toNat z) = z` for `z ≥ 0`
    simpa [Int.natMod, r, Int.toNat_of_nonneg hnonneg]
  have hbr : (b1 + r : ℤ) ≡ x [ZMOD m] := by
    -- start from `(x-b1)%m ≡ x-b1`, then add `b1` and rewrite `(r:ℤ)`.
    have h0 : (x - b1) % (m : ℤ) ≡ x - b1 [ZMOD m] := Int.mod_modEq (x - b1) (m : ℤ)
    have h1 : b1 + (x - b1) % (m : ℤ) ≡ b1 + (x - b1) [ZMOD m] :=
      (Int.ModEq.add Int.ModEq.rfl h0)
    -- Now rewrite `((x-b1)%m)` as `(r:ℤ)` and simplify `b1 + (x - b1) = x`.
    simpa [hr_coe, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using h1
  by_cases hr : r ≤ m - 2
  · refine ⟨b1, by simp, r, hr, ?_⟩
    simpa using hbr
  · have hr_eq : r = m - 1 := by omega
    refine ⟨b1 + 2, by simp, m - 3, ?_, ?_⟩
    · omega
    · -- `(b1+2)+(m-3) = b1 + (m-1) = b1 + r`
      have hEq : (b1 + 2 + (m - 3 : ℕ) : ℤ) = b1 + r := by
        rw [hr_eq]
        norm_cast
        omega
      simpa [hEq] using hbr

/-- The set `{b+r | b ∈ {b1, b1+2, b1+4}, 0 ≤ r ≤ 1}` covers all residues mod `3`. -/
lemma residues_covered_m_3 (b1 : ℤ) (x : ℤ) :
    ∃ b ∈ ({b1, b1 + 2, b1 + 4} : Set ℤ), ∃ r : ℕ, r ≤ 3 - 2 ∧ (b + r : ℤ) ≡ x [ZMOD 3] := by
  let r : ℕ := (x - b1).natMod 3
  have hr_lt : r < 3 := Int.natMod_lt (m := x - b1) (by decide : (3 : ℕ) ≠ 0)
  have hr_cases : r = 0 ∨ r = 1 ∨ r = 2 := by omega
  have hm_ne0 : (3 : ℤ) ≠ 0 := by decide
  have hr_coe : (r : ℤ) = (x - b1) % 3 := by
    have hnonneg : 0 ≤ (x - b1) % (3 : ℤ) := Int.emod_nonneg _ hm_ne0
    simpa [Int.natMod, r, Int.toNat_of_nonneg hnonneg]
  have hbr : (b1 + r : ℤ) ≡ x [ZMOD 3] := by
    have h0 : (x - b1) % (3 : ℤ) ≡ x - b1 [ZMOD 3] := Int.mod_modEq (x - b1) (3 : ℤ)
    have h1 : b1 + (x - b1) % (3 : ℤ) ≡ b1 + (x - b1) [ZMOD 3] :=
      (Int.ModEq.add Int.ModEq.rfl h0)
    simpa [hr_coe, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using h1
  rcases hr_cases with h0 | h12
  · -- r = 0
    refine ⟨b1, by simp, 0, by decide, ?_⟩
    simpa [h0] using hbr
  · rcases h12 with h1 | h2
    · -- r = 1
      refine ⟨b1, by simp, 1, by decide, ?_⟩
      simpa [h1] using hbr
    · -- r = 2: choose b = b1+2, r = 0
      refine ⟨b1 + 2, by simp, 0, by decide, ?_⟩
      have hEq : (b1 + 2 : ℤ) = b1 + r := by simpa [h2]
      simpa [hEq] using hbr

/-- Existence of b, r for Cauchy's decomposition. -/
lemma exists_cauchy_b_r (m N : ℕ) (hm : 3 ≤ m) (hN : 108 * m ≤ N) :
    ∃ b r : ℕ, Odd b ∧ r ≤ m - 2 ∧ (N : ℤ) - r ≡ b [ZMOD m] ∧
      ∃ a : ℤ, (b : ℤ) ^ 2 < 4 * a ∧ 3 * a < (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4 ∧
      (m : ℤ) * (a - b) = 2 * ((N : ℤ) - b - r) := by
  sorry

/-- 8n + 3 is never of the form 4^a(8k + 7). -/
lemma not_exception_eight_n_add_three (n : ℕ) :
    ¬ Nat.is_three_square_exception (8 * n + 3) := by
  intro ⟨a, k, heq⟩
  cases a with
  | zero =>
    simp at heq; omega
  | succ a' =>
    have hmod : (8 * n + 3) % 4 = 3 := by omega
    have hpow : 4 ^ (a' + 1) * (8 * k + 7) % 4 = 0 := by
      have : 4 ^ (a' + 1) = 4 * 4 ^ a' := by ring
      rw [this]; simp [Nat.mul_mod]
    rw [heq] at hmod; omega

/-- Helper: For odd `a` and odd `b` with `b² < 4a`, we have `4a - b² ≡ 3 (mod 8)`. -/
lemma four_a_minus_b_sq_mod_eight (a b : ℕ) (ha : Odd a) (hb : Odd b)
    (_hcond : b ^ 2 < 4 * a) : (4 * a - b ^ 2) % 8 = 3 := by
  obtain ⟨k, hak⟩ := ha
  have h4a : (4 * a) % 8 = 4 := by
    -- a = 2*k+1 ⇒ 4a = 8k+4
    rw [hak]
    omega
  have hb2 : b ^ 2 % 8 = 1 := Nat.sq_mod_eight_odd b hb
  -- With `b^2 < 4a`, subtraction is well-defined and omega can close.
  omega

/-- 4a - b² is not of the exception form 4^e(8k+7). -/
lemma four_a_minus_b_sq_not_exception (a b : ℕ) (_ha_pos : 1 ≤ a) (_hb_pos : 1 ≤ b)
    (ha_odd : Odd a) (hb_odd : Odd b) (hcond : b ^ 2 < 4 * a) :
    ¬ Nat.is_three_square_exception (4 * a - b ^ 2) := by
  have hmod3 := four_a_minus_b_sq_mod_eight a b ha_odd hb_odd hcond
  let m := (4 * a - b ^ 2 - 3) / 8
  have heq : 4 * a - b ^ 2 = 8 * m + 3 := by
    have hmod0 : (4 * a - b ^ 2 - 3) % 8 = 0 := by omega
    have hdiv : 8 * m = 4 * a - b ^ 2 - 3 :=
      Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod0)
    omega
  rw [heq]
  exact not_exception_eight_n_add_three m

/-- If n is a sum of three squares, it has a representation with integers x, y, z sorted x ≥ y ≥ z. -/
lemma exists_sorted_three_squares_int (n : ℕ) (h : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) :
    ∃ x y z : ℤ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≥ y ∧ y ≥ z ∧ x ^ 2 + y ^ 2 + z ^ 2 = n := by
  obtain ⟨a, b, c, habc⟩ := h
  have hsym : ∀ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 →
      (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = n := by
    intros x y z hxyz; have : (x ^ 2 + y ^ 2 + z ^ 2 : ℕ) = n := by rw [hxyz, habc]
    exact_mod_cast this
  rcases Nat.le_total a b with hab | hba
  · rcases Nat.le_total b c with hbc | hcb
    · exact ⟨c, b, a, by linarith, by linarith, by linarith, by exact_mod_cast hbc, by exact_mod_cast hab, hsym c b a (by ring)⟩
    · rcases Nat.le_total a c with hac | hca
      · exact ⟨b, c, a, by linarith, by linarith, by linarith, by exact_mod_cast hcb, by exact_mod_cast hac, hsym b c a (by ring)⟩
      · exact ⟨b, a, c, by linarith, by linarith, by linarith, by exact_mod_cast hab, by exact_mod_cast hca, hsym b a c (by ring)⟩
  · rcases Nat.le_total b c with hbc | hcb
    · rcases Nat.le_total a c with hac | hca
      · exact ⟨c, a, b, by linarith, by linarith, by linarith, by exact_mod_cast hac, by exact_mod_cast hba, hsym c a b (by ring)⟩
      · exact ⟨a, c, b, by linarith, by linarith, by linarith, by exact_mod_cast hca, by exact_mod_cast hbc, hsym a c b (by ring)⟩
    · exact ⟨a, b, c, by linarith, by linarith, by linarith, by exact_mod_cast hba, by exact_mod_cast hcb, hsym a b c (by ring)⟩

/-- The Cauchy-Schwarz inequality for three terms in ℤ. -/
lemma three_terms_cauchy_schwarz_int (x y z : ℤ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  have h : 3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 =
           (x - y) ^ 2 + (x - z) ^ 2 + (y - z) ^ 2 := by ring
  have h_pos : (x - y) ^ 2 + (x - z) ^ 2 + (y - z) ^ 2 ≥ 0 := by
    have h1 : (x - y) ^ 2 ≥ 0 := sq_nonneg _; have h2 : (x - z) ^ 2 ≥ 0 := sq_nonneg _; have h3 : (y - z) ^ 2 ≥ 0 := sq_nonneg _
    linarith
  linarith

/-- Modular sign choice for Cauchy’s lemma. -/
lemma choose_u_div_four (b x y z : ℤ) (hb : Odd b) (hx : Odd x) (hy : Odd y) (hz : Odd z) :
    ∃ u : ℤ, (u = z ∨ u = -z) ∧ (4 : ℤ) ∣ (b + x + y + u) := by
  have hsum_odd : Odd (b + x + y) := (hb.add_odd hx).add_odd hy
  have heven_plus : Even (b + x + y + z) := hsum_odd.add_odd hz
  have heven_minus : Even (b + x + y - z) := by rw [sub_eq_add_neg]; exact hsum_odd.add_odd hz.neg
  obtain ⟨k1, hk1⟩ := heven_plus
  by_cases hk1_even : Even k1
  · obtain ⟨m, hm⟩ := hk1_even; use z, Or.inl rfl; rw [hk1, hm]; use m; ring
  · have hk1_odd : Odd k1 := by rwa [← Int.not_even_iff_odd]
    have h_factor : b + x + y - z = 2 * (k1 - z) := by calc b + x + y - z = b + x + y + z - 2 * z := by ring
      _ = 2 * k1 - 2 * z := by rw [hk1]; ring
      _ = 2 * (k1 - z) := by ring
    have : Even (k1 - z) := hk1_odd.sub_odd hz; obtain ⟨m, hm⟩ := this
    use -z, Or.inr rfl; rw [← sub_eq_add_neg, h_factor, hm]; use m; ring

/-- The main Cauchy's Lemma (Nathanson Lemma 1.12). -/
theorem four_nonneg_sum_from_cauchy (a b : ℕ) (ha_pos : 1 ≤ a) (hb_pos : 1 ≤ b)
    (ha_odd : Odd a) (hb_odd : Odd b)
    (hcond1 : b ^ 2 < 4 * a) (hcond2 : 3 * a < b ^ 2 + 2 * b + 4) :
    ∃ s t u v : ℕ, a = s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 ∧ b = s + t + u + v := by
  sorry

/-- Given valid Cauchy conditions, express N in terms of polygonal numbers. -/
theorem cauchy_decomposition (m : ℕ) (hm : 3 ≤ m) (N : ℕ) (hN : 108 * m ≤ N) :
    ∃ p1 p2 p3 p4 : ℕ, ∃ r : ℕ,
      r ≤ m - 2 ∧
      N = polygonal (m + 2) p1 + polygonal (m + 2) p2 +
          polygonal (m + 2) p3 + polygonal (m + 2) p4 + r := by
  sorry

/-- Gauss's Eureka Theorem wrapper. -/
theorem gauss_eureka (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n := by
  sorry

/-- The "small n" case for Fermat's Polygonal Number Theorem. -/
lemma fermat_polygonal_small (s : ℕ) (hs : 3 ≤ s) (n : ℕ) (hn : n < 108 * (s - 2)) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  sorry

/-- Fermat's Polygonal Number Theorem. -/
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  sorry

end PolygonalNumberTheorem
