import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Descent Valuation Argument

This experiment formalizes the core valuation argument for Ankeny's descent:
If p is a prime factor of n - x^2 with odd multiplicity and p ≡ 3 mod 4,
then we derive a contradiction.
-/

namespace Covolume.Experiments

open Nat

lemma valuation_argument (n q : ℕ) (x y z : ℤ) (p : ℕ) [hp : Fact p.Prime]
    (hp_mod3 : p % 4 = 3)
    (hn_sqfree : Squarefree n)
    (h_ankeny : 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q)
    (hq_mod : (2 * q : ZMod n) = -1)
    (hp_dvd_K : (p : ℤ) ∣ (n - x^2)) :
    False := by
  -- 1. p cannot be 2 (since p ≡ 3 mod 4)
  have hp_odd : p % 2 = 1 := by
    have : p % 4 = 3 := hp_mod3
    omega
  
  -- 2. Rearrange Ankeny equation
  have h_eq : y^2 + n * z^2 = 2 * q * (n - x^2) := by
    calc y^2 + n * z^2 = (2 * q * x^2 + y^2 + n * z^2) - 2 * q * x^2 := by ring
      _ = 2 * n * q - 2 * q * x^2 := by rw [h_ankeny]
      _ = 2 * q * (n - x^2) := by ring

  -- 3. Modulo p analysis
  have h_sum_zero : (y^2 + n * z^2 : ZMod p) = 0 := by
    have : (y^2 + n * z^2 : ℤ) ≡ 0 [ZMOD p] := by
      rw [h_eq]
      apply Int.ModEq.mul_left
      exact Int.modEq_zero_iff_dvd.mpr hp_dvd_K
    exact (ZMod.intCast_eq_intCast_iff _ _ p).mpr this

  -- Case analysis on p | n
  by_cases hpn : p ∣ n
  · -- If p | n, then y^2 ≡ 0 (mod p) => p | y
    have hy : (y : ZMod p) = 0 := by
      rw [hpn.cast_zmod_eq_zero] at h_sum_zero
      simp at h_sum_zero
      exact h_sum_zero.power_zero (by decide)
    
    -- Since n is squarefree, v_p(n) = 1.
    -- Since p | (n - x^2) and p | n, we have p | x^2, so p | x.
    have hx : (x : ZMod p) = 0 := by
      have : (x^2 : ZMod p) = (n : ZMod p) - ((n - x^2) : ℤ) := by
        push_cast; ring
      rw [hpn.cast_zmod_eq_zero] at this
      have : ((n - x^2) : ZMod p) = 0 := by
        exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hp_dvd_K
      rw [this] at this
      simp at this
      exact this.power_zero (by decide)

    -- Now we need to divide by p.
    -- This requires moving to integers and using v_p(n)=1.
    sorry

  · -- If p ∤ n, then n is a unit mod p.
    -- n ≡ x^2 (mod p) from p | n-x^2.
    have hn_sq : (n : ZMod p) = (x : ZMod p)^2 := by
      have : ((n - x^2) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hp_dvd_K
      push_cast at this
      rw [sub_eq_zero] at this
      exact this.symm
    
    rw [hn_sq] at h_sum_zero
    -- y^2 + x^2 z^2 ≡ 0 (mod p)
    -- (y/x)^2 + z^2 ≡ 0 (mod p) if x != 0
    -- If x ≡ 0 (mod p), then n ≡ 0 (mod p), contradiction to p ∤ n.
    have hx_nz : (x : ZMod p) ≠ 0 := by
      intro h
      rw [h, zero_pow (by decide)] at hn_sq
      exact hpn ((ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp hn_sq.symm)
    
    -- If z ≡ 0 (mod p), then y ≡ 0 (mod p).
    -- Then p^2 divides LHS = 2q(n-x^2).
    -- If v_p(n-x^2) = 1, then p^2 | 2q(n-x^2) is impossible if p != 2, p != q.
    sorry

end Covolume.Experiments
