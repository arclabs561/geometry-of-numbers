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

/-- In ZMod p where p ≡ 3 mod 4, x^2 + y^2 = 0 implies x = 0 and y = 0. -/
lemma sq_add_sq_eq_zero_iff_three_mod_four (p : ℕ) [hp : Fact p.Prime] (hp_mod : p % 4 = 3)
    (x y : ZMod p) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    by_cases hy : y = 0
    · subst hy; simp at h; exact ⟨pow_eq_zero h, rfl⟩
    · -- If y != 0, then (x/y)^2 = -1
      have : IsUnit y := (ZMod.isUnit_iff_ne_zero y).mpr hy
      let z := x * (this.unit)⁻¹
      have hz : z^2 = -1 := by
        calc z^2 = x^2 * ((this.unit)⁻¹ : ZMod p)^2 := by ring
          _ = (-y^2) * (y⁻¹)^2 := by rw [← add_eq_zero_iff_eq_neg.mp h]; simp
          _ = -(y^2 * (y⁻¹)^2) := by ring
          _ = -1 := by simp [hy]
      -- Contradiction: -1 is not a square mod p ≡ 3 mod 4
      have h_sq : ∃ w : ZMod p, w^2 = -1 := ⟨z, hz⟩
      rw [ZMod.exists_sq_eq_neg_one_iff] at h_sq
      have p_ne_2 : p ≠ 2 := by
        intro hp2; rw [hp2] at hp_mod; contradiction
      simp [p_ne_2, hp_mod] at h_sq
  · rintro ⟨rfl, rfl⟩; simp

lemma valuation_argument (n q : ℕ) (x y z : ℤ) (p : ℕ) [hp : Fact p.Prime]
    (hp_mod3 : p % 4 = 3)
    (hn_sqfree : Squarefree n)
    (h_ankeny : 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q)
    (hp_dvd_K : (p : ℤ) ∣ (n - x^2)) :
    (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
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
    have hy_zero : (y : ZMod p) = 0 := by
      have : (n : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mpr (Int.natCast_dvd_natCast.mpr hpn)
      rw [this] at h_sum_zero
      simp at h_sum_zero
      exact h_sum_zero.power_zero (by decide)
    
    -- Since n is squarefree, v_p(n) = 1.
    -- Since p | (n - x^2) and p | n, we have p | x^2, so p | x.
    have hx_zero : (x : ZMod p) = 0 := by
      have : (x^2 : ZMod p) = (n : ZMod p) - ((n - x^2) : ℤ) := by push_cast; ring
      have : (n : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd n p).mpr (Int.natCast_dvd_natCast.mpr hpn)
      rw [this] at this
      have : ((n - x^2) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hp_dvd_K
      rw [this] at this
      simp at this
      exact this.power_zero (by decide)

    -- Move back to integers
    have hy_dvd : (p : ℤ) ∣ y := (ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp hy_zero
    have hx_dvd : (p : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx_zero
    
    -- Let x = p*x1, y = p*y1, n = p*n1.
    obtain ⟨x1, hx1⟩ := hx_dvd
    obtain ⟨y1, hy1⟩ := hy_dvd
    obtain ⟨n1, hn1⟩ := Int.natCast_dvd_natCast.mpr hpn
    
    -- Equation: p^2 y1^2 + p n1 z^2 = 2q(p n1 - p^2 x1^2)
    -- Divide by p: p y1^2 + n1 z^2 = 2q(n1 - p x1^2)
    -- Modulo p: n1 z^2 ≡ 2q n1 (mod p)
    -- Since n is squarefree, p doesn't divide n1.
    -- So z^2 ≡ 2q (mod p).
    -- This part is not needed for the ∧ z result if we assume p | z.
    -- Wait, if p | n, we don't necessarily get p | z from this.
    -- But in Ankeny's proof, we chose q such that (-2q/p) = -1? No.
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
    have h_sq_sum : (y : ZMod p)^2 + ((x : ZMod p) * (z : ZMod p))^2 = 0 := by
      rw [mul_pow]; exact h_sum_zero
    
    -- If p ≡ 3 (mod 4), then a^2 + b^2 ≡ 0 mod p implies a ≡ 0, b ≡ 0.
    have h_zero : (y : ZMod p) = 0 ∧ ((x : ZMod p) * (z : ZMod p)) = 0 := by
      apply (sq_add_sq_eq_zero_iff_three_mod_four p hp_mod3 _ _).mp h_sq_sum
    
    have hy_zero : (y : ZMod p) = 0 := h_zero.left
    have hxz_zero : (x : ZMod p) * (z : ZMod p) = 0 := h_zero.right
    
    -- x is not zero mod p because p ∤ n and n ≡ x^2.
    have hx_nz : (x : ZMod p) ≠ 0 := by
      intro h
      rw [h, zero_pow (by decide)] at hn_sq
      have : (n : ZMod p) = 0 := hn_sq
      exact hpn ((ZMod.intCast_zmod_eq_zero_iff_dvd n p).mp this)
    
    have hz_zero : (z : ZMod p) = 0 := by
      exact (mul_eq_zero.mp hxz_zero).resolve_left hx_nz
    
    -- Thus p | y and p | z.
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp hy_zero,
           (ZMod.intCast_zmod_eq_zero_iff_dvd z p).mp hz_zero⟩

end Covolume.Experiments
