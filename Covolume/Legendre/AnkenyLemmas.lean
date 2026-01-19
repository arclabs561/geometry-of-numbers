import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

namespace Covolume

/-- gcd(4, n) = 1 for odd n. -/
lemma coprime_four_n (n : ℕ) (hn : n % 2 = 1) : Nat.Coprime 4 n := by
  have h2 : Nat.Coprime 2 n := by
    apply (Nat.prime_two.coprime_iff_not_dvd).mpr
    intro h
    have : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    rw [hn] at this
    contradiction
  show Nat.Coprime (2^2) n
  apply Nat.Coprime.pow_left 2 h2

/-- 2 is invertible modulo any odd n. -/
lemma isUnit_two_zmod (n : ℕ) (hn : n % 2 = 1) : IsUnit (2 : ZMod n) := by
  apply (ZMod.isUnit_iff_coprime 2 n).mpr
  apply (Nat.prime_two.coprime_iff_not_dvd).mpr
  intro h
  have : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  rw [hn] at this
  contradiction

/-- Every `n` can be written as `s^2 * m` where `m` is squarefree. -/
lemma exists_squarefree_part (n : ℕ) :
    ∃ s m : ℕ, n = s^2 * m ∧ Squarefree m := by
  obtain ⟨m, s, h_eq, h_sq⟩ := Nat.sq_mul_squarefree n
  use s, m
  constructor
  · rw [h_eq]
  · exact h_sq

/-- If `n ≡ 3 (mod 8)`, then its squarefree part `m` satisfies `m ≡ 3 (mod 8)`. -/
lemma squarefree_part_mod_eight (n s m : ℕ) (heq : n = s^2 * m) (hn : n % 8 = 3) :
    m % 8 = 3 := by
  have hs_odd : s % 2 = 1 := by
    by_contra h_even
    have h2s : 2 ∣ s := Nat.dvd_iff_mod_eq_zero.mpr (Nat.mod_two_ne_one.mp h_even)
    have h4s2 : 4 ∣ s^2 := by
      obtain ⟨k, rfl⟩ := h2s
      use k^2; ring
    have h4n : 4 ∣ n := by
      rw [heq]
      exact dvd_mul_of_dvd_left h4s2 m
    have hn4_zero : n % 4 = 0 := Nat.mod_eq_zero_of_dvd h4n
    have hn4_three : n % 4 = 3 % 4 := by
      rw [← Nat.mod_mod_of_dvd n (by decide : 4 ∣ 8), hn]
    rw [hn4_zero] at hn4_three
    norm_num at hn4_three

  have hs_sq_mod : s^2 % 8 = 1 := by
    have h_cases : s % 8 = 1 ∨ s % 8 = 3 ∨ s % 8 = 5 ∨ s % 8 = 7 := by
      -- If `s` is odd, then `s % 8` cannot be even, hence must be in {1,3,5,7}.
      -- The key identity is `(s % 8) % 2 = s % 2` (since `2 ∣ 8`).
      have h2 : (s % 8) % 2 = s % 2 := Nat.mod_mod_of_dvd s (by decide : 2 ∣ 8)
      rw [hs_odd] at h2
      match h8 : s % 8 with
      | 1 => left; rfl
      | 3 => right; left; rfl
      | 5 => right; right; left; rfl
      | 7 => right; right; right; rfl
      | 0|2|4|6 =>
        rw [h8] at h2
        contradiction
      | _ =>
        have : s % 8 < 8 := Nat.mod_lt s (by decide)
        omega
    rcases h_cases with h1 | h3 | h5 | h7
    · simp [Nat.pow_mod, h1]
    · simp [Nat.pow_mod, h3]
    · simp [Nat.pow_mod, h5]
    · simp [Nat.pow_mod, h7]

  have h_mod : n % 8 = (s^2 % 8 * (m % 8)) % 8 := by
    rw [heq, Nat.mul_mod]
  rw [hn, hs_sq_mod, one_mul] at h_mod
  exact (Nat.mod_mod m 8).symm.trans h_mod.symm

/-- Scaling lemma: if `m` is a sum of three squares, then so is `s^2 * m`. -/
lemma sum_three_squares_mul_sq (s m : ℕ)
    (hm : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = m) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = s ^ 2 * m := by
  rcases hm with ⟨x, y, z, hxyz⟩
  refine ⟨s * x, s * y, s * z, ?_⟩
  -- Expand squares and factor `s^2`.
  have hxy :
      s ^ 2 * x ^ 2 + s ^ 2 * y ^ 2 = s ^ 2 * (x ^ 2 + y ^ 2) := by
    simpa [Nat.mul_add] using (Nat.mul_add (s ^ 2) (x ^ 2) (y ^ 2)).symm
  have hxyz' :
      s ^ 2 * (x ^ 2 + y ^ 2) + s ^ 2 * z ^ 2 = s ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    simpa [Nat.add_assoc, Nat.mul_add] using
      (Nat.mul_add (s ^ 2) (x ^ 2 + y ^ 2) (z ^ 2)).symm
  calc
    (s * x) ^ 2 + (s * y) ^ 2 + (s * z) ^ 2
        = s ^ 2 * x ^ 2 + s ^ 2 * y ^ 2 + s ^ 2 * z ^ 2 := by
            simp [mul_pow, pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    _ = s ^ 2 * (x ^ 2 + y ^ 2) + s ^ 2 * z ^ 2 := by
            -- fold the first two terms into `s^2 * (x^2 + y^2)`
            simp [hxy, Nat.add_assoc]
    _ = s ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := hxyz'
    _ = s ^ 2 * m := by simpa [hxyz]

end Covolume
