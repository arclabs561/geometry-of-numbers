import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace PolygonalNumberTheorem

/-- gcd(4, n) = 1 for odd n. -/
lemma coprime_four_n (n : ℕ) (hn : n % 2 = 1) : Nat.Coprime 4 n := by
  have h2 : Nat.Coprime 2 n := by
    apply (Nat.prime_two.coprime_iff_not_dvd).mpr
    intro h
    have : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    rw [hn] at this; contradiction
  rw [show 4 = 2^2 by norm_num]
  exact h2.pow_left 2

/-- 2 is invertible modulo any odd n > 1. -/
lemma isUnit_two_zmod (n : ℕ) (hn : n % 2 = 1) : IsUnit (2 : ZMod n) := by
  apply (ZMod.isUnit_iff_coprime 2 n).mpr
  apply (Nat.prime_two.coprime_iff_not_dvd).mpr
  intro h
  have : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  rw [hn] at this; contradiction

end PolygonalNumberTheorem
