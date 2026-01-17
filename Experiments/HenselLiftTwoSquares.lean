import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
Scratch space for the prime-power lifting step in `Covolume/Core/ModularSquares.lean`.

Goal: if we have a solution to
\[
u^2 + v^2 + 1 \equiv 0 \pmod{p^k}
\]
with `p` an odd prime and `p ∤ u`, then we can adjust `u` by a multiple of `p^k` to obtain a
solution modulo `p^(k+1)`.

This file is intentionally small: we want the proof to be robust before porting it into the
library file (so we don’t repeatedly break `lake build` while iterating).
-/

namespace Covolume.Experiments

open scoped BigOperators

lemma hensel_lift_two_squares_one_step
    (p k : ℕ) [Fact p.Prime] (hp_odd : p % 2 = 1)
    (u v : ℤ)
    (hk : 1 ≤ k)
    (hu : ¬ (p : ℤ) ∣ u)
    (h0 : u ^ 2 + v ^ 2 + 1 ≡ 0 [ZMOD (p ^ k)]) :
    ∃ u' : ℤ, u' ^ 2 + v ^ 2 + 1 ≡ 0 [ZMOD (p ^ (k + 1))] ∧ u' ≡ u [ZMOD (p ^ k)] := by
  -- Notation.
  let pk : ℤ := p ^ k
  have hpk : (p ^ k : ℤ) = pk := rfl
  -- Turn the congruence into a divisibility statement.
  have h_dvd : pk ∣ u ^ 2 + v ^ 2 + 1 := by
    -- `Int.modEq_zero_iff_dvd` expects an `Int.ModEq ... [ZMOD pk]` statement.
    simpa [pk] using (Int.modEq_zero_iff_dvd.mp h0)
  rcases h_dvd with ⟨m, hm⟩

  -- Work in `ZMod p` to choose the correction factor `x`.
  let mZ : ZMod p := m
  let uZ : ZMod p := u
  let a : ZMod p := 2 * uZ
  have ha_ne0 : a ≠ 0 := by
    -- In the field `ZMod p`, `2*u = 0` implies `2 = 0` or `u = 0`.
    have h2_ne0 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have hp_dvd_two_z : (p : ℤ) ∣ (2 : ℤ) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).1 (by simpa using h0)
      have hp_dvd_two : p ∣ 2 := Int.natCast_dvd_natCast.mp (by simpa using hp_dvd_two_z)
      have hp_ne2 : p ≠ 2 := by
        intro hp2; subst hp2; simpa using hp_odd
      have : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1 hp_dvd_two
      exact hp_ne2 this
    have hu_ne0 : (uZ : ZMod p) ≠ 0 := by
      intro h0
      have hp_dvd_u : (p : ℤ) ∣ u :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (u : ℤ) p).1 (by simpa [uZ] using h0)
      exact hu hp_dvd_u
    exact mul_ne_zero h2_ne0 hu_ne0

  let xZ : ZMod p := -mZ * a⁻¹
  rcases ZMod.intCast_surjective xZ with ⟨x, hx⟩
  let u' : ℤ := u + x * pk

  refine ⟨u', ?_, ?_⟩
  · -- Show the lifted congruence modulo `p^(k+1)`.
    -- TODO: finish in this scratch file before porting into the library.
    sorry
  · -- `u' ≡ u [ZMOD p^k]` is immediate from the definition `u' = u + x*pk`.
    -- (Since `pk` divides the difference.)
    have : u' - u = x * pk := by simp [u']
    have : pk ∣ (u' - u) := by
      refine ⟨x, ?_⟩
      simpa [this]
    -- Convert to `Int.ModEq`.
    exact (Int.modEq_iff_dvd).2 this

end Covolume.Experiments

