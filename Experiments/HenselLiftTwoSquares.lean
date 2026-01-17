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
    -- Expand and factor out `pk`.
    have h_expand :
        u' ^ 2 + v ^ 2 + 1 = pk * (m + 2 * u * x + x ^ 2 * pk) := by
      -- `u' = u + x*pk`
      have : u' ^ 2 + v ^ 2 + 1
            = (u ^ 2 + v ^ 2 + 1) + 2 * u * x * pk + x ^ 2 * pk ^ 2 := by
        simp [u', pow_two]
        ring
      calc
        u' ^ 2 + v ^ 2 + 1
            = (u ^ 2 + v ^ 2 + 1) + 2 * u * x * pk + x ^ 2 * pk ^ 2 := this
        _ = (pk * m) + 2 * u * x * pk + x ^ 2 * pk ^ 2 := by simpa [hm]
        _ = pk * (m + 2 * u * x + x ^ 2 * pk) := by ring_nf

    -- We need `p ∣ (m + 2*u*x + x^2*pk)`. The `x^2*pk` term is divisible by `p` as soon as `k ≥ 1`.
    have hp_dvd_pk : (p : ℤ) ∣ pk := by
      -- `k ≥ 1` implies `pk = p^(k0+1)`.
      have hk0 : k ≠ 0 := Nat.ne_of_gt hk
      rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨k0, rfl⟩
      -- now `pk = (p : ℤ)^(k0+1)`
      simpa [pk] using (dvd_pow_self (p : ℤ) (k0 + 1))
    have hp_dvd_tail : (p : ℤ) ∣ (x ^ 2 * pk) :=
      dvd_mul_of_dvd_right hp_dvd_pk (x ^ 2)

    -- Show `p ∣ (m + 2*u*x)` by construction of `x`.
    have hp_dvd_lin : (p : ℤ) ∣ (m + 2 * u * x) := by
      have hx' : (x : ZMod p) = xZ := by simpa using hx
      have hZ0 : ((m + 2 * u * x : ℤ) : ZMod p) = 0 := by
        -- In `ZMod p`, `m + (2*u)*x = 0` when `x = -m * (2*u)⁻¹`.
        calc
          ((m + 2 * u * x : ℤ) : ZMod p)
              = (mZ + a * (x : ZMod p)) := by
                    -- `simp` handles casting and rewriting `a = 2*uZ`.
                    simp [mZ, uZ, a, two_mul, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
          _ = (mZ + a * xZ) := by simp [hx']
          _ = (mZ + a * (-mZ * a⁻¹)) := by simp [xZ]
          _ = (mZ - a * mZ * a⁻¹) := by ring
          _ = (mZ - mZ) := by
                -- cancel `a * a⁻¹ = 1`
                simp [mul_assoc, mul_left_comm, mul_comm, mul_inv_cancel₀ ha_ne0]
          _ = 0 := by simp
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (m + 2 * u * x : ℤ) p).1 hZ0

    have hp_dvd_big : (p : ℤ) ∣ (m + 2 * u * x + x ^ 2 * pk) :=
      dvd_add hp_dvd_lin hp_dvd_tail

    -- Convert divisibility of the bracket into divisibility by `p^(k+1)` of the whole expression.
    have hp_pow_dvd :
        ((p : ℤ) ^ (k + 1)) ∣ (u' ^ 2 + v ^ 2 + 1) := by
      -- `u'^2+v^2+1 = pk * (...)` and `p ∣ (...)`, while `pk = p^k`.
      rcases hp_dvd_big with ⟨r, hr⟩
      -- rewrite the RHS using `hr`
      have : u' ^ 2 + v ^ 2 + 1 = pk * ((p : ℤ) * r) := by
        simpa [hr, mul_assoc, mul_left_comm, mul_comm] using h_expand
      -- `pk * (p*r) = (p^k) * p * r = p^(k+1) * r`
      refine ⟨r, ?_⟩
      -- Use `pow_succ` and the definitional equality of `pk`.
      -- `pk` is definitionally `(p : ℤ) ^ k`.
      simpa [pk, pow_succ, mul_assoc, mul_left_comm, mul_comm] using this

    exact (Int.modEq_zero_iff_dvd).2 hp_pow_dvd
  · -- `u' ≡ u [ZMOD p^k]` is immediate from the definition `u' = u + x*pk`.
    -- (Since `pk` divides the difference.)
    have : u' - u = x * pk := by simp [u']
    have : pk ∣ (u' - u) := by
      refine ⟨x, ?_⟩
      simpa [this]
    -- Convert to `Int.ModEq`.
    exact (Int.modEq_iff_dvd).2 this

end Covolume.Experiments

