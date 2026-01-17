import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace Covolume

/-!
# Modular “two squares + one” solvability

Several Minkowski/Ankeny-style proofs need the local congruence condition

```text
u^2 + v^2 + 1 ≡ 0  [ZMOD n]
```

for odd `n`. In the descent-lattice approach (`Legendre/Minkowski.lean`) this condition ensures that
any lattice point has norm square divisible by `n`.

This file collects helper lemmas that produce such `u, v` in easy cases (primes)
and prime powers.
-/

/-- Prime modulus case: for a prime `p`, there exist `u, v : ZMod p` with `u^2 + v^2 + 1 = 0`. -/
theorem exists_sq_add_sq_add_one_eq_zero_mod_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ u v : ZMod p, u^2 + v^2 + 1 = 0 := by
  -- Utilizes Nat.sq_add_sq_zmodEq from Mathlib
  obtain ⟨a, b, _, _, hab⟩ := Nat.sq_add_sq_zmodEq p (-1)
  use (a : ZMod p), (b : ZMod p)
  have hZ : ((a ^ 2 + b ^ 2 : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) := by
    exact (ZMod.intCast_eq_intCast_iff (a ^ 2 + b ^ 2 : ℤ) (-1) p).2 hab
  have : (a ^ 2 + b ^ 2 : ZMod p) = (-1 : ZMod p) := by
    simpa using hZ
  linear_combination this

/-- One-step lifting lemma (Hensel-style) for the congruence
\[
u^2 + v^2 + 1 \equiv 0 \pmod{p^k}.
\]

If `p` is an odd prime and `p ∤ u`, we can adjust `u` by a multiple of `p^k` to lift a solution
from modulus `p^k` to `p^(k+1)`. -/
private lemma hensel_lift_two_squares_one_step
    (p k : ℕ) [Fact p.Prime] (hp_odd : p % 2 = 1)
    (u v : ℤ)
    (hk : 1 ≤ k)
    (hu : ¬ (p : ℤ) ∣ u)
    (h0 : u ^ 2 + v ^ 2 + 1 ≡ 0 [ZMOD (p ^ k)]) :
    ∃ u' : ℤ, u' ^ 2 + v ^ 2 + 1 ≡ 0 [ZMOD (p ^ (k + 1))] ∧ u' ≡ u [ZMOD (p ^ k)] := by
  -- Notation.
  let pk : ℤ := p ^ k
  -- Turn the congruence into a divisibility statement.
  have h_dvd : pk ∣ u ^ 2 + v ^ 2 + 1 := by
    simpa [pk] using (Int.modEq_zero_iff_dvd.mp h0)
  rcases h_dvd with ⟨m, hm⟩

  -- Work in `ZMod p` to choose the correction factor `x`.
  let mZ : ZMod p := m
  let uZ : ZMod p := u
  let a : ZMod p := 2 * uZ
  have ha_ne0 : a ≠ 0 := by
    have h2_ne0 : (2 : ZMod p) ≠ 0 := by
      intro h0
      have hp_dvd_two_z : (p : ℤ) ∣ (2 : ℤ) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).1 (by simpa using h0)
      have hp_dvd_two : p ∣ 2 := Int.natCast_dvd_natCast.mp (by simpa using hp_dvd_two_z)
      have hp_ne2 : p ≠ 2 := by
        intro hp2; subst hp2; simpa using hp_odd
      have : p = 2 :=
        (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).1 hp_dvd_two
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
  · -- Lifted congruence mod `p^(k+1)`.
    have h_expand :
        u' ^ 2 + v ^ 2 + 1 = pk * (m + u * (x * 2) + pk * x ^ 2) := by
      have : u' ^ 2 + v ^ 2 + 1
            = (u ^ 2 + v ^ 2 + 1) + 2 * u * x * pk + x ^ 2 * pk ^ 2 := by
        simp [u', pow_two]
        ring
      calc
        u' ^ 2 + v ^ 2 + 1
            = (u ^ 2 + v ^ 2 + 1) + 2 * u * x * pk + x ^ 2 * pk ^ 2 := this
        _ = (pk * m) + 2 * u * x * pk + x ^ 2 * pk ^ 2 := by simpa [hm]
        _ = pk * (m + u * (x * 2) + pk * x ^ 2) := by ring_nf

    have hp_dvd_pk : (p : ℤ) ∣ pk := by
      have hk0 : k ≠ 0 := Nat.ne_of_gt hk
      rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨k0, rfl⟩
      simpa [pk] using (dvd_pow_self (p : ℤ) (Nat.succ_ne_zero k0))
    have hp_dvd_tail : (p : ℤ) ∣ (x ^ 2 * pk) :=
      dvd_mul_of_dvd_right hp_dvd_pk (x ^ 2)

    have hp_dvd_lin : (p : ℤ) ∣ (m + u * (x * 2)) := by
      have hx' : (x : ZMod p) = xZ := by simpa using hx
      have hZ0 : ((m + u * (x * 2) : ℤ) : ZMod p) = 0 := by
        calc
          ((m + u * (x * 2) : ℤ) : ZMod p)
              = (mZ + a * (x : ZMod p)) := by
                    simp [mZ, uZ, a, two_mul, add_assoc, add_left_comm, add_comm,
                      mul_assoc, mul_left_comm, mul_comm]
          _ = (mZ + a * xZ) := by simp [hx']
          _ = (mZ + a * (-mZ * a⁻¹)) := by simp [xZ]
          _ = (mZ - a * mZ * a⁻¹) := by ring
          _ = (mZ - mZ) := by
                simp [mul_assoc, mul_left_comm, mul_comm, mul_inv_cancel₀ ha_ne0]
          _ = 0 := by simp
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (m + u * (x * 2) : ℤ) p).1 hZ0

    have hp_dvd_big : (p : ℤ) ∣ (m + u * (x * 2) + pk * x ^ 2) := by
      -- `p ∣ x^2*pk` implies `p ∣ pk*x^2`.
      have hp_dvd_tail' : (p : ℤ) ∣ (pk * x ^ 2) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hp_dvd_tail
      -- `m + u*(x*2) + pk*x^2 = (m + u*(x*2)) + pk*x^2`
      simpa [add_assoc] using (dvd_add hp_dvd_lin hp_dvd_tail')

    have hp_pow_dvd : ((p : ℤ) ^ (k + 1)) ∣ (u' ^ 2 + v ^ 2 + 1) := by
      rcases hp_dvd_big with ⟨r, hr⟩
      have : u' ^ 2 + v ^ 2 + 1 = pk * ((p : ℤ) * r) := by
        simpa [hr, mul_assoc, mul_left_comm, mul_comm] using h_expand
      refine ⟨r, ?_⟩
      simpa [pk, pow_succ, mul_assoc, mul_left_comm, mul_comm] using this

    exact (Int.modEq_zero_iff_dvd).2 hp_pow_dvd
  · -- Congruence mod `p^k` is immediate from the definition of `u'`.
    -- `Int.modEq_iff_dvd` uses `b - a`, so we show `↑(p^k) ∣ u - u'`.
    have : pk ∣ (u - u') := by
      refine ⟨-x, ?_⟩
      -- `u - (u + x*pk) = pk * (-x)`
      simp [u', pk, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
    -- Convert to `Int.ModEq`.
    exact (Int.modEq_iff_dvd).2 this

/-- Solvability modulo prime power `p^k` for odd `p`. -/
lemma exists_sq_add_sq_add_one_eq_zero_mod_prime_pow (p k : ℕ) [hp : Fact p.Prime] (hp_odd : p % 2 = 1) :
    ∃ u v : ℤ, u^2 + v^2 + 1 ≡ 0 [ZMOD (p^k)] := by
  induction k with
  | zero => use 0, 0; simp [Int.ModEq]
  | succ k' ih =>
    obtain ⟨u0, v0, h0⟩ := ih
    rcases k' with _ | k''
    · obtain ⟨u, v, h⟩ := exists_sq_add_sq_add_one_eq_zero_mod_prime p
      use u.val, v.val
      rw [pow_one]
      exact (ZMod.intCast_eq_intCast_iff _ _ p).mp (by simpa using h)

    -- At least one of `u0, v0` is not divisible by `p`.
    have h_not_both_zero : ¬((p : ℤ) ∣ u0 ∧ (p : ℤ) ∣ v0) := by
      intro h
      have h_sum : (p : ℤ) ∣ u0^2 + v0^2 := by
        apply dvd_add
        · exact dvd_pow h.1 (by decide)
        · exact dvd_pow h.2 (by decide)
      have h_one : (p : ℤ) ∣ (u0^2 + v0^2 + 1) - (u0^2 + v0^2) := by
        -- `p` divides the left term since it divides `p^(k''+1)`, which divides `u0^2+v0^2+1`.
        have hp_dvd_pk : (p : ℤ) ∣ (p : ℤ) ^ (k'' + 1) :=
          dvd_pow_self (p : ℤ) (Nat.succ_ne_zero k'')
        have : (p : ℤ) ∣ (u0^2 + v0^2 + 1) := by
          -- `p^(k''+1) ∣ (...)` from `h0`, and `p ∣ p^(k''+1)`.
          have hpkk_dvd : ((p : ℤ) ^ (k'' + 1)) ∣ (u0^2 + v0^2 + 1) := by
            simpa using (Int.modEq_zero_iff_dvd.mp h0)
          exact dvd_trans hp_dvd_pk hpkk_dvd
        apply dvd_sub this h_sum
      simp at h_one
      exact Nat.Prime.not_dvd_one (Fact.out : p.Prime) (Int.natCast_dvd_natCast.mp h_one)

    by_cases hu : ¬((p : ℤ) ∣ u0)
    · -- lift by adjusting `u0`
      have hkpos : 1 ≤ (k'' + 1) := Nat.succ_le_succ (Nat.zero_le k'')
      obtain ⟨u1, hu1, _hu1_congr⟩ :=
        hensel_lift_two_squares_one_step p (k'' + 1) hp_odd u0 v0 hkpos hu (by
          -- restate `h0` with the intended exponent
          simpa [pow_succ] using h0)
      refine ⟨u1, v0, ?_⟩
      simpa [Nat.succ_eq_add_one, add_assoc, add_left_comm, add_comm] using hu1
    · -- lift by adjusting `v0` (symmetry)
      have hv : ¬((p : ℤ) ∣ v0) := by
        intro hv
        apply h_not_both_zero
        classical
        exact ⟨not_not.mp hu, hv⟩
      have hkpos : 1 ≤ (k'' + 1) := Nat.succ_le_succ (Nat.zero_le k'')
      obtain ⟨v1, hv1, _hv1_congr⟩ :=
        hensel_lift_two_squares_one_step p (k'' + 1) hp_odd v0 u0 hkpos hv (by
          simpa [pow_succ, add_comm, add_left_comm, add_assoc] using h0)
      refine ⟨u0, v1, ?_⟩
      -- reorder the symmetric sum
      simpa [add_assoc, add_left_comm, add_comm] using hv1

/-- Odd modulus case: for odd `n`, there exist integers `u, v` such that
`u^2 + v^2 + 1 ≡ 0 [ZMOD n]`. -/
lemma exists_sq_add_sq_add_one_eq_zero_mod_odd (n : ℕ) (hn : Odd n) :
    ∃ u v : ℤ, u^2 + v^2 + 1 ≡ 0 [ZMOD n] := by
  -- For n = 1, (0,0) is a valid solution.
  rcases n with _ | n
  · simp [Odd] at hn
  rcases n with _ | n'
  · use 0, 0; simp [Int.ModEq]
  -- For n > 1, use prime power decomposition and CRT.
  sorry

end Covolume
