import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

namespace GeometryOfNumbers
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
        intro hp2
        subst hp2
        simp at hp_odd
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
        _ = (pk * m) + 2 * u * x * pk + x ^ 2 * pk ^ 2 := by simp [hm]
        _ = pk * (m + u * (x * 2) + pk * x ^ 2) := by ring_nf

    have hp_dvd_pk : (p : ℤ) ∣ pk := by
      have hk0 : k ≠ 0 := Nat.ne_of_gt hk
      rcases Nat.exists_eq_succ_of_ne_zero hk0 with ⟨k0, rfl⟩
      simp [pk]
    have hp_dvd_tail : (p : ℤ) ∣ (x ^ 2 * pk) :=
      dvd_mul_of_dvd_right hp_dvd_pk (x ^ 2)

    have hp_dvd_lin : (p : ℤ) ∣ (m + u * (x * 2)) := by
      have hx' : (x : ZMod p) = xZ := by simpa using hx
      have hZ0 : ((m + u * (x * 2) : ℤ) : ZMod p) = 0 := by
        calc
          ((m + u * (x * 2) : ℤ) : ZMod p)
              = (mZ + a * (x : ZMod p)) := by
                    -- normalize multiplication order in `ZMod p`
                    simp [mZ, uZ, a, mul_left_comm, mul_comm]
          _ = (mZ + a * xZ) := by simp [hx']
          _ = (mZ + a * (-mZ * a⁻¹)) := by simp [xZ]
          _ = (mZ - a * mZ * a⁻¹) := by ring
          _ = (mZ - mZ) := by
                have : a * mZ * a⁻¹ = mZ := by
                  calc
                    a * mZ * a⁻¹ = mZ * (a * a⁻¹) := by ring
                    _ = mZ * 1 := by simp [mul_inv_cancel₀ ha_ne0]
                    _ = mZ := by simp
                simp [this]
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
      simp [u', pk, sub_eq_add_neg]
      ring
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
  classical
  cases n with
  | zero =>
      -- `Odd 0` is impossible.
      simp [Odd] at hn
  | succ n =>
      -- Work in `ZMod (n+1)` and use the CRT ring equivalence
      -- `ZMod (n+1) ≃ Π p : (n+1).primeFactors, ZMod (p^(v_p(n+1)))`.
      let N : ℕ := Nat.succ n
      have hNodd : Odd N := by simpa [N] using hn
      have hN0 : N ≠ 0 := by simp [N]

      let e := ZMod.equivPi (n := N) hN0

      -- For each prime-power component, build a solution using `exists_sq_add_sq_add_one_eq_zero_mod_prime_pow`.
      have hcomp :
          ∀ p : N.primeFactors,
            ∃ u v : ZMod ((p : ℕ) ^ (N.factorization p)), u ^ 2 + v ^ 2 + 1 = 0 := by
        intro p
        have hp_prime : Nat.Prime (p : ℕ) := Nat.prime_of_mem_primeFactors p.property
        have hp_dvd : (p : ℕ) ∣ N := Nat.dvd_of_mem_primeFactors p.property
        have hp_ne2 : (p : ℕ) ≠ 2 := by
          intro hp2
          have h2dvd : 2 ∣ N := by simpa [hp2] using hp_dvd
          have hmod1 : N % 2 = 1 := Nat.odd_iff.1 hNodd
          have hmod0 : N % 2 = 0 := Nat.mod_eq_zero_of_dvd h2dvd
          simp [hmod0] at hmod1
        have hp_odd : (p : ℕ) % 2 = 1 := hp_prime.eq_two_or_odd.resolve_left hp_ne2
        haveI : Fact (Nat.Prime (p : ℕ)) := ⟨hp_prime⟩
        -- Use the prime-power lemma to get integer witnesses, then cast into `ZMod`.
        obtain ⟨uI, vI, huvI⟩ :=
          exists_sq_add_sq_add_one_eq_zero_mod_prime_pow (p := (p : ℕ)) (k := N.factorization p) hp_odd
        refine ⟨(uI : ZMod ((p : ℕ) ^ (N.factorization p))),
          (vI : ZMod ((p : ℕ) ^ (N.factorization p))), ?_⟩
        -- Convert `Int.ModEq` into equality in `ZMod`.
        have hZ :
            ((uI ^ 2 + vI ^ 2 + 1 : ℤ) : ZMod ((p : ℕ) ^ (N.factorization p))) = (0 : ZMod ((p : ℕ) ^ (N.factorization p))) := by
          simpa using
            (ZMod.intCast_eq_intCast_iff (uI ^ 2 + vI ^ 2 + 1 : ℤ) 0 ((p : ℕ) ^ (N.factorization p))).2 huvI
        -- Normalize casts.
        simpa [pow_two, Int.cast_add, Int.cast_mul, Int.cast_one] using hZ

      classical
      choose uC vC huvC using hcomp

      let uZ : ZMod N := e.symm uC
      let vZ : ZMod N := e.symm vC

      have huvZ : uZ ^ 2 + vZ ^ 2 + 1 = 0 := by
        -- Prove the equality by applying the ring equivalence and checking componentwise.
        apply e.injective
        ext p
        -- `e (e.symm x) = x`.
        simp [uZ, vZ, huvC]

      -- Lift `uZ, vZ` back to integers and convert the equality to `Int.ModEq`.
      rcases ZMod.intCast_surjective uZ with ⟨uI, huI⟩
      rcases ZMod.intCast_surjective vZ with ⟨vI, hvI⟩
      refine ⟨uI, vI, ?_⟩
      have hZ : ((uI ^ 2 + vI ^ 2 + 1 : ℤ) : ZMod N) = 0 := by
        -- Replace by `uZ, vZ` via the chosen representatives.
        have : ((uI : ZMod N) ^ 2 + (vI : ZMod N) ^ 2 + 1) = 0 := by
          simpa [huI, hvI, pow_two] using huvZ
        -- Turn it into a statement about the cast of the integer expression.
        simpa [pow_two, Int.cast_add, Int.cast_mul, Int.cast_one] using this
      have hdvd : (N : ℤ) ∣ (uI ^ 2 + vI ^ 2 + 1) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (uI ^ 2 + vI ^ 2 + 1 : ℤ) N).1 hZ
      exact (Int.modEq_zero_iff_dvd).2 hdvd

end GeometryOfNumbers