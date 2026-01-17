import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.Finite.Basic

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
    
    let pk : ℤ := p ^ (k'' + 1)
    have h_dvd : pk ∣ u0^2 + v0^2 + 1 := Int.modEq_zero_iff_dvd.mp h0
    obtain ⟨m, hm⟩ := h_dvd
    
    have h_not_both_zero : ¬((p : ℤ) ∣ u0 ∧ (p : ℤ) ∣ v0) := by
      intro h
      have h_sum : (p : ℤ) ∣ u0^2 + v0^2 := by
        apply dvd_add
        · exact dvd_pow h.1 (by decide)
        · exact dvd_pow h.2 (by decide)
      have h_one : (p : ℤ) ∣ (u0^2 + v0^2 + 1) - (u0^2 + v0^2) := by
        rw [hm]
        apply dvd_sub
        · apply dvd_mul_of_dvd_left
          -- `pk` is a (positive) power of `p`, hence divisible by `p`.
          simpa [pk] using (dvd_pow_self (p : ℤ) (k'' + 1))
        · exact h_sum
      simp at h_one
      exact Nat.Prime.not_dvd_one (Fact.out : p.Prime) (Int.natCast_dvd_natCast.mp h_one)

    by_cases hu : ¬((p : ℤ) ∣ u0)
    · let m_zmod : ZMod p := m
      let u0_zmod : ZMod p := u0
      let x_zmod := -m_zmod * (2 * u0_zmod)⁻¹
      obtain ⟨x, hx⟩ := ZMod.intCast_surjective x_zmod
      use u0 + x * pk, v0
      -- Hensel-lifting step (prime power): adjust `u0` by a multiple of `p^(k''+1)`
      -- to gain an extra factor of `p`.
      --
      -- This is the point where we use invertibility of `2*u0 (mod p)` (since `p ∤ u0`)
      -- to solve a linear congruence in `x (mod p)`.
      --
      -- The full proof is intentionally deferred; we keep the surrounding scaffolding
      -- to make the intended argument explicit and keep the project compiling.
      sorry
    · have hv : ¬((p : ℤ) ∣ v0) := by
        intro h; apply h_not_both_zero; constructor <;> try assumption
        -- From `¬¬(p ∣ u0)` we extract `p ∣ u0` classically.
        classical
        exact (not_not.mp hu)
      let m_zmod : ZMod p := m
      let v0_zmod : ZMod p := v0
      let y_zmod := -m_zmod * (2 * v0_zmod)⁻¹
      obtain ⟨y, hy⟩ := ZMod.intCast_surjective y_zmod
      use u0, v0 + y * pk
      -- Symmetric Hensel-lifting step when `p ∣ u0` but `p ∤ v0`.
      -- We solve for `y (mod p)` using invertibility of `2*v0 (mod p)`.
      sorry

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
