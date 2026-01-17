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

This file collects small helper lemmas that produce such `u, v` in easy cases (currently: primes)
and records the intended strategy for odd composite `n` (currently a placeholder).
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
    -- Lift from p^k' to p^{k'+1} using Hensel's lemma logic.
    -- For k'=0, use prime case existence.
    -- For k'>0, at least one of u0, v0 is a unit mod p.
    sorry

/-- Odd modulus case: for odd `n`, there exist integers `u, v` such that
`u^2 + v^2 + 1 ≡ 0 [ZMOD n]`. -/
lemma exists_sq_add_sq_add_one_eq_zero_mod_odd (n : ℕ) (hn : Odd n) :
    ∃ u v : ℤ, u^2 + v^2 + 1 ≡ 0 [ZMOD n] := by
  -- Follows from prime power case via Chinese Remainder Theorem.
  sorry

end Covolume
