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

/-- Prime modulus case: for a prime `p`, there exist `u, v : ZMod p` with `u^2 + v^2 + 1 = 0`.

### Evidence

This is a direct reuse of `Nat.sq_add_sq_zmodEq` from `Mathlib/FieldTheory/Finite/Basic.lean`:
it produces `a, b : ℤ` such that `a^2 + b^2 ≡ -1 [ZMOD p]`, and we transport the statement into
`ZMod p`.

### Why we need this

This is the base case for building solutions modulo an odd `n` by Chinese remainder/lifting.
-/
theorem exists_sq_add_sq_add_one_eq_zero_mod_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ u v : ZMod p, u^2 + v^2 + 1 = 0 := by
  -- Use `Nat.sq_add_sq_zmodEq` from `Mathlib.FieldTheory.Finite.Basic`.
  obtain ⟨a, b, _, _, hab⟩ := Nat.sq_add_sq_zmodEq p (-1)
  use (a : ZMod p), (b : ZMod p)
  -- hab : (a^2 + b^2 : ℤ) ≡ -1 [ZMOD p]
  -- Convert to ZMod p.
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
    sorry

/-- Odd modulus case: for odd `n`, there exist integers `u, v` such that
`u^2 + v^2 + 1 ≡ 0 [ZMOD n]`. -/
lemma exists_sq_add_sq_add_one_eq_zero_mod_odd (n : ℕ) (hn : Odd n) :
    ∃ u v : ℤ, u^2 + v^2 + 1 ≡ 0 [ZMOD n] := by
  sorry

end Covolume
