import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.Finite.Basic

namespace PolygonalNumberTheorem

/-- For any prime `p`, there exist `u, v` such that `u² + v² + 1 ≡ 0 (mod p)`. -/
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

/-- Every odd integer `n` satisfies the modular root condition. -/
lemma exists_sq_add_sq_add_one_eq_zero_mod_odd (n : ℕ) (hn : Odd n) :
    ∃ u v : ℤ, u^2 + v^2 + 1 ≡ 0 [ZMOD n] := by
  -- 1. True for prime p.
  -- 2. Combine via Chinese Remainder Theorem? Or Hensel's Lemma?
  -- Actually, we can use the fact that for every prime factor p of n,
  -- we have u_p^2 + v^2 + 1 = 0 mod p.
  -- Lifting to powers of p is the hard part.
  sorry

end PolygonalNumberTheorem
