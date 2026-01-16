import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.LinearCombination

namespace PolygonalNumberTheorem

/-- The number of squares in `ZMod p` for an odd prime `p` is `(p+1)/2`. -/
lemma card_sq_zmod_prime (p : ℕ) [hp : Fact p.Prime] (h_odd : p ≠ 2) :
    Nat.card { x : ZMod p | ∃ y : ZMod p, y ^ 2 = x } = (p + 1) / 2 := by
  sorry

/-- For any prime `p`, there exist `u, v` such that `u² + v² + 1 ≡ 0 (mod p)`. -/
theorem exists_sq_add_sq_add_one_eq_zero_mod_prime (p : ℕ) [hp : Fact p.Prime] :
    ∃ u v : ZMod p, u^2 + v^2 + 1 = 0 := by
  by_cases h2 : p = 2
  · subst h2; use 1, 0; decide
  · -- Pigeonhole principle on squares.
    sorry

end PolygonalNumberTheorem
