import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Descent Valuation Argument

This experiment formalizes the core valuation argument for Ankeny's descent:
If p is a prime factor of n - x^2 with odd multiplicity and p ≡ 3 mod 4,
then we derive a contradiction.
-/

namespace Covolume.Experiments

open Nat

/-- In ZMod p where p ≡ 3 mod 4, x^2 + y^2 = 0 implies x = 0 and y = 0. -/
lemma sq_add_sq_eq_zero_iff_three_mod_four (p : ℕ) [hp : Fact p.Prime] (hp_mod : p % 4 = 3)
    (x y : ZMod p) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 := by
  -- TODO: this is a useful “local obstruction” lemma, but the proof here drifted across
  -- mathlib versions (deprecated lemmas and renamed helpers). Keep it as a stable
  -- placeholder until we re-derive it against the pinned `mathlib` revision.
  --
  -- Expected structure:
  -- - if `y ≠ 0`, reduce to `IsSquare (-1)` in `ZMod p`
  -- - use `ZMod.exists_sq_eq_neg_one_iff` and `p % 4 = 3` to contradict
  -- - conclude both `x = 0` and `y = 0`
  sorry

lemma valuation_argument (n q : ℕ) (x y z : ℤ) (p : ℕ) [hp : Fact p.Prime]
    (hp_mod3 : p % 4 = 3)
    (hn_sqfree : Squarefree n)
    (h_ankeny : 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q)
    (hp_dvd_K : (p : ℤ) ∣ (n - x^2)) :
    (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
  -- TODO: this file is meant to isolate the “\(p \equiv 3 \pmod 4\) forces divisibility”
  -- step used in the descent. The current draft proof drifted with API renames and
  -- type-casting details.
  --
  -- We keep the statement and the intended structure here, but defer the proof so the
  -- `Experiments` library remains buildable as a whole.
  sorry

end Covolume.Experiments
