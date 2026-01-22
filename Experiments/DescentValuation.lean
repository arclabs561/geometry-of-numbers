import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import GeometryOfNumbers.Legendre.Ankeny

/-!
# Descent Valuation Argument

This experiment formalizes the core valuation argument for Ankeny's descent:
If p is a prime factor of n - x^2 with odd multiplicity and p ≡ 3 mod 4,
then we derive a contradiction.
-/

namespace GeometryOfNumbers.Experiments

open Nat

/-- In ZMod p where p ≡ 3 mod 4, x^2 + y^2 = 0 implies x = 0 and y = 0. -/
lemma sq_add_sq_eq_zero_iff_three_mod_four (p : ℕ) [hp : Fact p.Prime] (hp_mod : p % 4 = 3)
    (x y : ZMod p) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro hxy
    by_cases hy : y = 0
    · subst hy
      have hx2 : x ^ 2 = 0 := by simpa using hxy
      have hx : x = 0 := by
        -- In a domain, `x^2 = 0` implies `x = 0`.
        exact (sq_eq_zero_iff.mp (by simpa [pow_two] using hx2))
      exact ⟨hx, rfl⟩
    · -- If `y ≠ 0`, then `x^2 = -y^2` exhibits `-1` as a square, forcing `p % 4 ≠ 3`.
      have hy' : y ≠ 0 := by simpa [ne_eq] using hy
      have hx2_neg : x ^ 2 = -y ^ 2 := by
        -- from `x^2 + y^2 = 0` we get `x^2 = -y^2`
        exact eq_neg_of_add_eq_zero_left hxy
      have hp_ne : p % 4 ≠ 3 :=
        ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (p := p) (x := x) (y := y) hy' hx2_neg
      exact False.elim (hp_ne hp_mod)
  · rintro ⟨hx, hy⟩
    subst hx
    subst hy
    simp

lemma valuation_argument (n q : ℕ) (x y z : ℤ) (p : ℕ) [hp : Fact p.Prime]
    (hp_mod3 : p % 4 = 3)
    (K : ℕ)
    (hpK : p ∣ K) (hp_not_dvd_n : ¬ p ∣ n)
    (hK_eq : (K : ℤ) = (n : ℤ) - x ^ 2)
    (h_eqK : y ^ 2 + (n : ℤ) * z ^ 2 = 2 * (q : ℤ) * (K : ℤ)) :
    (p : ℤ) ∣ y ∧ (p : ℤ) ∣ z := by
  -- This experiment is now a thin wrapper around the canonical lemma proved in `Legendre/Ankeny.lean`.
  haveI : Fact p.Prime := hp
  simpa using
    (GeometryOfNumbers.ankeny_p_dvd_yz_of_dvd_K (n := n) (q := q) (K := K) (p := p) (x := x) (y := y) (z := z)
      (hp := hp.1) (hp4 := hp_mod3) (hpK := hpK) (hp_not_dvd_n := hp_not_dvd_n) (hK_eq := hK_eq) (h_eqK := h_eqK))

end GeometryOfNumbers.Experiments
