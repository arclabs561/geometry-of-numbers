
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

section AnkenyReduction

variable (n q : ℕ) (x y z : ℤ)

/-- The core reduction lemma for Ankeny's theorem.
    If `y^2 + n*z^2 = 2*q*(n - x^2)` with `q ≡ 1 mod 4`, `n ≡ 3 mod 4`,
    then `n - x^2` is a sum of two squares. -/
lemma ankeny_reduction_step
    (hn_mod4 : n % 4 = 3)
    (hq_prime : Nat.Prime q)
    (hq_mod4 : q % 4 = 1)
    (h_eq : y^2 + n * z^2 = 2 * q * (n - x^2)) :
    ∃ u v : ℤ, n - x^2 = u^2 + v^2 := by
  -- NOTE: This file is an experiment scratchpad. The fully detailed descent proof is
  -- nontrivial and currently lives as a design intent (and partial fragments) across:
  -- - `Covolume/Legendre/Ankeny.lean`
  -- - `Experiments/DescentValuation.lean`
  -- - `doc/TechnicalNotes.md`
  --
  -- Keep the *statement* close at hand, but avoid letting broken intermediate attempts
  -- make the whole `Experiments` library fail to build.
  sorry

end AnkenyReduction
