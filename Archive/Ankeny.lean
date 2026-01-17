import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Ankeny Descent (scratch)

This file is a *copy* of the sibling workspace scratch file `../Covolume/AnkenyDescent.lean`.
We keep it here so the repo contains the whole exploration surface.

Status: not integrated into the main proof. The current recommended path is the Minkowski pivot
in [`Covolume.MinkowskiDescent`], but Ankeny remains a plausible alternative if we
decide to pull in primes-in-AP / Dirichlet infrastructure.
-/

namespace Nat

/--
Ankeny's Descent Lemma: if qx² + y² + mz² = qm, then m is a sum of three squares.

This assumes:
1. m is square-free and m ≢ 7 mod 8
2. q is a prime with q ≡ 1 mod 4
3. -m is a quadratic residue modulo q
-/
theorem ankeny_descent (m q x y z : ℕ) (hm_sqfree : Squarefree m)
    (hq : Nat.Prime q) (hq1 : q % 4 = 1)
    (hsum : q * x ^ 2 + y ^ 2 + m * z ^ 2 = q * m) :
    ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = m := by
  -- Proof:
  -- 1. y² + mz² = q(m - x²)
  -- 2. Let p be a prime dividing y² + mz² an odd number of times.
  -- 3. Show p ≡ 1 mod 4 using quadratic reciprocity and q ≡ 1 mod 4.
  -- 4. By sum of two squares theorem, (y² + mz²)/q is a sum of two squares u² + v².
  -- 5. m - x² = u² + v², so m = x² + u² + v².
  sorry

/-- Dirichlet's Theorem on Arithmetic Progressions.
    For any co-prime integers a and d, there are infinitely many primes q ≡ a (mod d).

    In Ankeny's proof, we find a prime q ≡ -1 (mod 4n) such that the Legendre symbol
    condition is satisfied. -/
theorem existence_of_ankeny_prime (n : ℕ) (hn : n > 0) :
    ∃ q, Nat.Prime q ∧ q ≡ -1 [MOD (4 * n)] ∧ legendreSym (- (n : ℤ)) q = -1 := by
  -- Requires Mathlib's formalization of Dirichlet's theorem.
  sorry

end Nat

