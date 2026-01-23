import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Ankeny Descent (scratch)

This file is a *copy* of the sibling workspace scratch file `../GeometryOfNumbers/AnkenyDescent.lean`.
We keep it here so the repo contains the whole exploration surface.

Status: not integrated into the main proof. The current recommended path is the Minkowski pivot
in [`GeometryOfNumbers.MinkowskiDescent`], but Ankeny remains a plausible alternative if we
decide to pull in primes-in-AP / Dirichlet infrastructure.

This is an **archive/scratch** file: we intentionally avoid leaving unfinished statements that look
like finished theorems. The intended statements are recorded below as prose only, until we decide
to invest in formalizing them.

## Intended statements (not formalized here yet)

- “Ankeny descent lemma”: from a representation \(q x^2 + y^2 + m z^2 = qm\) (with hypotheses on `m,q`)
  derive that `m` is a sum of three squares.
- “Existence of Ankeny prime”: existence of a prime in a congruence class with a Legendre/Jacobi condition,
  which would rely on Mathlib’s Dirichlet/primes-in-AP infrastructure and some number-theory glue.
-/

