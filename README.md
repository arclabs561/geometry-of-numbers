## Geometry of Numbers (Lean)

Lean 4 formalization around a geometry-of-numbers route to:

- **Legendre’s three-square theorem** (Ankeny 1957 + Minkowski)
- **Cauchy’s reduction** for Fermat’s polygonal number theorem

This repo is a mix of proved lemmas and scaffolds that still contain `sorry`, but the whole project is expected to typecheck.

Dual-licensed under MIT or Apache-2.0.

### Quickstart

Install Lean (one-time; pinned by `lean-toolchain`):

```bash
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
```

Build and run local checks:

```bash
lake build
./Scripts/check.sh pre-commit
./Scripts/check.sh pre-push
```

### Two formulas

Three-square “exception” numbers have the form:

\[
n = 4^a(8k+7).
\]

Ankeny’s descent is organized around the ternary quadratic form:

\[
Q(x,y,z) = 2qx^2 + y^2 + nz^2.
\]

## What’s here (roughly)

- `GeometryOfNumbers.lean`: public import root (curated facade)
- `Covolume/Core/`: reusable lemmas/definitions (some files are still scaffolds)
- `Covolume/Legendre/`: the Ankeny proof path and the three-square theorem entry point
- `Covolume/Cauchy/`: the polygonal-number reduction (currently scaffolded)
- `Covolume/Computable/LLL.lean`: LLL scaffold; see also `Experiments/LLLRational.lean`
- `Experiments/`: small probes and scratch files; these are allowed to use `sorry` but must compile

### Tooling

`./Scripts/check.sh pre-commit` runs `lake exe gon_checks` + lint-style. If a sibling checkout of `../proofloops`
exists, it also runs a bounded “review-diff” step via the Rust helper CLI (non-blocking unless strict).

Controls:
- `GON_LLM_REVIEW=0` disables the review step
- `GON_LLM_REVIEW_STRICT=1` makes “no reviewer available” / “review failed” fail the check

## Structure

```
Covolume/
  Core/
    Basic.lean            -- Polygonal number definitions and identities.
    QuadraticLattice.lean -- Quadratic forms ↔ lattices (scaffold).
    SuccessiveMinima.lean -- Lattice spectral theory.
    Composition.lean      -- Composition-law scaffolding.
    ModularSquares.lean   -- Local solvability conditions.
    Determinant.lean      -- Lattice determinant and covolume links.
  Computable/
    LLL.lean              -- LLL scaffold.
  Legendre/
    AnkenyLemmas.lean     -- Squarefree decomposition and mod-8 logic.
    Ankeny.lean           -- Ankeny (1957) descent proof.
    Main.lean             -- Legendre's Three-Square Theorem entry point.
  Cauchy/
    Main.lean             -- Cauchy Lemma and Fermat Polygonal Theorem reduction.

Scripts/
  StatusReport.lean          -- Project status summary generator.

Experiments/
  CheckZMod.lean             -- Congruence bridge validation.
  AnkenyCheck.lean           -- Ankeny prime existence probes.
  ankeny_check.py            -- Numeric validation for Ankeny reduction.
  LLLBasic.lean              -- LLL step and Gram-Schmidt probing.
  SuccessiveMinimaBasic.lean -- Spectral theory validation on Z2.
  BhargavaCubes.lean         -- Discriminant invariant checks.
  DescentValuation.lean      -- Valuation contradiction formalization.
```

## Entry points (some are scaffolds)

**Legendre's Three-Square Theorem** (target):
```lean
theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ is_three_square_exception n
```

**Gauss's Triangular Number Theorem** (target):
```lean
theorem gauss_triangular (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n
```

**Fermat's Polygonal Number Theorem** (target):
```lean
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n
```

## Note: Nathanson (1987)
For the `s ≥ 5` case, we target the Cauchy/Nathanson reduction in the “four terms + residue” form
\(n = \sum_{i=1}^4 P(s,x_i) + r\) with \(0 \le r \le s-4\), then pad with `0/1` polygonals.

There is a known residue-class gap in some short presentations; we are following the modern
streamlined route (e.g. Nathanson’s book treatment / the Whitty talk notes) rather than relying on
an unverified modulo argument.

## References

- Legendre, A. M. (1798). *Essai sur la théorie des nombres*.
- Cauchy, A. L. (1813). *Démonstration du théorème général de Fermat sur les nombres polygones*.
- Ankeny, N. C. (1957). *Sums of three squares*. Proceedings of the American Mathematical Society.
- Nathanson, M. B. (1987). *A short proof of Cauchy's polygonal number theorem*.
- Bhargava, M. (2004). *Higher composition laws*. Annals of Mathematics.
