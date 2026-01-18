# Covolume

Lean 4 code around a geometry-of-numbers route to:

- Legendre’s three-square theorem (via Ankeny 1957 + Minkowski)
- Cauchy’s reduction for Fermat’s polygonal number theorem

This library targets the Ankeny–Minkowski pipeline for Legendre's Three-Square Theorem and the Fermat/Cauchy Polygonal Number Theorem.
At present it is a mix of proved lemmas and “scaffold” modules that typecheck but still contain `sorry`.

Dual-licensed under MIT or Apache-2.0.

```sh
# Install Lean + lake (one-time). This repo is pinned by `lean-toolchain`.
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

```
lake build
lake exe status_report
lake exe lint-style
./Scripts/install_git_hooks.sh
```

## Two formulas we use a lot

Three-square “exception” numbers have the form

$$
n = 4^a(8k+7).
$$

Ankeny’s geometric descent is organized around the ternary quadratic form

$$
Q(x,y,z) = 2qx^2 + y^2 + nz^2,
$$

and a Minkowski step on a suitable ellipsoid for a lattice of covolume $2nq$.

## What’s here (roughly)

- `Covolume/Core/`: reusable lemmas/definitions (some files are still scaffolds)
- `Covolume/Legendre/`: the Ankeny proof path and the three-square theorem entry point
- `Covolume/Cauchy/`: the polygonal-number reduction (currently scaffolded)
- `Covolume/Computable/LLL.lean`: LLL scaffold; see also `Experiments/LLLRational.lean`
- `Experiments/`: small probes and scratch files; these are allowed to use `sorry` but must compile

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
For the Cauchy reduction, we rely on the corrected proof from Nathanson’s 1996 book (not the 1987 note), due to a known gap about residue classes.

## References

- Legendre, A. M. (1798). *Essai sur la théorie des nombres*.
- Cauchy, A. L. (1813). *Démonstration du théorème général de Fermat sur les nombres polygones*.
- Ankeny, N. C. (1957). *Sums of three squares*. Proceedings of the American Mathematical Society.
- Nathanson, M. B. (1987). *A short proof of Cauchy's polygonal number theorem*.
- Bhargava, M. (2004). *Higher composition laws*. Annals of Mathematics.
