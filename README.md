# Covolume

A Constructive Geometry of Numbers Library for Lean 4.

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
```

## Math (rendered on GitHub)

Three-square “exception” numbers have the form

$$
n = 4^a(8k+7).
$$

Ankeny’s geometric descent is organized around the ternary quadratic form

$$
Q(x,y,z) = 2qx^2 + y^2 + nz^2,
$$

and a Minkowski step on a suitable ellipsoid for a lattice of covolume $2nq$.

## Strategy

The project implements a modular approach to formalizing the geometry of numbers, prioritizing infrastructure over isolated proofs.

### 1. The Systems Kernel
The `QuadraticLattice` bridge connects abstract quadratic forms over integers to geometric submodules in Euclidean space. This interface allows for the resolution of representation problems by encoding local p-adic obstructions into geometric lattice density.

### 2. Successive Minima and Spectral Theory
The library targets the first formalization of **Successive Minima** in Lean 4. These values act as the "spectral lines" of a lattice, providing the fundamental bounds for the Shortest Vector Problem (SVP) and Minkowski's Second Theorem.

### 3. Bhargava Primitives
We include foundational structures for **Bhargava's higher composition laws**, specifically focusing on integer cubes. This establishes a path toward formalizing modern breakthroughs in number field counting and class group structures.

### 4. The Computable Core
The project targets a verified implementation of the Lenstra–Lenstra–Lovász (LLL) lattice reduction algorithm.
The current `Covolume/Computable/LLL.lean` code is a scaffold (with placeholders), and `Experiments/LLLRational.lean` provides a small rational-arithmetic probe.

### 5. Parallel Constructive Track
To address the non-constructive nature of abstract Minkowski theory, the library maintains a parallel track for computable small-case verification.

## Structure

```
Covolume/
  Core/
    Basic.lean            -- Polygonal number definitions and identities.
    QuadraticLattice.lean -- Systems Kernel: Quadratic form to lattice bridge.
    SuccessiveMinima.lean -- Lattice spectral theory.
    Composition.lean      -- Bhargava higher composition primitives.
    ModularSquares.lean   -- Local solvability conditions.
    Determinant.lean      -- Lattice determinant and covolume links.
  Computable/
    LLL.lean              -- Verified LLL implementation.
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

## Key Theorems

**Legendre's Three-Square Theorem**:
```lean
theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ is_three_square_exception n
```

**Gauss's Triangular Number Theorem**:
```lean
theorem gauss_triangular (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n
```

**Fermat's Polygonal Number Theorem**:
```lean
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n
```

## Technical Nuance: The Nathanson Gap
During the formalization of the Cauchy reduction, we identified a known gap in Nathanson's original 1987 paper regarding residue classes. This library targets the corrected proof from Nathanson's 1996 book, ensuring absolute formal rigor.

## References

- Legendre, A. M. (1798). *Essai sur la théorie des nombres*.
- Cauchy, A. L. (1813). *Démonstration du théorème général de Fermat sur les nombres polygones*.
- Ankeny, N. C. (1957). *Sums of three squares*. Proceedings of the American Mathematical Society.
- Nathanson, M. B. (1987). *A short proof of Cauchy's polygonal number theorem*.
- Bhargava, M. (2004). *Higher composition laws*. Annals of Mathematics.
