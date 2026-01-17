# Covolume

A Constructive Geometry of Numbers Library for Lean 4.

This library formalizes the Ankeny-Minkowski pipeline to prove Legendre's Three-Square Theorem and the Fermat/Cauchy Polygonal Number Theorem. It establishes a framework for lattice systems and geometric number theory within the Lean 4 ecosystem.

Dual-licensed under MIT or Apache-2.0.

```sh
# Install Lean + lake (one-time). This repo is pinned by `lean-toolchain`.
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

```
lake build
lake exe status_report
```

## Strategy

The project implements a modular approach to formalizing the geometry of numbers, prioritizing infrastructure over isolated proofs.

### 1. The Systems Kernel
The `QuadraticLattice` bridge connects abstract quadratic forms over integers to geometric submodules in Euclidean space. This interface allows for the resolution of representation problems by encoding local p-adic obstructions into geometric lattice density.

### 2. Successive Minima and Spectral Theory
The library targets the first formalization of **Successive Minima** in Lean 4. These values act as the "spectral lines" of a lattice, providing the fundamental bounds for the Shortest Vector Problem (SVP).

### 3. Bhargava Primitives
We include foundational structures for **Bhargava's higher composition laws**, specifically focusing on integer cubes. This establishes a path toward formalizing modern breakthroughs in number field counting.

### 4. The Computable Core
The project targets a verified implementation of the Lenstra–Lenstra–Lovász (LLL) lattice reduction algorithm. By bridging abstract measure theory with computable matrix algorithms, the library provides a foundation for verified lattice-based cryptography and optimization.

### 3. Parallel Constructive Track
To address the non-constructive nature of abstract Minkowski theory, the library maintains a parallel track for computable small-case verification.

## Structure

```
Covolume/
  Core/
    Basic.lean            -- Polygonal number definitions and identities.
    QuadraticLattice.lean -- Systems Kernel: Quadratic form to lattice bridge.
    ModularSquares.lean   -- Local solvability conditions.
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
```

## Key Theorems

**Legendre's Three-Square Theorem**:
```lean
theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ is_three_square_exception n
```

**Gauss's Eureka Theorem**:
```lean
theorem gauss_eureka (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n
```

**Fermat's Polygonal Number Theorem**:
```lean
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n
```

## Proof Strategy for Legendre's Theorem

The primary objective is the formalization of the hard direction of Legendre's theorem (n not an exception implies representation by three squares). The strategy employs Ankeny's descent method (1957), which uses the geometry of numbers to bridge local p-adic conditions and global integer existence.

## References

- Legendre, A. M. (1798). *Essai sur la théorie des nombres*.
- Cauchy, A. L. (1813). *Démonstration du théorème général de Fermat sur les nombres polygones*.
- Ankeny, N. C. (1957). *Sums of three squares*. Proceedings of the American Mathematical Society.
- Nathanson, M. B. (1987). *A short proof of Cauchy's polygonal number theorem*.
