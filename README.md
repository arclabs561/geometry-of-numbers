# Polygonal Number Theorem

Formalization of **Legendre's Three-Square Theorem** and the **Fermat/Cauchy Polygonal Number Theorem** in Lean 4.

Dual-licensed under MIT or Apache-2.0.

```sh
# Install Lean + lake (one-time). This repo is pinned by `lean-toolchain`.
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

```
lake build
lake exe status_report
```

Note: this workspace also has a sibling directory `../PolygonalNumberTheorem/` with
scratch Lean files. We’re merging useful bits into this repo (copying, not deleting).

## Status

| Component | Status |
|-----------|--------|
| Legendre easy direction | Done |
| Legendre hard direction | 1 sorry |
| Gauss's Eureka (triangular) | Done (mod Legendre) |
| Lagrange (squares) | Via Mathlib |
| Cauchy's lemma | 1 sorry |
| Fermat polygonal (s ≥ 5) | 2 sorrys |

**Total: 5 sorrys** (all depend on the Legendre hard direction)

## Structure

```
PolygonalNumberTheorem/
  Basic.lean           -- polygonal(s,n) definition, algebraic identities
  LowDim.lean          -- 2x2, 3x3 determinant formulas
  TernaryQF.lean       -- Ternary quadratic forms x² + y² + z²
  SumThreeSquares.lean -- Legendre's theorem (both directions)
  Cauchy.lean          -- Cauchy's lemma, Gauss Eureka, main theorem
```

## Key Theorems

**Legendre** (characterization):
```lean
theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ is_three_square_exception n
```

**Gauss Eureka** (every n is sum of 3 triangular numbers):
```lean
theorem gauss_eureka (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n
```

**Fermat Polygonal** (every n is sum of s s-gonal numbers):
```lean
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n
```

## Proof Strategy for Legendre Hard Direction

The main blocker. Three possible approaches:

1. **Minkowski** (geometry of numbers): Show a lattice point exists in a suitable region
2. **Ankeny** (elementary): Use primes in arithmetic progressions
3. **Reduction theory**: Show x² + y² + z² represents all valid n via class number 1

## References

- Legendre (1798). *Essai sur la théorie des nombres*.
- Cauchy (1813). *Démonstration du théorème général de Fermat*.
- Ankeny (1957). *Sums of three squares*. Proc. AMS.
- Nathanson (1987). *A short proof of Cauchy's polygonal number theorem*.
