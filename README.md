## Geometry of Numbers (Lean 4)

[![CI](https://github.com/arclabs561/geometry-of-numbers/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/arclabs561/geometry-of-numbers/actions/workflows/lean_action_ci.yml)

Lean 4 formalization of geometry-of-numbers proofs: Legendre's three-square theorem via Ankeny's descent, Fermat's polygonal number theorem via Cauchy/Nathanson, and a computable exact-rational LLL implementation with verified termination.

The codebase is `sorry`-free and builds against current Mathlib.

### Proved theorems

```lean
-- Legendre's Three-Square Theorem (GeometryOfNumbers/Legendre/Main.lean)
theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ is_three_square_exception n

-- Gauss's Triangular Number Theorem (GeometryOfNumbers/Cauchy/Main.lean)
theorem gauss_triangular (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n

-- Fermat's Polygonal Number Theorem (GeometryOfNumbers/Cauchy/Main.lean)
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n
```

The computable LLL track (`GeometryOfNumbers/Computable/`) provides an exact rational
Gram-Schmidt LLL loop with a proved postcondition (`finished` implies `LLLReducedQ`)
and a termination witness under row linear independence.

### Building

Requires [elan](https://github.com/leanprover/elan) (installs the pinned Lean toolchain automatically).

```bash
lake build
```

Run checks:

```bash
just status          # should report 0 sorry tokens
just fast            # quick feedback loop
just regen-check     # regenerate + verify Cauchy medium-regime tables
```

### Structure

```
GeometryOfNumbers/
  Core/             Shared infrastructure (polygonal defs, Minkowski wrapper,
                    successive minima, determinants, modular squares)
  Legendre/         Ankeny descent + three-square theorem entry point
  Cauchy/           Polygonal number reduction + generated medium-regime tables
  Computable/       Exact-ℚ LLL loop, correctness proofs, termination

Experiments/        Compilation-checked scratch files and sanity probes
Scripts/            Status report, linters, pre-commit checks
```

### Key formulas

Three-square exceptions have the form $n = 4^a(8k+7)$.

Ankeny's descent uses the ternary quadratic form:

$$
Q(x,y,z) = 2qx^2 + y^2 + nz^2.
$$

For `s >= 5`, the Cauchy/Nathanson reduction produces
$n = \sum_{i=1}^4 P(s,x_i) + r$ with $0 \le r \le s-4$,
then pads with `0/1` polygonals.

### References

- Ankeny, N. C. (1957). *Sums of three squares*. Proceedings of the AMS.
- Cauchy, A. L. (1813). *Demonstration du theoreme general de Fermat sur les nombres polygones*.
- Legendre, A. M. (1798). *Essai sur la theorie des nombres*.
- Nathanson, M. B. (1987). *A short proof of Cauchy's polygonal number theorem*.

### License

Dual-licensed under MIT or Apache-2.0.
