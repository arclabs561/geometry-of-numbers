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

If `lake` isn’t on your PATH, try `"$HOME/.elan/bin/lake"` instead.

Note: this workspace also has a sibling directory `../PolygonalNumberTheorem/` with
scratch Lean files. We’re merging useful bits into this repo (copying, not deleting).

## Status

`lake build` succeeds, but the development files still contain `sorry` placeholders.
Treat anything labeled “done” as “typechecks”, not “fully proved”.

## Structure

```
PolygonalNumberTheorem/
  Core/Basic.lean            -- polygonal(s,n) definition + algebra spine
  Core/ModularSquares.lean   -- modular “u²+v²+1≡0” root existence (WIP)
  Legendre/Exceptions.lean   -- exception set: 4^a(8k+7)
  Legendre/Minkowski.lean    -- Minkowski/descent scaffolding (WIP)
  Legendre/Main.lean         -- Legendre statement + glue to proof attempt (WIP)
  Cauchy/Main.lean           -- Cauchy lemma + polygonal theorem scaffolding (WIP)

Scripts/
  StatusReport.lean          -- prints the current (manual) status summary
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
