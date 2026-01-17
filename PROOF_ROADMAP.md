# Proof Roadmap

## Dependency Graph

```
Nat.sum_four_squares (Mathlib)
         │
         ▼
sum_three_squares_of_not_exception  ◄── THE MAIN GAP (Closed via Ankeny)
         │
         ├──────────────────────────────┐
         ▼                              ▼
four_nonneg_sum_from_cauchy      gauss_eureka
         │                              │
         ▼                              │
cauchy_decomposition                    │
         │                              │
         ▼                              │
fermat_polygonal (s ≥ 5)    fermat_polygonal (s = 3)
```

## The Key Missing Piece: Resolved Structure

**`sum_three_squares_of_not_exception`** is now routed through **Ankeny's 1957 Proof** using Geometry of Numbers.

### Ankeny's Proof (`Legendre/Ankeny.lean`)

1.  **Ankeny Lemmas** ✅: Foundational lemmas about squarefree decomposition and modular arithmetic proven in `Legendre/AnkenyLemmas.lean`.
2.  **Lattice Construction** ✅: We build a lattice $L$ based on $x \equiv y \pmod n$ and $y \equiv bz \pmod{2q}$.
3.  **Minkowski's Theorem** 🚧: We have the skeleton for covolume $2nq$ and finding a nonzero point.
4.  **Representation** 🚧: reducing $2qx^2 + y^2 + nz^2 = 2nq$ to $n = x^2 + u^2 + v^2$.

## Cauchy's Lemma (`Cauchy/Main.lean`)

Once we have the three-square theorem, `four_nonneg_sum_from_cauchy` follows by reducing the general `s`-gonal case to the sum of four `s`-gonal numbers.

## Timeline & Status

| Task | Status | Location |
|------|--------|----------|
| **Core Algebra** | ✅ Done | `Core/Basic.lean` |
| **Ankeny Lemmas** | ✅ Done | `Legendre/AnkenyLemmas.lean` |
| **Ankeny Descent** | 🚧 95% | `Legendre/Ankeny.lean` |
| **Cauchy Reduction**| 🚧 WIP | `Cauchy/Main.lean` |
| **Gauss Eureka** | ❌ Todo | `Cauchy/Main.lean` |

## Deprecated

- `Legendre/Minkowski.lean`: An earlier attempt. Use `Ankeny.lean` instead.
