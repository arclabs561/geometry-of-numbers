# Proof Roadmap

## Dependency Graph

```
Nat.sum_four_squares (Mathlib)
         │
         ▼
QuadraticLattice Bridge  ◄── SYSTEMS KERNEL
         │
         ▼
sum_three_squares_of_not_exception
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

## Parallel Track: Computable LLL

Independent of the primary proof, the library targets a verified LLL implementation in `Covolume/Computable/LLL.lean`. This provides a computational method for finding the lattice points whose existence is guaranteed by the Three-Square Theorem.

## Ankeny's Proof (Covolume/Legendre/Ankeny.lean)

The current implementation of `sum_three_squares_of_not_exception` follows the geometric descent method proposed by Ankeny (1957). The proof structure is formalized and typechecks, with specific technical lemmas awaiting completion.

1.  **Ankeny Lemmas**: Squarefree decomposition and mod-8 congruence logic. Fully formalized in `Covolume/Legendre/AnkenyLemmas.lean`.
2.  **Lattice Definition**: The `ankeny_lattice` is defined as an `AddSubgroup (Fin 3 → ℝ)` encoding the congruences \(x \equiv y \pmod n\) and \(y \equiv bz \pmod{2q}\).
3.  **Algebraic Glue**: `ankeny_Q_mod` establishes that the quadratic form \(Q(x,y,z) = 2qx^2 + y^2 + nz^2\) vanishes modulo \(2nq\) for all points in the lattice.
4.  **Minkowski Application**: `exists_ankeny_representation` utilizes volume bounds to guarantee a non-zero lattice point satisfying \(Q(x,y,z) = 2nq\).
5.  **Descent Step**: `reduction_to_sum_three_squares` reduces the Ankeny representation to a sum of three squares for \(n\) using the properties of prime factors \(p \equiv 3 \pmod 4\).

## Cauchy's Lemma (Covolume/Cauchy/Main.lean)

The final stage of the project formalizes Cauchy's reduction of the general Fermat Polygonal Number Theorem to the sum of four s-gonal numbers, leveraging Legendre's Three-Square Theorem.

## Project Status

| Task | Status | Location |
|------|--------|----------|
| **Core Algebra** | Mixed | `Covolume/Core/Basic.lean` (proved), `Covolume/Core/ModularSquares.lean` (WIP) |
| **Ankeny Lemmas** | Proved | `Covolume/Legendre/AnkenyLemmas.lean` |
| **Ankeny Proof** | Active | `Covolume/Legendre/Ankeny.lean` |
| **Cauchy Reduction** | Scaffold | `Covolume/Cauchy/Main.lean` |
| **Gauss Eureka** | Scaffold | `Covolume/Cauchy/Main.lean` |

## Auxiliary Evidence

- **Congruence Bridges**: `Experiments/CheckZMod.lean` provides validated patterns for mapping `ZMod` operations to `Int.ModEq`.
- **Numeric Validation**: `Experiments/ankeny_check.py` performs exhaustive searches for small cases to verify the intended algebraic invariants of the Ankeny setup.
