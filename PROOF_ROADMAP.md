# Proof Roadmap

## Dependency Graph

```
Nat.sum_four_squares (Mathlib)
         │
         ▼
QuadraticLattice Bridge
         │
         ▼
sum_three_squares_of_not_exception
         │
         ├──────────────────────────────┐
         ▼                              ▼
four_nonneg_sum_from_cauchy      gauss_triangular
         │                              │
         ▼                              │
cauchy_decomposition                    │
         │                              │
         ▼                              │
fermat_polygonal (s ≥ 5)    fermat_polygonal (s = 3)
```

## Parallel Track: Computable LLL

Independent of the primary proof, the library targets a *computable* LLL implementation in `Covolume/Computable/LLL.lean`.
At the moment this is a scaffold (with placeholders), plus a small rational-arithmetic probe in `Experiments/LLLRational.lean`.

## Ankeny's Proof (Covolume/Legendre/Ankeny.lean)

The current implementation of `sum_three_squares_of_not_exception` follows the geometric descent method proposed by Ankeny (1957). The proof structure is formalized and typechecks, with specific technical lemmas awaiting completion.

1.  **Ankeny Lemmas**: Squarefree decomposition and mod-8 congruence logic. Fully formalized in `Covolume/Legendre/AnkenyLemmas.lean`.
2.  **Lattice Definition**: The `ankeny_lattice` is defined as an `AddSubgroup (Fin 3 → ℝ)` encoding the congruences $x \equiv y \pmod n$ and $y \equiv bz \pmod{2q}$.
3.  **Algebraic Glue**: `ankeny_Q_mod` proves that $Q(x,y,z) = 2qx^2 + y^2 + nz^2$ vanishes modulo $2nq$, assuming the two defining congruences and the relation $b^2 \equiv -n \pmod{2q}$.
4.  **Minkowski Application**:
    - The full geometric call-site (volume bound + Minkowski) is proved in `Experiments/CheckMinkowski.lean`.
    - `exists_ankeny_representation` in `Covolume/Legendre/Ankeny.lean` is the port target: extract the congruences + a strict bound $0 < Q(x,y,z) < 4nq$ from ellipsoid membership, then force $Q(x,y,z) = 2nq$ by divisibility.
5.  **Descent Step**: `reduction_to_sum_three_squares` is the intended valuation-based descent step using primes \(p \equiv 3 \pmod 4\) (currently a placeholder).

## Cauchy's Lemma (Covolume/Cauchy/Main.lean)

The final stage of the project formalizes Cauchy's reduction of the general Fermat Polygonal Number Theorem to the sum of four s-gonal numbers, leveraging Legendre's Three-Square Theorem.

## Project Status

| Task | Status | Location |
|------|--------|----------|
| **Core Algebra** | Mixed | `Covolume/Core/Basic.lean` (proved), `Covolume/Core/ModularSquares.lean` (WIP) |
| **Ankeny Lemmas** | Proved | `Covolume/Legendre/AnkenyLemmas.lean` |
| **Ankeny Proof** | Active | `Covolume/Legendre/Ankeny.lean` |
| **Cauchy Reduction** | Scaffold | `Covolume/Cauchy/Main.lean` |
| **Gauss Triangular** | Scaffold | `Covolume/Cauchy/Main.lean` |

## Auxiliary Evidence

- **Congruence Bridges**: `Experiments/CheckZMod.lean` provides validated patterns for mapping `ZMod` operations to `Int.ModEq`.
- **Numeric Validation**: `Experiments/ankeny_check.py` performs exhaustive searches for small cases to verify the intended algebraic invariants of the Ankeny setup.
- **LLL Probing**: `Experiments/LLLRational.lean` verifies rational LLL steps on simple bases.
