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

Independent of the primary proof tracks, the library targets a **computable** LLL implementation:

- `GeometryOfNumbers/Computable/LLLExact.lean`: executable, exact loop (ℚ Gram–Schmidt) + instrumented runner `lllRunExact`
- `GeometryOfNumbers/Computable/LLLExactProofs.lean`: correctness lemmas supporting the eventual postcondition
- `GeometryOfNumbers/Computable/LLL.lean`: noncomputable (ℝ) loop scaffold

Status:

- **Correctness**: `finished → LLLReducedQ` is proved in `LLLExactProofs.lean`.
- **Termination**: `∃ limit, (lllRunExact B δ limit).reason = .finished` (under `RowLIQ` and `δ < 1`) is proved
  in `LLLExactTermination.lean`.
- **Next**: relate the proof’s measure/potential to a *recognizable* complexity bound (swap/iteration count).

## Ankeny's Proof (`GeometryOfNumbers/Legendre/Ankeny.lean`)

The current implementation follows the geometric descent method proposed by Ankeny (1957).
As of the current repo state, the proof is **sorry-free** and `GeometryOfNumbers/Legendre/Main.lean`
exports the clean interface `sum_three_squares_iff`.

1.  **Ankeny Lemmas**: Squarefree decomposition and mod-8 congruence logic. Fully formalized in `GeometryOfNumbers/Legendre/AnkenyLemmas.lean`.
2.  **Lattice Definition**: The `ankeny_lattice` is defined as an `AddSubgroup (Fin 3 → ℝ)` encoding the congruences $x \equiv y \pmod n$ and $y \equiv bz \pmod{2q}$.
3.  **Algebraic Glue**: `ankeny_Q_mod` proves that $Q(x,y,z) = 2qx^2 + y^2 + nz^2$ vanishes modulo $2nq$, assuming the two defining congruences and the relation $b^2 \equiv -n \pmod{2q}$.
4.  **Minkowski Application**:
    - The full geometric call-site (volume bound + Minkowski) is proved in `Experiments/CheckMinkowski.lean`.
    - `exists_ankeny_representation` in `GeometryOfNumbers/Legendre/Ankeny.lean` is the port target: extract the congruences + a strict bound $0 \lt Q(x,y,z) \lt 4nq$ from ellipsoid membership, then force $Q(x,y,z) = 2nq$ by divisibility.
5.  **Descent Step**: `reduction_to_sum_three_squares` (and the Q₁ analogue) implement the valuation-based descent step using primes $p \equiv 3 \pmod 4$.

## Cauchy's Lemma (`GeometryOfNumbers/Cauchy/Main.lean`)

The final stage of the project formalizes the **Cauchy/Nathanson reduction** in the sharper form:

$$
  \forall s \ge 5,\ \forall n,\ \exists x_1,x_2,x_3,x_4,r,\quad
  n = \sum_{i=1}^4 P(s, x_i) + r,\qquad 0 \le r \le s-4.
$$

Then `r` is realized by padding with `r` copies of `P(s,1)=1` and `s-4-r` copies of `P(s,0)=0` to
obtain exactly `s` terms.

## Project Status

| Task | Status | Location |
|------|--------|----------|
| **Core Algebra** | Mostly proved | `GeometryOfNumbers/Core/Basic.lean` (proved), `GeometryOfNumbers/Core/ModularSquares.lean` (proved; odd-modulus solvability) |
| **Ankeny Lemmas** | Proved | `GeometryOfNumbers/Legendre/AnkenyLemmas.lean` |
| **Ankeny Proof** | Proved | `GeometryOfNumbers/Legendre/Ankeny.lean` |
| **Cauchy Reduction** | Proved | `GeometryOfNumbers/Cauchy/Main.lean` |
| **Gauss Triangular** | Proved | `GeometryOfNumbers/Cauchy/Main.lean` |

## Auxiliary Evidence

- **Congruence Bridges**: `Experiments/CheckZMod.lean` provides validated patterns for mapping `ZMod` operations to `Int.ModEq`.
- **Numeric Validation**: keep numeric sanity checks in Lean (`Experiments/*`) so `lake build` remains the single source of truth.
- **LLL Probing**: `Experiments/LLLRational.lean` verifies rational LLL steps on simple bases.
