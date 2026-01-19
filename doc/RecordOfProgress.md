# Record of Progress

## Phase 1: Foundations
*   **Polygonal Numbers**: Defined `polygonal s n` and established basic identities, including the recurrence $P(s,n+1) = P(s,n) + 1 + (s-2)n$ and the quadratic closed form in $\mathbb{Z}$.
*   **Cauchy Identity**: Proved the core algebraic identity relating sums of polygonal numbers to sums of squares: $2 \cdot \sum P(s, x_i) = (s-2) \cdot \sum x_i^2 + (4-s) \cdot \sum x_i$.

## Phase 2: Legendre's Three-Square Theorem
*   **Lattice Construction**: Implemented candidate lattice definitions for Ankeny-style descent. The current implementation uses congruence-defined membership and targets a computable covolume.
*   **Covolume Computation**: Initial API exploration for covolume calculations is documented in `Experiments/CheckMinkowski.lean`.
*   **Proof Strategy Pivot**: The project has shifted from a direct Minkowski application to Ankeny's descent method. This approach involves finding a representation of $2nq$ and reducing it to a representation of $n$.

## Phase 3: Cauchy's Lemma
*   **Interval Logic**: Scaffold for lemmas identifying odd integers within specified real intervals (proofs pending).
*   **Gauss's Eureka Theorem**: Implemented `gauss_triangular` in `Covolume/Cauchy/Main.lean` (proved).
*   **Cauchy/Nathanson route (structure)**:
    - Updated the target statement for `s ≥ 5` to the standard “four terms + residue” form
      \(n = \sum_{i=1}^4 P(s,x_i) + r\) with \(0 \le r \le s-4\).
    - Proved the padding/bookkeeping lemma that turns this into an `Fin s → ℕ` family by filling the
      remaining slots with `1` (for the residue) and `0`.
    - Extracted two explicit boundary lemmas as `sorry` stubs: `nathanson_parameters` and `cauchy_lemma`.
    - Added an experiment module `Covolume/Experiments/CauchyIdentityScratch.lean` to validate the algebraic spine.

## Project Status (January 2026)
*   The main theorem `fermat_polygonal` is defined, but still contains placeholders in the reduction chain.
*   Active development is prioritized as follows:
    - `Covolume/Legendre/AnkenyLemmas.lean`: Proved foundational components.
    - `Covolume/Legendre/Ankeny.lean`: Primary descent proof structure.
    - `Covolume/Cauchy/Main.lean`: Top-level theorem reduction.
*   Numeric Validation: keep sanity checks as Lean `Experiments/*` modules (so they compile under `lake build`).
