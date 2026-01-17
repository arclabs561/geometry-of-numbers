# Record of Progress

## Phase 1: Foundations
*   **Polygonal Numbers**: Defined `polygonal s n` and established basic identities, including the recurrence \(P(s,n+1) = P(s,n) + 1 + (s-2)n\) and the quadratic closed form in \(\mathbb{Z}\).
*   **Cauchy Identity**: Proved the core algebraic identity relating sums of polygonal numbers to sums of squares: \(2 \cdot \sum P(s, x_i) = (s-2) \cdot \sum x_i^2 + (4-s) \cdot \sum x_i\).

## Phase 2: Legendre's Three-Square Theorem
*   **Lattice Construction**: Implemented candidate lattice definitions for Ankeny-style descent. The current implementation uses congruence-defined membership and targets a computable covolume.
*   **Covolume Computation**: Initial API exploration for covolume calculations is documented in `Experiments/CheckMinkowski.lean`.
*   **Proof Strategy Pivot**: The project has shifted from a direct Minkowski application to Ankeny's descent method. This approach involves finding a representation of \(2nq\) and reducing it to a representation of \(n\).

## Phase 3: Cauchy's Lemma
*   **Interval Logic**: Scaffold for lemmas identifying odd integers within specified real intervals (proofs pending).
*   **Gauss's Eureka Theorem**: The triangular number theorem ($s=3$) is currently a formalized scaffold awaiting proof completion.

## Project Status (January 2026)
*   The main theorem `fermat_polygonal` is defined, but still contains placeholders in the reduction chain.
*   Active development is prioritized as follows:
    - `Covolume/Legendre/AnkenyLemmas.lean`: Proved foundational components.
    - `Covolume/Legendre/Ankeny.lean`: Primary descent proof structure.
    - `Covolume/Cauchy/Main.lean`: Top-level theorem reduction.
*   Numeric Validation: The `Experiments/ankeny_check.py` script continues to validate the Ankeny reduction hypothesis across a range of small inputs.
