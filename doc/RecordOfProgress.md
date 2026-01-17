# Record of Progress

## Phase 1: Foundations
*   **Polygonal Numbers**: Defined `polygonal s n` and established basic identities like the alternative quadratic form in `ℤ` and the recurrence `P(s,n+1) = P(s,n) + 1 + (s-2)n`.
*   **Cauchy Identity**: Proved the core algebraic identity connecting sums of polygonal numbers to sums of squares: `2 * ∑ P(s, x_i) = (s-2) * ∑ x_i^2 + (4-s) * ∑ x_i`.

## Phase 2: Legendre's Three-Squares Theorem
*   **Lattice construction (scaffold)**: Implemented candidate lattice definitions for both the Minkowski-style and Ankeny-style routes.
    The intended invariants are congruence-defined membership and a computable covolume; some of these are still `sorry`.
*   **Covolume computation (scaffold)**: The main covolume statements are currently scaffolds (`sorry`) in the main proof files,
    but there is a fair amount of working API exploration in `Experiments/CheckMinkowski.lean`.
*   **Research pivot**: The direct Minkowski “one-shot volume” argument is not strong enough uniformly.
    The current direction is descent (Ankeny-style): find a representation of \(2nq\) and reduce to \(n\).

## Phase 3: Cauchy's Lemma
*   **Interval Logic**: Formalized lemmas for finding odd integers in real intervals.
*   **Gauss's Eureka Theorem**: Currently a scaffold in `Cauchy/Main.lean` (uses `sorry`).

## Current Status (Jan 2026)
*   Main theorem `fermat_polygonal` is defined but uses `sorry`.
*   Active development is split:
    - `Covolume/Legendre/AnkenyLemmas.lean` is the cleanest component (0 `sorry`).
    - `Covolume/Legendre/Ankeny.lean` is the main scaffold (several `sorry`).
    - `Covolume/Cauchy/Main.lean` is the polygonal theorem scaffold (`sorry`).
*   Numeric sanity: `uv run Experiments/ankeny_check.py` checks small instances of the Ankeny reduction setup (not a proof).
