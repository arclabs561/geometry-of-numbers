# Record of Progress

## Phase 1: Foundations
*   **Polygonal Numbers**: Defined `polygonal s n` and established basic identities like the alternative quadratic form in `ℤ` and the recurrence `P(s,n+1) = P(s,n) + 1 + (s-2)n`.
*   **Cauchy Identity**: Proved the core algebraic identity connecting sums of polygonal numbers to sums of squares: `2 * ∑ P(s, x_i) = (s-2) * ∑ x_i^2 + (4-s) * ∑ x_i`.

## Phase 2: Legendre's Three-Squares Theorem
*   **Lattice Construction**: Constructed a 3D lattice `Λ` with covolume `n²` satisfying `x² + y² + z² ≡ 0 (mod n)`.
*   **Covolume Lemma**: Proved that the fundamental domain volume is exactly `n²`.
*   **Research Pivot**: Realized via experiments that Minkowski's direct volume argument is only sufficient for very small `n`. Potted a pivot to the **Method of Descent** (Ankeny/Mordell).

## Phase 3: Cauchy's Lemma
*   **Interval Logic**: Formalized lemmas for finding odd integers in real intervals.
*   **Gauss's Eureka Theorem**: Sketched the reduction of the triangular number theorem to the three-squares theorem for `8n+3`.

## Current Status (Jan 2026)
*   Main theorem `fermat_polygonal` is defined but uses `sorry`.
*   Active development is in `PolygonalNumberTheorem/Legendre/Minkowski.lean` (Descent step).
*   Small cases `n < 108(s-2)` verified via Python script.
