# Record of Progress

## Phase 1: Foundations
*   **Polygonal Numbers**: Defined `polygonal s n` and established basic identities, including the recurrence $P(s,n+1) = P(s,n) + 1 + (s-2)n$ and the quadratic closed form in $\mathbb{Z}$.
*   **Cauchy Identity**: Proved the core algebraic identity relating sums of polygonal numbers to sums of squares: $2 \cdot \sum P(s, x_i) = (s-2) \cdot \sum x_i^2 + (4-s) \cdot \sum x_i$.

## Phase 2: Legendre's Three-Square Theorem
*   **Lattice Construction**: Implemented candidate lattice definitions for Ankeny-style descent. The current implementation uses congruence-defined membership and targets a computable covolume.
*   **covolume computation**: Initial API exploration for covolume calculations is documented in `Experiments/CheckMinkowski.lean`.
*   **Proof Strategy Pivot**: The project has shifted from a direct Minkowski application to Ankeny's descent method. This approach involves finding a representation of $2nq$ and reducing it to a representation of $n$.

## Phase 3: Cauchy's Lemma
*   **Interval Logic**: Implemented the real-interval lemma for picking odd integers (see `GeometryOfNumbers/Cauchy/Main.lean`).
*   **Gauss's Eureka Theorem**: Implemented `gauss_triangular` in `GeometryOfNumbers/Cauchy/Main.lean` (proved).
*   **Cauchy/Nathanson route (structure)**:
    - Updated the target statement for `s ≥ 5` to the standard “four terms + residue” form
      \(n = \sum_{i=1}^4 P(s,x_i) + r\) with \(0 \le r \le s-4\).
    - Proved the padding/bookkeeping lemma that turns this into an `Fin s → ℕ` family by filling the
      remaining slots with `1` (for the residue) and `0`.
    - Kept explicit lemma boundaries for the hard steps (`nathanson_parameters_large`, `cauchy_lemma`) so the rest is algebra/bookkeeping.
    - Added an experiment module `Experiments/CauchyIdentityScratch.lean` to validate the algebraic spine.
*   **Generated tables (medium regime)**: Introduced sharded table modules to keep compilation time bounded:
    - `GeometryOfNumbers/Cauchy/MediumTablesSmall.lean` importing shards `MediumTablesSmall/S05..S23.lean`
    - `GeometryOfNumbers/Cauchy/MediumTablesMge22.lean` for the \(s-2 \ge 22\) regime

## Project Status
*   `lake exe status_report` reports **0** `sorry` tokens across `GeometryOfNumbers/`, `Scripts/`, and `Experiments/`.
*   `./Scripts/check.sh pre-commit` and `./Scripts/check.sh pre-push` are green (including the generated-table `regen-check` lane).
*   Main entrypoints:
    - `GeometryOfNumbers/Legendre/Main.lean`: `sum_three_squares_iff` and its directional lemmas.
    - `GeometryOfNumbers/Cauchy/Main.lean`: `gauss_triangular` and `fermat_polygonal`.
*   Numeric Validation: keep sanity checks as Lean `Experiments/*` modules (so they compile under `lake build`).

## Phase 4: Computable LLL (exact, ℚ-based)

This is a parallel “algorithmic correctness” track, independent of the Legendre/Cauchy proofs.

**Where we are now (rough):**

- **Executable core (≈ 70%)**:
  - `GeometryOfNumbers/Computable/LLLExact.lean` contains a fully computable LLL loop (fuel-bounded) with an
    instrumented runner `lllRunExact` and reducedness checkers `isSizeReducedQ` / `isLovaszReducedQ` / `isLLLReducedQ`.
- **Invariants + step correctness (≈ 50%)**:
  - `GeometryOfNumbers/Computable/LLLCore.lean`: integer row operations + `rowSpan` preservation (proved).
  - `GeometryOfNumbers/Computable/LLLExactProofs.lean`: dot-product algebra, rounding bound, GS fold orthogonality,
    GS identity `dot(b,u)=dot(u,u)`, and prefix linkage lemmas for `gsoPrefixListQ`.
- **Main postcondition (≈ 0–20%)**:
  - Next target is a theorem of the form:
    - if `lllRunExact.reason = finished`, then the output basis satisfies `isLLLReducedQ = true`
    - and then a Prop-level “LLLReduced” specification mirroring the boolean checks.
- **Termination / complexity (≈ 0–10%)**:
  - Not yet formalized; expected to require a potential-function argument and careful bookkeeping choices.

**Why the uncertainty:** there are multiple plausible proof routes for the postcondition and for termination
(boolean-level vs Prop-level first; how much “GS structure” we expose as lemmas; what potential function we commit to).
