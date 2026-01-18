# Technical Notes and Shelved Approaches

## 1. Direct Minkowski Application for Sum of Three Squares
*   **Approach**: Utilize Minkowski's Convex Body Theorem on a sphere of radius $\sqrt{n}$ within a lattice of covolume $n$.
*   **Analysis**: In three dimensions, the volume of a sphere with radius $R$ is $\frac{4}{3}\pi R^3$. For a non-zero lattice point to be guaranteed, the volume must exceed $8 \cdot \text{covolume}$.
*   **Constraint**: For $\text{covolume} = n$, the requirement is $\frac{4}{3}\pi n^{3/2} > 8n$, or $\sqrt{n} > \frac{6}{\pi} \approx 1.91$, implying $n > 3.65$. For $n=3$, the volume is $\frac{4}{3}\pi (3\sqrt{3}) \approx 21.7$, which is less than the required $24$.
*   **Conclusion**: Direct application is insufficient for small \(n\). The project has pivoted to a descent method, representing \(kn\) and descending to \(k=1\).

## 2. Ternary Quadratic Forms (Archive/TernaryQF.lean)
*   **Approach**: Employ the theory of ternary quadratic forms, including genus and class number considerations.
*   **Obstacle**: This route requires significant infrastructure for quadratic form equivalence and mass formulas, which is currently underdeveloped or highly complex in Mathlib4.
*   **Conclusion**: Shelved in favor of the more direct geometric descent method.

## Specialization: the Nathanson (1987) gap

*   **Observation**: The expression $4a - b^2$ appearing in Cauchy's Lemma is always congruent to $3 \pmod 8$ when $a$ and $b$ are odd.
*   **Impact**: Specifying \(n \equiv 3 \pmod 8\) satisfies the requirements for the general theorem while avoiding powers-of-4 logic.
*   **Note**: During the formalization of the Cauchy reduction, we rely on the corrected proof in Nathanson’s 1996 book (not the 1987 note), due to a known gap about complete residue classes modulo \(m\).

## 4. Verification Infrastructure
The project maintains a suite of experiments to validate algebraic invariants and reduce formalization friction.

### Experiments policy (buildability first)

- Every file under `Experiments/` must **compile under `lake build`** at all times.
- Proofs may use `sorry` (with a short “TODO(sorry)” comment), but experiments should not contain
  API-drifted proof attempts that break compilation.
- If an experiment becomes stale, prefer replacing the proof body with a stable placeholder and a
  minimal statement that records intent.

*   **Congruence Bridges (`Experiments/CheckZMod.lean`)**: Validates the mapping between `ZMod` equalities and `Int.ModEq` congruences, including CRT-style combinations.
*   **Numeric Validation (`Experiments/ankeny_check.py`)**: Performs exhaustive searches for small instances of the Ankeny quadratic form setup.
*   **Valuation Logic (`Experiments/DescentValuation.lean`)**: Sketch scaffold for the p-adic contradiction logic for the descent step (currently uses placeholders).
*   **LLL Probing (`Experiments/LLLRational.lean`)**: Validates rational-arithmetic steps for the lattice reduction algorithm.
*   **Successive Minima (`Experiments/SuccessiveMinimaBasic.lean`)**: Type-level experiment for the spectral theory definition on a standard lattice (currently uses placeholders).

## 5. Linting (what we treat as “useful”)

This repo uses two different kinds of linting:

- **Text/style lint**: `lake exe lint-style`
  - This is high-signal because it catches purely mechanical drift (e.g. trailing whitespace) that creates noisy diffs.
  - The file `Scripts/nolints-style.txt` is the (optional) allowlist; keep it empty unless we have a specific justification.

- **Lean lints (proof hygiene)**: Lean’s built-in linters and Mathlib linters.
  - **High-signal**: unused simp args, unused arguments/locals, and anything indicating API drift.
  - **Lower-signal**: `try 'simp' instead of 'simpa'` warnings; treat as optional unless it improves readability.
