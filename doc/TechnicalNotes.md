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

## Optimization: Specialization and the Nathanson Gap

*   **Observation**: The expression $4a - b^2$ appearing in Cauchy's Lemma is always congruent to $3 \pmod 8$ when $a$ and $b$ are odd.
*   **Impact**: Specifying \(n \equiv 3 \pmod 8\) satisfies the requirements for the general theorem while avoiding powers-of-4 logic.
*   **The Nathanson Gap**: During the formalization of the Cauchy reduction, we identified a known gap in Nathanson's original 1987 paper regarding complete residue classes modulo \(m\). This library targets the corrected proof presented in Nathanson's 1996 book (*Additive Number Theory: The Classical Bases*), ensuring mathematical rigor.

## 4. Verification Infrastructure
The project maintains a suite of experiments to validate algebraic invariants and reduce formalization friction.

### Experiments policy (buildability first)

- Every file under `Experiments/` must **compile under `lake build`** at all times.
- Proofs may use `sorry` (with a short “Escape Hatch” comment), but experiments should not contain
  API-drifted proof attempts that break compilation.
- If an experiment becomes stale, prefer replacing the proof body with a stable placeholder and a
  minimal statement that records intent.

*   **Congruence Bridges (`Experiments/CheckZMod.lean`)**: Validates the mapping between `ZMod` equalities and `Int.ModEq` congruences, including CRT-style combinations.
*   **Numeric Validation (`Experiments/ankeny_check.py`)**: Performs exhaustive searches for small instances of the Ankeny quadratic form setup.
*   **Valuation Logic (`Experiments/DescentValuation.lean`)**: Sketch scaffold for the p-adic contradiction logic for the descent step (currently uses placeholders).
*   **LLL Probing (`Experiments/LLLRational.lean`)**: Validates rational-arithmetic steps for the lattice reduction algorithm.
*   **Successive Minima (`Experiments/SuccessiveMinimaBasic.lean`)**: Type-level probe for the spectral theory definition on a standard lattice (currently uses placeholders).
