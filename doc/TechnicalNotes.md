# Technical Notes and Shelved Approaches

## 1. Direct Minkowski for Sum of Three Squares
*   **Approach**: Use Minkowski's Convex Body Theorem on a ball of radius `√n` in a lattice of covolume `n`.
*   **Problem**: In 3D, the volume of a ball of radius `R` is `(4/3)πR³`. For a point to be guaranteed, we need `(4/3)πn^{3/2} > 8 * covolume`.
*   **Result**: If `covolume = n`, we need `n^{1/2} > 6/π ≈ 1.91`, so `n > 3.65`. However, for `n=3`, the volume is `(4/3)π(3√3) ≈ 21.7 < 24`.
*   **Refinement**: If we use the lattice with `covolume = n²` (from `x ≡ uz, y ≡ vz`), the gap is even larger.
*   **Decision**: Shelved direct application in favor of **Descent**. We find a representation of `kn` and descend to `k=1`.

## 2. Ternary Quadratic Forms (Archive/TernaryQF.lean)
*   **Approach**: Use the theory of ternary quadratic forms and genus/class numbers.
*   **Problem**: Requires extensive infrastructure for quadratic forms (genus, mass formula, etc.) that is partially missing or very complex in current Mathlib4.
*   **Decision**: Shelved in favor of the more elementary (though technically involved) Minkowski Descent.

## 3. Ankeny's Descent (Archive/Ankeny.lean)
*   **Approach**: Use a specific prime `q` and a refined lattice to descend directly.
*   **Status**: Highly promising, but requires Dirichlet's Theorem on primes in arithmetic progressions to pick `q`.
*   **Decision**: Kept as a reference in `Archive/` in case the Minkowski route becomes too difficult.
