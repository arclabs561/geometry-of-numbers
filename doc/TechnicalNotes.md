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

## 4. Discovery: Cauchy's Proof only requires $n \equiv 3 \pmod 8$
*   **Discovery**: The integer $4a - b^2$ that appears in Cauchy's Lemma is always $\equiv 3 \pmod 8$ when $a$ and $b$ are odd.
*   **Parity Proof**: $4a \equiv 4 \pmod 8$ and $b^2 \equiv 1 \pmod 8$, so $4a - b^2 \equiv 3 \pmod 8$.
*   **Impact**: We only need to prove the representation theorem for the specific case $n \equiv 3 \pmod 8$. This case avoids all powers-of-4 logic and the most difficult exception classes.
*   **Revised Roadmap**: Focus `PolygonalNumberTheorem/Legendre/Minkowski.lean` specifically on $n \equiv 3 \pmod 8$ using a descent from $kn$ to $n$.
