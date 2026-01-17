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

## 3. Discovery: Cauchy's proof only needs \(n \equiv 3 \pmod 8\)
*   **Discovery**: The integer $4a - b^2$ that appears in Cauchy's Lemma is always $\equiv 3 \pmod 8$ when $a$ and $b$ are odd.
*   **Parity Proof**: $4a \equiv 4 \pmod 8$ and $b^2 \equiv 1 \pmod 8$, so $4a - b^2 \equiv 3 \pmod 8$.
*   **Impact**: We only need to prove the representation theorem for the specific case $n \equiv 3 \pmod 8$. This case avoids all powers-of-4 logic and the most difficult exception classes.
*   **Revised Roadmap**: Focus on the \(n \equiv 3 \pmod 8\) case, prove it via Ankeny/Minkowski descent,
    then use standard reductions to the full exception characterization.

## 4. Evidence scaffolds (experiments that reduce proof friction)

These experiments are “engineering evidence”: they do not prove the theorem, but they pin down the
exact Mathlib lemma shapes we need and sanity-check the intended arithmetic.

* **`Experiments/CheckZMod.lean` (Lean)**: compiles small bridge lemmas used by `Legendre/Ankeny.lean`:
  - moving between `ZMod` equalities and `Int.ModEq` congruences via `ZMod.intCast_eq_intCast_iff`;
  - combining congruences via `Int.modEq_and_modEq_iff_modEq_mul`.

* **`Experiments/ankeny_check.py` (Python)**: brute searches small instances of the quadratic form
  \(2qx^2 + y^2 + nz^2 = 2nq\) and checks whether \(n - x^2\) is a sum of two squares.
  This is useful for catching sign mistakes before formalizing descent.
