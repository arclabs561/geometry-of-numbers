# Polygonal Number Theorem Project

This repository targets the formalization of **Legendre's Three-Square Theorem** and the **Fermat/Cauchy Polygonal Number Theorem** in Lean 4.

## Goals

1.  **Legendre's Three-Square Theorem**: Formalize the missing link in Mathlib's sum-of-squares trilogy (2, 3, 4).
    *   Statement: `n` is a sum of 3 squares iff `n ≠ 4^a(8k+7)`.
    *   Strategy: Ankeny's elementary proof using Dirichlet's Theorem on Arithmetic Progressions.

2.  **Cauchy's Lemma**: Prove the existence of solutions to the system `k = Σ x_i^2`, `s = Σ x_i` under parity constraints.

3.  **Polygonal Number Theorem**: Prove that every `n` is a sum of `s` `s`-gonal numbers.

## Current Status

*   [ ] `SumThreeSquares.lean`: Theorem statement defined. Proof pending.
*   [ ] `Polygonal.lean`: Not started.

## References

*   Legendre, A.-M. (1798). *Essai sur la théorie des nombres*.
*   Cauchy, A. L. (1813). *Démonstration du théorème général de Fermat sur les nombres polygones*.
*   Ankeny, N. C. (1957). *Sums of three squares*. Proceedings of the American Mathematical Society.
*   Nathanson, M. B. (1987). *A short proof of Cauchy's polygonal number theorem*.
