import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace LowDim

variable {R : Type*} [CommRing R]

/-!
### Explicit Low-Dimensional Matrix Operations

Mathlib's `Matrix.det` is defined generally via permutations. For 2x2 and 3x3 matrices,
explicit formulas are often more convenient for algebraic manipulation and porting
proofs from pen-and-paper sources.
-/

section TwoByTwo

def det_two (a b c d : R) : R := a * d - b * c

/-- The determinant of a 2x2 matrix matches the explicit formula. -/
lemma det_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  simp [Matrix.det_fin_two]

end TwoByTwo

section ThreeByThree

/-- Explicit Rule of Sarrus for 3x3 determinant. -/
def det_three (a11 a12 a13 a21 a22 a23 a31 a32 a33 : R) : R :=
  a11 * a22 * a33 + a12 * a23 * a31 + a13 * a21 * a32 -
  a13 * a22 * a31 - a12 * a21 * a33 - a11 * a23 * a32

/-- The determinant of a 3x3 matrix matches the explicit formula. -/
lemma det_fin_three (A : Matrix (Fin 3) (Fin 3) R) :
    A.det = det_three
      (A 0 0) (A 0 1) (A 0 2)
      (A 1 0) (A 1 1) (A 1 2)
      (A 2 0) (A 2 1) (A 2 2) := by
  simp [Matrix.det_fin_three, det_three]
  ring

end ThreeByThree

end LowDim
