import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Gauss-Bhargava Composition Primitives

This file defines the basic structures for Bhargava's higher composition laws,
specifically focused on the "cube of integers" representation.

## Mathematical Context
Manjul Bhargava (2004) generalized Gauss's composition of binary quadratic forms
by considering cubes of integers (2x2x2 arrays). Each such cube gives rise to
three binary quadratic forms sharing the same discriminant.

## Implementation Details
- `IntegerCube`: A 2x2x2 array of integers.
- `slice_bqf`: The binary quadratic form coefficients obtained by taking the determinant
  of a linear combination of faces.
-/

namespace GeometryOfNumbers.Composition

/-- A 2x2x2 cube of integers. -/
def IntegerCube := Fin 2 → Fin 2 → Fin 2 → ℤ

/-- Extract a 2x2 face of the cube along a specific dimension. -/
def face (A : IntegerCube) (dim : Fin 3) (index : Fin 2) : Matrix (Fin 2) (Fin 2) ℤ :=
  match dim with
  | 0 => fun i j => A index i j
  | 1 => fun i j => A i index j
  | 2 => fun i j => A i j index

/-- The determinant of a 2x2 matrix of integers. -/
def det2x2 (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

/-- Coefficients of a binary quadratic form \(ax^2 + bxy + cy^2\). -/
structure BinaryQuadraticForm where
  a : ℤ
  b : ℤ
  c : ℤ

/-- Evaluate a binary quadratic form on `(x,y)`. -/
def BinaryQuadraticForm.eval (Q : BinaryQuadraticForm) (x y : ℤ) : ℤ :=
  Q.a * x ^ 2 + Q.b * x * y + Q.c * y ^ 2

/-- The binary quadratic form coefficients arising from a specific dimension of the cube.

If `M0, M1` are the two faces, then the associated form is:

\[
Q(x,y) = -\det(M_0 x + M_1 y) = ax^2 + bxy + cy^2.
\]

This file only defines the coefficients; the “equal discriminant across slices” identity lives
in `Experiments/` until we commit to a full formal proof.
-/
def slice_bqf (A : IntegerCube) (dim : Fin 3) : BinaryQuadraticForm :=
  let M0 := face A dim 0
  let M1 := face A dim 1
  let a := -det2x2 M0
  let c := -det2x2 M1
  -- b = -(det(M0 + M1) - det(M0) - det(M1))
  let b := -(det2x2 (M0 + M1) - det2x2 M0 - det2x2 M1)
  { a := a, b := b, c := c }

/-- The discriminant of a binary quadratic form ax^2 + bxy + cy^2 is b^2 - 4ac. -/
def discriminant (Q : BinaryQuadraticForm) : ℤ :=
  Q.b ^ 2 - 4 * Q.a * Q.c

end GeometryOfNumbers.Composition
