import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import PolygonalNumberTheorem.LowDim

/-!
# Ternary Quadratic Forms

Definitions and basic properties of ternary quadratic forms over `ℤ`.
This structure is central to the Nathanson/Pollack-Schorn proof of the Three-Square Theorem.
-/

structure TernaryQF where
  a11 : ℤ
  a12 : ℤ
  a13 : ℤ
  a22 : ℤ
  a23 : ℤ
  a33 : ℤ
  deriving DecidableEq, Inhabited, Repr

namespace TernaryQF

/-- Convert to a symmetric Matrix (Fin 3) (Fin 3) ℤ.
    Q(x,y,z) = a11 x² + a22 y² + a33 z² + 2 a12 xy + 2 a13 xz + 2 a23 yz
-/
def toMatrix (F : TernaryQF) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![F.a11, F.a12, F.a13;
     F.a12, F.a22, F.a23;
     F.a13, F.a23, F.a33]

/-- Evaluate the form at a vector `v`. -/
def eval (F : TernaryQF) (v : Fin 3 → ℤ) : ℤ :=
  let x := v 0
  let y := v 1
  let z := v 2
  F.a11 * x^2 + F.a22 * y^2 + F.a33 * z^2 +
  2 * F.a12 * x * y + 2 * F.a13 * x * z + 2 * F.a23 * y * z

/-- The determinant of the form (determinant of its matrix). -/
def det (F : TernaryQF) : ℤ :=
  LowDim.det_three
    F.a11 F.a12 F.a13
    F.a12 F.a22 F.a23
    F.a13 F.a23 F.a33

/-- Equivalence of forms: G = A^T F A for some A ∈ SL₃(ℤ). -/
def Equiv (F G : TernaryQF) : Prop :=
  ∃ A : Matrix.SpecialLinearGroup (Fin 3) ℤ,
    G.toMatrix = A.1.transpose * F.toMatrix * A.1

/-- Positive definiteness: Q(v) > 0 for all v ≠ 0. -/
def PosDef (F : TernaryQF) : Prop :=
  ∀ v : Fin 3 → ℤ, v ≠ 0 → F.eval v > 0

/-- The standard sum of three squares form: x² + y² + z². -/
def sumThreeSquares : TernaryQF :=
  { a11 := 1, a12 := 0, a13 := 0
    a22 := 1, a23 := 0
    a33 := 1 }

lemma sumThreeSquares_det : sumThreeSquares.det = 1 := by
  simp [sumThreeSquares, det, LowDim.det_three]

/-- A ternary quadratic form is "reduced" (in the sense of Seeber/Eisenstein).
    This is a canonical representative for its equivalence class. -/
def IsReduced (F : TernaryQF) : Prop :=
  F.a11 > 0 ∧
  0 ≤ 2 * F.a12 ∧ 2 * F.a12 ≤ F.a11 ∧
  0 ≤ 2 * F.a13 ∧ 2 * F.a13 ≤ F.a11 ∧
  F.a11 ≤ F.a22 ∧
  0 ≤ 2 * F.a23 ∧ 2 * F.a23 ≤ F.a22 ∧
  F.a22 ≤ F.a33

/-- Hermite's constant for ternary forms implies a11 * a22 * a33 ≤ 2 * det for reduced forms. -/
lemma reduced_coeff_bound (F : TernaryQF) (_hpos : F.PosDef) (_hred : F.IsReduced) :
    F.a11 * F.a22 * F.a33 ≤ 2 * F.det := by
  sorry

theorem reduced_det_one_is_sum_three_squares (F : TernaryQF) (hpos : F.PosDef) 
    (hred : F.IsReduced) (hdet : F.det = 1) :
    F = sumThreeSquares := by
  sorry

/-- Every positive definite ternary form of determinant 1 is equivalent 
    to the sum of three squares. -/
theorem equiv_sumThreeSquares_of_det_one (F : TernaryQF) (hpos : F.PosDef) (hdet : F.det = 1) :
    F.Equiv sumThreeSquares := by
  sorry

/-- The discriminant of a ternary quadratic form. -/
def disc (F : TernaryQF) : ℤ := F.det

/-- Adjoint (or reciprocal) form of a ternary form. -/
def adjoint (F : TernaryQF) : TernaryQF :=
  { a11 := F.a22 * F.a33 - F.a23 ^ 2
    a12 := F.a13 * F.a23 - F.a12 * F.a33
    a13 := F.a12 * F.a23 - F.a13 * F.a22
    a22 := F.a11 * F.a33 - F.a13 ^ 2
    a23 := F.a12 * F.a13 - F.a11 * F.a23
    a33 := F.a11 * F.a22 - F.a12 ^ 2 }

end TernaryQF
