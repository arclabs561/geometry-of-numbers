import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# Rational LLL Probing

Experimental implementation of LLL steps using rational arithmetic.
-/

namespace GeometryOfNumbers.Experiments

open Matrix

/-- Round a rational number to the nearest integer. -/
def round_rat (q : ℚ) : ℤ := ⌊q + 1/2⌋

/-- Size reduce vector k wrt vector j in a rational basis. -/
def size_reduce_step {n : ℕ} (B : Matrix (Fin n) (Fin n) ℚ) (k j : Fin n) (μ : ℚ) : 
    Matrix (Fin n) (Fin n) ℚ :=
  let q := round_rat μ
  B.updateRow k (B k - (q : ℚ) • B j)

/-- Test on a 2D basis. -/
def test_basis : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]

example : size_reduce_step test_basis 0 1 (1 : ℚ) = !![1, 0; 0, 1] := by
  simp [size_reduce_step, test_basis, round_rat]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp; try norm_num)

end GeometryOfNumbers.Experiments
