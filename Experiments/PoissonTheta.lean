import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Poisson summation → theta-style identity (experiment)

This file is a tiny “bridge” experiment: it exercises Mathlib’s Poisson summation machinery by
importing the Gaussian specialization, which already proves a Jacobi theta transformation formula.

Why this belongs here:
- It demonstrates that Poisson summation is “available infrastructure” in Mathlib.
- It suggests a path from GoN lattice sums to analytic identities (theta series, counting).
-/

namespace GeometryOfNumbers.Experiments

open Real

-- Jacobi theta transformation (one common normalization).
example {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Real.exp (-Real.pi * a * (n : ℝ) ^ 2)) =
      (1 : ℝ) / a ^ (1 / 2 : ℝ) * (∑' n : ℤ, Real.exp (-Real.pi / a * (n : ℝ) ^ 2)) := by
  simpa using Real.tsum_exp_neg_mul_int_sq ha

end GeometryOfNumbers.Experiments

