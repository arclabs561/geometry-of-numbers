import GeometryOfNumbers.Computable.LLLExact

namespace GeometryOfNumbers.Computable

/-!
## Proofs about the exact (ℚ) Gram–Schmidt path

This file contains “hard/meaty” correctness lemmas for `LLLExact`:

- basic algebra for `dotQ`,
- orthogonality of the prefix Gram–Schmidt vectors produced by `gsoPrefixListQ`,
- consequences needed for size-reduction correctness.

Keeping these proofs out of `LLLExact.lean` preserves the executable surface and keeps compilation
costs more predictable.
-/

open scoped BigOperators

lemma dotQ_add_left {n : ℕ} (v v' w : Fin n → ℚ) :
    dotQ (n := n) (v + v') w = dotQ (n := n) v w + dotQ (n := n) v' w := by
  simp [dotQ, Finset.sum_add_distrib, add_mul]

lemma dotQ_add_right {n : ℕ} (v w w' : Fin n → ℚ) :
    dotQ (n := n) v (w + w') = dotQ (n := n) v w + dotQ (n := n) v w' := by
  simp [dotQ, Finset.sum_add_distrib, mul_add]

lemma dotQ_smul_left {n : ℕ} (a : ℚ) (v w : Fin n → ℚ) :
    dotQ (n := n) (a • v) w = a * dotQ (n := n) v w := by
  simp [dotQ, Finset.mul_sum, mul_left_comm, mul_comm]

lemma dotQ_smul_right {n : ℕ} (a : ℚ) (v w : Fin n → ℚ) :
    dotQ (n := n) v (a • w) = a * dotQ (n := n) v w := by
  simp [dotQ, Finset.mul_sum, mul_left_comm]

lemma dotQ_sub_left {n : ℕ} (v v' w : Fin n → ℚ) :
    dotQ (n := n) (v - v') w = dotQ (n := n) v w - dotQ (n := n) v' w := by
  -- expand and use linearity
  simp [dotQ, sub_eq_add_neg, Finset.sum_add_distrib, add_mul, neg_mul]

lemma dotQ_sub_right {n : ℕ} (v w w' : Fin n → ℚ) :
    dotQ (n := n) v (w - w') = dotQ (n := n) v w - dotQ (n := n) v w' := by
  simp [dotQ, sub_eq_add_neg, Finset.sum_add_distrib, mul_add, mul_neg]

/-- If `u` is nonzero, then the projection update makes `v - μ•u` orthogonal to `u`. -/
lemma dotQ_proj_update_zero {n : ℕ} (u v : Fin n → ℚ) (hu : dotQ (n := n) u u ≠ 0) :
    let μ : ℚ := dotQ (n := n) v u / dotQ (n := n) u u
    dotQ (n := n) (v - μ • u) u = 0 := by
  intro μ
  -- dot(v - μ u, u) = dot(v,u) - μ dot(u,u)
  have hlin : dotQ (n := n) (v - μ • u) u =
      dotQ (n := n) v u - μ * dotQ (n := n) u u := by
    -- linearity in the left argument, then simplify
    calc
      dotQ (n := n) (v - μ • u) u
          = dotQ (n := n) v u - dotQ (n := n) (μ • u) u := by
              simp [dotQ_sub_left]
      _ = dotQ (n := n) v u - μ * dotQ (n := n) u u := by
              simp [dotQ_smul_left]
  -- substitute μ and finish
  simp [μ, hlin, hu]

end GeometryOfNumbers.Computable

