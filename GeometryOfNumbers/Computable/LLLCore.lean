import Mathlib.LinearAlgebra.Matrix.RowCol

namespace GeometryOfNumbers.Computable

/-!
## LLL core (computable)

This file contains only the **computable kernel** for lattice-basis operations used by LLL:

- swapping two rows
- replacing one row by `row_k - q • row_j` for an integer `q`

and algebraic invariants about the induced ℤ-span of the rows.

The noncomputable / analytic parts (Gram–Schmidt over ℝ, etc.) live in `LLL.lean`.
-/

/-- The ℤ-span of the row vectors of `B`. -/
def rowSpan {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.span ℤ (Set.range B)

lemma row_mem_rowSpan {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    B i ∈ rowSpan B := by
  exact Submodule.subset_span ⟨i, rfl⟩

/-- Swap two rows (as a precomposition by `Equiv.swap`). -/
def swap_vectors {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) :
    Matrix (Fin n) (Fin n) ℤ :=
  fun i => B (Equiv.swap k j i)

/-- Replace row `k` by `row_k - q • row_j`. -/
def size_reduceZ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) (q : ℤ) :
    Matrix (Fin n) (Fin n) ℤ :=
  B.updateRow k (B k - q • B j)

lemma rowSpan_swap_vectors {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) :
    rowSpan (swap_vectors B k j) = rowSpan B := by
  have hrange : Set.range (swap_vectors B k j) = Set.range B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Equiv.swap k j i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Equiv.swap k j i, by simp [swap_vectors]⟩
  simp [rowSpan, hrange]

lemma rowSpan_size_reduceZ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) (hkj : k ≠ j)
    (q : ℤ) :
    rowSpan (size_reduceZ B k j q) = rowSpan B := by
  -- Replace generator `B k` by `B k - q • B j` (keeping `B j`): span unchanged.
  let B' := size_reduceZ B k j q
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    by_cases hiK : i = k
    · cases hiK
      have hk : B k ∈ rowSpan B := row_mem_rowSpan B k
      have hj' : B j ∈ rowSpan B := row_mem_rowSpan B j
      have : B k - q • B j ∈ rowSpan B := (rowSpan B).sub_mem hk ((rowSpan B).smul_mem q hj')
      simpa [B', size_reduceZ, Matrix.updateRow_self] using this
    · simpa [B', size_reduceZ, Matrix.updateRow_ne, hiK] using (row_mem_rowSpan B i)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    by_cases hiK : i = k
    · cases hiK
      have hk' : B' k ∈ rowSpan B' := row_mem_rowSpan B' k
      have hj' : B' j ∈ rowSpan B' := row_mem_rowSpan B' j
      have hsum : B' k + q • B' j ∈ rowSpan B' := (rowSpan B').add_mem hk' ((rowSpan B').smul_mem q hj')
      have hjk : j ≠ k := Ne.symm hkj
      -- `B' k = B k - q•B j`, `B' j = B j`
      simpa [B', size_reduceZ, Matrix.updateRow_self, Matrix.updateRow_ne, hjk, sub_add_cancel] using hsum
    · exact Submodule.subset_span ⟨i, by simp [size_reduceZ, Matrix.updateRow_ne, hiK]⟩

end GeometryOfNumbers.Computable

