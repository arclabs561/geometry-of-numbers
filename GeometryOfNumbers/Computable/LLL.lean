import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.PiL2
import GeometryOfNumbers.Computable.LLLCore

/-!
# LLL Algorithm Implementation

This file contains a computable implementation of the Lenstra–Lenstra–Lovász (LLL) lattice reduction algorithm.

## Specification
1.  **Gram-Schmidt Orthogonalization**: Basis for computing projections and Lovász conditions.
2.  **Size Reduction**: Reduction of off-diagonal basis entries using integer operations.
3.  **Lovász Condition**: Swapping adjacent basis vectors to satisfy the potential function requirement.
-/

namespace GeometryOfNumbers.Computable

open InnerProductSpace WithLp

-- NOTE: This file mixes (1) noncomputable algorithm code and (2) algebraic invariants about the
-- underlying ℤ-module spanned by the basis rows. Keep lints actionable.

/-- The status of an LLL reduction step. -/
inductive LLLStatus
  | reduced
  | size_reduced
  | swapped

/-- Perform size reduction on vector k with respect to vector j.
    b_k := b_k - round(μ_{k,j}) * b_j -/
noncomputable def size_reduce {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) (μ : ℝ) :
    Matrix (Fin n) (Fin n) ℤ :=
  let q : ℤ := ⌊μ + 1/2⌋
  size_reduceZ B k j q

/-- Gram-Schmidt orthogonalization coefficients μ_{i,j}.
    μ_{i,j} = (b_i, b*_j) / (b*_j, b*_j) -/
noncomputable def gram_schmidt_projections {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : ℝ :=
  let Bstar := gramSchmidt ℝ (fun k => (toLp 2 (B k) : EuclideanSpace ℝ (Fin n)))
  let Bi : EuclideanSpace ℝ (Fin n) := toLp 2 (B i)
  let Bstarj : EuclideanSpace ℝ (Fin n) := Bstar j
  @inner ℝ _ _ Bi Bstarj / ‖Bstarj‖^2

/-- Compute the squared norm of the i-th Gram-Schmidt vector. -/
noncomputable def gso_norm_sq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  let Bstar := gramSchmidt ℝ (fun k => (toLp 2 (B k) : EuclideanSpace ℝ (Fin n)))
  ‖Bstar i‖^2

/-- Compute the potential function D = Π d_i, where d_i is the determinant of the
    sublattice spanned by the first i vectors.
    Each swap step in LLL decreases this value by a factor of at least δ. -/
noncomputable def potential_function {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℝ :=
  let B_real : Matrix (Fin n) (Fin n) ℝ := B.map Int.cast
  (Finset.univ).prod fun i =>
    (gso_norm_sq B_real i) ^ (n - 1 - (i : ℕ))

/-- Check the Lovász condition for two adjacent basis vectors.
    ‖b*_k‖² ≥ (δ - μ_{k,k-1}²) * ‖b*_{k-1}‖² -/
def lovasz_condition (norm_k norm_km1 μ : ℝ) (δ : ℚ) : Prop :=
  norm_k ≥ ((δ : ℝ) - μ^2) * norm_km1

lemma rowSpan_size_reduce {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) (hkj : k ≠ j)
    (q : ℤ) :
    rowSpan (B.updateRow k (B k - q • B j)) = rowSpan B := by
  simpa [size_reduceZ] using rowSpan_size_reduceZ (B := B) (k := k) (j := j) hkj q

/-- Skeleton for the LLL algorithm.
    This will eventually be a computable function that returns a reduced basis. -/
noncomputable def lll_mu_nat {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : ℕ)
    (hk : k < n) (hj : j < n) : ℝ :=
  let B_real : Matrix (Fin n) (Fin n) ℝ := B.map Int.cast
  gram_schmidt_projections (n := n) B_real ⟨k, hk⟩ ⟨j, hj⟩

noncomputable def lll_size_reduce_nat {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : ℕ)
    (hk : k < n) (hj : j < n) : Matrix (Fin n) (Fin n) ℤ :=
  let μ : ℝ := lll_mu_nat (n := n) B k j hk hj
  size_reduce (n := n) B ⟨k, hk⟩ ⟨j, hj⟩ μ

/-- Size-reduce row `k` against all earlier rows `0,1,...,k-1` (in increasing order). -/
noncomputable def lll_size_reduce_all {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : ℕ)
    (hk : k < n) : Matrix (Fin n) (Fin n) ℤ :=
  let js : List (Fin k) := List.ofFn (fun j : Fin k => j)
  js.foldl
    (fun acc (j : Fin k) =>
      have hj : (j : ℕ) < n := Nat.lt_trans j.2 hk
      lll_size_reduce_nat (n := n) acc k (j : ℕ) hk hj)
    B

lemma rowSpan_lll_size_reduce_nat {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : ℕ)
    (hk : k < n) (hj : j < n) (hkj : k ≠ j) :
    rowSpan (lll_size_reduce_nat (n := n) B k j hk hj) = rowSpan B := by
  classical
  -- `lll_size_reduce_nat` is exactly the updateRow of `size_reduce`, so we can reuse `rowSpan_size_reduce`.
  have hkj' : (⟨k, hk⟩ : Fin n) ≠ ⟨j, hj⟩ := by
    intro h
    apply hkj
    exact congrArg Fin.val h
  let μ : ℝ := lll_mu_nat (n := n) B k j hk hj
  let q : ℤ := ⌊μ + 1 / 2⌋
  have hspan : rowSpan (B.updateRow ⟨k, hk⟩ (B ⟨k, hk⟩ - q • B ⟨j, hj⟩)) = rowSpan B :=
    rowSpan_size_reduce (B := B) (k := ⟨k, hk⟩) (j := ⟨j, hj⟩) hkj' q
  -- now rewrite `lll_size_reduce_nat` into that shape
  simpa [lll_size_reduce_nat, lll_mu_nat, μ, size_reduce, q] using hspan

lemma rowSpan_lll_size_reduce_all {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k < n) :
    rowSpan (lll_size_reduce_all (n := n) B k hk) = rowSpan B := by
  classical
  -- unfold and induct over the explicit list of indices `0..k-1`
  unfold lll_size_reduce_all
  set js : List (Fin k) := List.ofFn (fun j : Fin k => j)
  -- the fold preserves rowSpan because each step is a `lll_size_reduce_nat` with `j < k`
  -- (hence `k ≠ j`)
  revert B
  induction js with
  | nil =>
      intro B
      simp
  | cons a tl ih =>
      intro B
      have ha_lt : (a : ℕ) < k := a.2
      have hkj : k ≠ (a : ℕ) := Nat.ne_of_gt ha_lt
      have ha_n : (a : ℕ) < n := Nat.lt_trans ha_lt hk
      -- step preserves rowSpan
      have hstep :
          rowSpan (lll_size_reduce_nat (n := n) B k (a : ℕ) hk ha_n) = rowSpan B :=
        rowSpan_lll_size_reduce_nat (n := n) (B := B) (k := k) (j := (a : ℕ)) hk ha_n hkj
      -- tail fold preserves rowSpan of its starting basis
      have htail :
          rowSpan
              (List.foldl
                (fun acc (j : Fin k) =>
                  lll_size_reduce_nat (n := n) acc k (j : ℕ) hk (Nat.lt_trans j.2 hk))
                (lll_size_reduce_nat (n := n) B k (a : ℕ) hk ha_n) tl) =
            rowSpan (lll_size_reduce_nat (n := n) B k (a : ℕ) hk ha_n) := by
        simpa using ih (B := lll_size_reduce_nat (n := n) B k (a : ℕ) hk ha_n)
      -- combine
      simpa [js, List.foldl, hstep] using htail

noncomputable def lll_reduce_loop {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k : ℕ)
    (limit : ℕ) : Matrix (Fin n) (Fin n) ℤ := by
  classical
  exact
  match limit with
  | 0 => B -- Timeout
  | limit' + 1 =>
    if hk : k < n then
      if h0 : k = 0 then
        lll_reduce_loop B δ 1 limit'
      else
        let B1 : Matrix (Fin n) (Fin n) ℤ := lll_size_reduce_all (n := n) B k hk
        let km1 : ℕ := k - 1
        have hkm1 : km1 < n := by
          -- `k-1 < k < n`
          exact Nat.lt_trans (Nat.pred_lt h0) hk
        let μ : ℝ := lll_mu_nat (n := n) B1 k km1 hk hkm1
        let B1_real : Matrix (Fin n) (Fin n) ℝ := B1.map Int.cast
        let norm_k : ℝ := gso_norm_sq (n := n) B1_real ⟨k, hk⟩
        let norm_km1 : ℝ := gso_norm_sq (n := n) B1_real ⟨km1, hkm1⟩
        if lovasz_condition norm_k norm_km1 μ δ then
          lll_reduce_loop B1 δ (k + 1) limit'
        else
          let B2 := swap_vectors (n := n) B1 ⟨k, hk⟩ ⟨km1, hkm1⟩
          lll_reduce_loop B2 δ km1 limit'
    else B

/-- Main entry point for the LLL algorithm. -/
noncomputable def lll_reduce {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) :
    Matrix (Fin n) (Fin n) ℤ :=
  -- Start with an arbitrary fuel limit for computability
  lll_reduce_loop B δ 1 1000000

theorem rowSpan_lll_reduce_loop {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k : ℕ)
    (limit : ℕ) :
    rowSpan (lll_reduce_loop (n := n) B δ k limit) = rowSpan B := by
  classical
  induction limit generalizing B k with
  | zero =>
      simp [lll_reduce_loop]
  | succ limit ih =>
      by_cases hk : k < n
      · by_cases h0 : k = 0
        · cases h0
          have hk0 : (0 : ℕ) < n := hk
          have := ih (B := B) (k := 1)
          simpa [lll_reduce_loop, hk0] using this
        · let B1 : Matrix (Fin n) (Fin n) ℤ := lll_size_reduce_all (n := n) B k hk
          have hB1 : rowSpan B1 = rowSpan B := by
            simpa [B1] using rowSpan_lll_size_reduce_all (n := n) (B := B) (k := k) hk
          let km1 : ℕ := k - 1
          have hkm1 : km1 < n := by
            exact Nat.lt_trans (Nat.pred_lt h0) hk
          let μ : ℝ := lll_mu_nat (n := n) B1 k km1 hk hkm1
          let B1_real : Matrix (Fin n) (Fin n) ℝ := B1.map Int.cast
          let norm_k : ℝ := gso_norm_sq (n := n) B1_real ⟨k, hk⟩
          let norm_km1 : ℝ := gso_norm_sq (n := n) B1_real ⟨km1, hkm1⟩
          by_cases hL : lovasz_condition norm_k norm_km1 μ δ
          · have := ih (B := B1) (k := k + 1)
            simpa [lll_reduce_loop, hk, h0, B1, km1, hkm1, μ, B1_real, norm_k, norm_km1, hL, hB1] using this
          · let B2 : Matrix (Fin n) (Fin n) ℤ := swap_vectors (n := n) B1 ⟨k, hk⟩ ⟨km1, hkm1⟩
            have hB2 : rowSpan B2 = rowSpan B1 := by
              simpa [B2] using rowSpan_swap_vectors (n := n) (B := B1) ⟨k, hk⟩ ⟨km1, hkm1⟩
            have ih2 := ih (B := B2) (k := km1)
            have : rowSpan (lll_reduce_loop (n := n) B2 δ km1 limit) = rowSpan B := by
              calc
                rowSpan (lll_reduce_loop (n := n) B2 δ km1 limit) = rowSpan B2 := by simpa using ih2
                _ = rowSpan B1 := by simp [hB2]
                _ = rowSpan B := by simp [hB1]
            simpa [lll_reduce_loop, hk, h0, B1, km1, hkm1, μ, B1_real, norm_k, norm_km1, hL, B2] using this
      · simp [lll_reduce_loop, hk]

theorem rowSpan_lll_reduce {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) :
    rowSpan (lll_reduce (n := n) B δ) = rowSpan B := by
  simpa [lll_reduce] using
    rowSpan_lll_reduce_loop (n := n) (B := B) (δ := δ) (k := 1) (limit := 1000000)

/-!
## A useful concrete reducer: 2D Gauss/LLL reduction

Before we have a full, verified LLL implementation in all dimensions, it is still valuable to have
an *actually-operational* reduction routine in the smallest nontrivial case \(n = 2\).

This is essentially Gauss reduction for rank-2 lattices:
- repeatedly size-reduce the second vector by the first using nearest-integer rounding, and
- swap the vectors if that decreases the (Euclidean) norm.

It is **noncomputable** (uses real inner products + `floor`), but it is not a no-op, and it is
useful as an executable “reality check” for later LLL work.
-/

noncomputable def lll_reduce2_step (B : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  let i0 : Fin 2 := 0
  let i1 : Fin 2 := 1
  let B_real : Matrix (Fin 2) (Fin 2) ℝ := B.map Int.cast
  let μ : ℝ := gram_schmidt_projections (n := 2) B_real i1 i0
  let q : ℤ := ⌊μ + 1 / 2⌋
  let B' : Matrix (Fin 2) (Fin 2) ℤ :=
    if q = 0 then
      B
    else
      B.updateRow i1 (B i1 - q • B i0)
  -- swap if the new second vector is shorter than the first
  let v0 : EuclideanSpace ℝ (Fin 2) := toLp 2 ((B'.map Int.cast) i0)
  let v1 : EuclideanSpace ℝ (Fin 2) := toLp 2 ((B'.map Int.cast) i1)
  if ‖v1‖ < ‖v0‖ then
    swap_vectors B' i0 i1
  else
    B'

noncomputable def lll_reduce2 (B : Matrix (Fin 2) (Fin 2) ℤ) (limit : ℕ := 200) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  -- Default fuel is intentionally small: this is meant as a quick reducer / smoke tool, not a
  -- fully verified termination story for all inputs.
  match limit with
  | 0 => B
  | limit' + 1 =>
      let B' := lll_reduce2_step B
      if B' = B then
        B
      else
        lll_reduce2 B' limit'

end GeometryOfNumbers.Computable
