import GeometryOfNumbers.Computable.LLLExact
import GeometryOfNumbers.Computable.LLLExactProofs
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Algebra.BigOperators.Fin

-- This file is intentionally proof-heavy; keep build output usable by silencing
-- style-only linters that otherwise dominate logs during development.
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

namespace GeometryOfNumbers.Computable

/-!
## Termination scaffolding (exact / ℚ GS)

This file is the start of the “hard” LLL story: a potential-function argument for termination.

The goal is to keep this development:
- **incremental** (small lemmas that compile),
- **backend-free** (pure Lean/Mathlib),
- and **admission-free** (no placeholder proofs).

See `doc/LLLTerminationRoadmap.md` for the proof plan.
-/

/-- The classic LLL potential, specialized to the exact-ℚ Gram–Schmidt track.

\[
\Phi(B) := \prod_{i=0}^{n-1} \bigl(\|b_i^\*\|^2\bigr)^{(n-1-i)}.
\]

We keep it in `ℚ` so later proofs can stay in rational arithmetic.
-/
def potentialQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℚ :=
  (Finset.univ : Finset (Fin n)).prod fun i =>
    (gsoNormSqQ (n := n) B i) ^ (n - 1 - i.1)

@[simp] lemma potentialQ_def {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    potentialQ (n := n) B =
      (Finset.univ : Finset (Fin n)).prod (fun i => (gsoNormSqQ (n := n) B i) ^ (n - 1 - i.1)) := by
  rfl

/-!
### First “leaf” lemmas

These are tiny facts we’ll reuse repeatedly once the swap-step inequality is in view.
-/

lemma gsoNormSqQ_nonneg {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (0 : ℚ) ≤ gsoNormSqQ (n := n) B i := by
  classical
  -- `dotQ v v` is a sum of squares.
  simp [gsoNormSqQ, dotQ]
  exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (gsoAtQ (n := n) B i j))

lemma gsoVectorForKPrefix_append_singleton {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ))
    (u : Fin n → ℚ) :
    gsoVectorForKPrefix (n := n) bk (us ++ [u]) =
      gsoVectorForKPrefix (n := n) bk us - (muQPrefix (n := n) bk u) • u := by
  -- `foldl` over `us ++ [u]` does the `us` pass, then one last update at `u`.
  simp [gsoVectorForKPrefix, List.foldl_append, muQPrefix]

/-!
### Prefix “volume squared” via GS norms

For our fixed order `0,1,2,...`, the squared volume of the prefix lattice can be expressed as the
product of squared GS norms:

`V_k(B) := ∏_{i=0}^{k-1} ‖b_i^*‖²`.

This is the key object that *actually* shrinks on an adjacent swap at index `k-1`.
-/

def prefixProdNormSqQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) : ℚ :=
  (Finset.univ : Finset (Fin k)).prod (fun i => gsoNormSqQ (n := n) B ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩)

/-!
### A prefix-volume potential (order-invariant by construction)

For termination it is convenient to use the **product of prefix volumes**:

\[
\Psi(B) := \prod_{k=0}^{n-1} V_k(B), \qquad V_k(B) := \prod_{i=0}^{k-1}\|b_i^\*\|^2.
\]

Note `V_0 = 1`, so including `k=0` is harmless.

This potential is equivalent to the classic exponent-weighted `potentialQ`, but it is easier to
reason about swaps because (via the Gram-determinant bridge) each `V_k` is order-invariant.
-/

def potentialVQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℚ :=
  (Finset.univ : Finset (Fin n)).prod (fun k => prefixProdNormSqQ (n := n) B k.1 (Nat.le_of_lt k.2))

@[simp] lemma potentialVQ_def {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    potentialVQ (n := n) B =
      (Finset.univ : Finset (Fin n)).prod (fun k => prefixProdNormSqQ (n := n) B k.1 (Nat.le_of_lt k.2)) := by
  rfl

@[simp] lemma prefixProdNormSqQ_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    prefixProdNormSqQ (n := n) B 0 (Nat.zero_le n) = 1 := by
  simp [prefixProdNormSqQ]

lemma prefixProdNormSqQ_succ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k + 1 ≤ n) :
    prefixProdNormSqQ (n := n) B (k + 1) hk =
      prefixProdNormSqQ (n := n) B k (Nat.le_trans (Nat.le_succ k) hk) *
        gsoNormSqQ (n := n) B ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ := by
  classical
  -- split `Fin (k+1)` into `Fin k` (castSucc) plus the last index
  -- (`Fin.prod_univ_castSucc` is the “add at end” decomposition)
  simpa [prefixProdNormSqQ, mul_assoc] using
    (Fin.prod_univ_castSucc (n := k) (f := fun i : Fin (k + 1) =>
      gsoNormSqQ (n := n) B ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩))

lemma prefixProdNormSqQ_nonneg {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    (0 : ℚ) ≤ prefixProdNormSqQ (n := n) B k hk := by
  classical
  -- product of nonnegative factors
  refine Finset.prod_nonneg ?_
  intro i hi
  simpa using gsoNormSqQ_nonneg (n := n) B ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩

/-!
### A prefix Gram matrix (order-invariant “ground truth”)

For the first `k` rows of `B` (viewed in `ℚ^n`), define the `k×k` Gram matrix:

`G_{ij} = dotQ(row_i, row_j)`.

This is the *order-invariant* object whose determinant is the squared volume of the parallelepiped
spanned by the first `k` rows.

We will later relate `det (gramPrefixQ B k)` to `prefixProdNormSqQ B k` (GS product).
Once that bridge exists, we get:
- invariance under `swap_vectors` and `size_reduceZ` “for free” (determinant invariance),
- and a discrete lower bound for swap-counting (integer determinant).
-/

def gramPrefixQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    Matrix (Fin k) (Fin k) ℚ :=
  fun i j =>
    dotQ (n := n)
      (rowQ (n := n) B (Fin.castLE hk i))
      (rowQ (n := n) B (Fin.castLE hk j))

/-!
For some termination lemmas it is convenient to talk about the `k×n` matrix of the first `k` rows of
`B` (cast to `ℚ`).
-/

def prefixRowsQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    Matrix (Fin k) (Fin n) ℚ :=
  fun i j => rowQ (n := n) B (Fin.castLE hk i) j

@[simp] lemma prefixRowsQ_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n)
    (i : Fin k) (j : Fin n) :
    prefixRowsQ (n := n) B k hk i j = rowQ (n := n) B (Fin.castLE hk i) j := by
  rfl

@[simp] lemma gramPrefixQ_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    gramPrefixQ (n := n) B k hk i j =
      ∑ t : Fin n, prefixRowsQ (n := n) B k hk i t * prefixRowsQ (n := n) B k hk j t := by
  simp [gramPrefixQ, prefixRowsQ, dotQ]

lemma gramPrefixQ_eq_prefixRowsQ_mul_transpose
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    gramPrefixQ (n := n) B k hk =
      prefixRowsQ (n := n) B k hk * (prefixRowsQ (n := n) B k hk).transpose := by
  classical
  ext i j
  -- unfold the matrix product and match `gramPrefixQ_apply`
  simp [gramPrefixQ_apply, Matrix.mul_apply, Matrix.transpose_apply]

/-!
### The GS-row matrix for a prefix

`gsoRowsQ B k` is the `k×n` matrix whose `i`th row is the Gram–Schmidt vector `gsoAtQ B i`.
This is the “orthogonalized rows” object that we want to compare against `prefixRowsQ`.
-/

def gsoRowsQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    Matrix (Fin k) (Fin n) ℚ :=
  fun i j => gsoAtQ (n := n) B (Fin.castLE hk i) j

@[simp] lemma gsoRowsQ_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n)
    (i : Fin k) (j : Fin n) :
    gsoRowsQ (n := n) B k hk i j = gsoAtQ (n := n) B (Fin.castLE hk i) j := by
  rfl

lemma gsoRowsQ_mul_transpose_apply
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) (i j : Fin k) :
    (gsoRowsQ (n := n) B k hk * (gsoRowsQ (n := n) B k hk).transpose) i j =
      dotQ (n := n)
        (gsoAtQ (n := n) B (Fin.castLE hk i))
        (gsoAtQ (n := n) B (Fin.castLE hk j)) := by
  classical
  simp [gsoRowsQ, dotQ, Matrix.mul_apply, Matrix.transpose_apply]

/-!
### Orthogonality of `gsoAtQ` under `RowLIQ`

We’ll use these to show that `gsoRowsQ * gsoRowsQᵀ` is diagonal (hence has determinant equal
to the product of the `gsoNormSqQ` terms).
-/

lemma gsoAtQ_mem_gsoPrefixListQ_succ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    gsoAtQ (n := n) B i ∈
      gsoPrefixListQ (n := n) B (i.1 + 1) (Nat.succ_le_of_lt i.2) := by
  classical
  -- `gsoAtQ` is `getD i` from the `(i+1)` prefix list, and that index is in-bounds.
  let l : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B (i.1 + 1) (Nat.succ_le_of_lt i.2)
  have hlen : l.length = i.1 + 1 := by
    dsimp [l]
    exact
      gsoPrefixListQ_length (n := n) (B := B) (k := i.1 + 1) (hk := Nat.succ_le_of_lt i.2)
  have hi_lt : i.1 < l.length := by simpa [hlen]
  -- turn `getD` into `get`, then use `List.get_mem`.
  let ii : Fin l.length := ⟨i.1, hi_lt⟩
  have hgetD : l.getD i.1 (zeroVecQ (n := n)) = l.get ii := by
    -- `getD_eq_get` is the cleanest form (avoids `getElem` notation)
    exact List.getD_eq_get (l := l) (d := zeroVecQ (n := n)) ii
  -- `gsoAtQ` definition
  have hgso : gsoAtQ (n := n) B i = l.getD i.1 (zeroVecQ (n := n)) := by
    rfl
  -- finish by rewriting and applying `List.get_mem` (avoid `simpa` here; it can over-simplify).
  change gsoAtQ (n := n) B i ∈ l
  rw [hgso, hgetD]
  exact List.get_mem l ii

lemma dotQ_gsoAtQ_lt_eq_zero_of_RowLIQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) (hij : i.1 < j.1)
    (hli : RowLIQ (n := n) B) :
    dotQ (n := n) (gsoAtQ (n := n) B i) (gsoAtQ (n := n) B j) = 0 := by
  classical
  -- work with `us0 = gsoPrefixListQ B j` (the list of GS vectors strictly before `j`)
  let us0 : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B j.1 (Nat.le_of_lt j.2)
  -- nondegeneracy for this prefix from `RowLIQ`
  have hnz_us0 : ∀ u ∈ us0, dotQ (n := n) u u ≠ 0 := by
    -- `HNZAt` gives exactly this
    have hnz : HNZAt (n := n) B j.1 j.2 := HNZAt_of_RowLIQ (n := n) (B := B) (k := j.1) j.2 hli
    simpa [HNZAt, us0]
      using hnz
  have horth_us0 : us0.Pairwise (fun u w => dotQ (n := n) u w = 0) :=
    gsoPrefixListQ_pairwise_orth (n := n) (B := B) j.1 (Nat.le_of_lt j.2) hnz_us0
  -- `gsoAtQ j` is the GS vector computed from `us0`
  have hgsoj :
      gsoAtQ (n := n) B j = gsoVectorForKPrefix (n := n) (rowQ (n := n) B j) us0 := by
    simpa [us0] using (gsoAtQ_eq_gsoVectorForKPrefix (n := n) (B := B) j)
  -- show `gsoAtQ i ∈ us0`
  have hi_mem_succ :
      gsoAtQ (n := n) B i ∈ gsoPrefixListQ (n := n) B (i.1 + 1) (Nat.succ_le_of_lt i.2) :=
    gsoAtQ_mem_gsoPrefixListQ_succ (n := n) (B := B) i
  have hi_succ_le_j : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hij
  have hi_mem : gsoAtQ (n := n) B i ∈ us0 := by
    -- lift membership through prefix nesting
    have hj_le : j.1 ≤ n := Nat.le_of_lt j.2
    have hi_succ_le_n : i.1 + 1 ≤ n := Nat.le_trans hi_succ_le_j hj_le
    exact
      gsoPrefixListQ_mem_of_le (n := n) (B := B)
        (m := i.1 + 1) (k := j.1) hi_succ_le_j hi_succ_le_n (Nat.le_of_lt j.2) _ hi_mem_succ
  -- use orthogonality of the GS fold result against any `u ∈ us0`
  have hz : dotQ (n := n) (gsoAtQ (n := n) B j) (gsoAtQ (n := n) B i) = 0 := by
    -- rewrite to `gsoVectorForKPrefix` and apply the general orthogonality lemma
    rw [hgsoj]
    exact dotQ_gsoVectorForKPrefix_mem_eq_zero (n := n)
      (bk := rowQ (n := n) B j) (us := us0) horth_us0 hnz_us0 _ hi_mem
  -- symmetric dot-product
  simpa [dotQ_comm] using hz

lemma gsoRowsQ_mul_transpose_eq_diagonal_of_RowLIQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k : Nat) (hk : k ≤ n) (hli : RowLIQ (n := n) B) :
    gsoRowsQ (n := n) B k hk * (gsoRowsQ (n := n) B k hk).transpose =
      Matrix.diagonal (fun i : Fin k => gsoNormSqQ (n := n) B (Fin.castLE hk i)) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    -- diagonal entry is just the norm-squared
    simp [gsoRowsQ_mul_transpose_apply, gsoNormSqQ, Matrix.diagonal]
  · -- off-diagonal entry is zero by orthogonality of distinct GS vectors
    have hne_val : i.1 ≠ j.1 := by
      intro hval
      exact hij (Fin.ext hval)
    have hlt_or : i.1 < j.1 ∨ j.1 < i.1 := lt_or_gt_of_ne hne_val
    have hz : dotQ (n := n)
        (gsoAtQ (n := n) B (Fin.castLE hk i))
        (gsoAtQ (n := n) B (Fin.castLE hk j)) = 0 := by
      cases hlt_or with
      | inl hlt =>
          -- cast preserves `val`
          simpa using
            (dotQ_gsoAtQ_lt_eq_zero_of_RowLIQ (n := n) (B := B)
              (i := Fin.castLE hk i) (j := Fin.castLE hk j) (by simpa using hlt) hli)
      | inr hgt =>
          -- flip with symmetry
          have : dotQ (n := n)
              (gsoAtQ (n := n) B (Fin.castLE hk j))
              (gsoAtQ (n := n) B (Fin.castLE hk i)) = 0 := by
            simpa using
              (dotQ_gsoAtQ_lt_eq_zero_of_RowLIQ (n := n) (B := B)
                (i := Fin.castLE hk j) (j := Fin.castLE hk i) (by simpa using hgt) hli)
          simpa [dotQ_comm] using this
    -- finish: the matrix product entry is exactly this dot-product
    simp [gsoRowsQ_mul_transpose_apply, hz, Matrix.diagonal, hij]

lemma det_gsoRowsQ_mul_transpose_eq_prefixProdNormSqQ_of_RowLIQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k : Nat) (hk : k ≤ n) (hli : RowLIQ (n := n) B) :
    Matrix.det (gsoRowsQ (n := n) B k hk * (gsoRowsQ (n := n) B k hk).transpose)
      =
      prefixProdNormSqQ (n := n) B k hk := by
  classical
  -- the Gram of the GS rows is diagonal, so determinant is the product of diagonal entries
  have hdiag :=
    gsoRowsQ_mul_transpose_eq_diagonal_of_RowLIQ (n := n) (B := B) (k := k) hk hli
  -- rewrite to `det (diagonal d) = ∏ d`
  have : Matrix.det (gsoRowsQ (n := n) B k hk * (gsoRowsQ (n := n) B k hk).transpose)
        = ∏ i : Fin k, gsoNormSqQ (n := n) B (Fin.castLE hk i) := by
    -- rewrite the Gram as a diagonal matrix, then apply `det_diagonal`
    rw [hdiag]
    exact
      (Matrix.det_diagonal (n := Fin k) (R := ℚ)
        (d := fun i : Fin k => gsoNormSqQ (n := n) B (Fin.castLE hk i)))
  -- and `prefixProdNormSqQ` is definitional the same product
  simpa [prefixProdNormSqQ] using this

/-!
### Determinant invariance under `det = 1` row changes (ℚ)

If we change a `k×n` row-matrix `M` by left-multiplying by a `k×k` matrix `A` with `det A = 1`,
then the Gram determinant of the rows is unchanged.

This is the algebraic backbone for the eventual GS↔Gram bridge: Gram–Schmidt is exactly a sequence
of such row operations (transvections).
-/

lemma det_mul_mul_transpose_invariant_of_det_one
    {k n : ℕ}
    (A : Matrix (Fin k) (Fin k) ℚ)
    (M : Matrix (Fin k) (Fin n) ℚ)
    (hdet : Matrix.det A = 1) :
    Matrix.det ((A * M) * ((A * M).transpose))
      = Matrix.det (M * M.transpose) := by
  classical
  -- `((A*M) * (A*M)ᵀ) = A * (M*Mᵀ) * Aᵀ`
  have hGram :
      ((A * M) * (A * M).transpose) =
        A * (M * M.transpose) * A.transpose := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  -- determinant multiplicativity + `det A = det Aᵀ = 1`
  calc
    Matrix.det ((A * M) * (A * M).transpose)
        = Matrix.det (A * (M * M.transpose) * A.transpose) := by
            exact congrArg Matrix.det hGram
    _ = Matrix.det A * Matrix.det (M * M.transpose) * Matrix.det (A.transpose) := by
            -- expand determinant over the triple product in two steps
            have hAX :
                Matrix.det (A * (M * M.transpose)) =
                  Matrix.det A * Matrix.det (M * M.transpose) :=
              Matrix.det_mul A (M * M.transpose)
            calc
              Matrix.det (A * (M * M.transpose) * A.transpose)
                  = Matrix.det (A * (M * M.transpose)) * Matrix.det (A.transpose) := by
                      -- `det (X * Y) = det X * det Y` with `X = A*(M*Mᵀ)` and `Y = Aᵀ`
                      simpa [Matrix.mul_assoc] using
                        (Matrix.det_mul (A * (M * M.transpose)) (A.transpose))
              _ = (Matrix.det A * Matrix.det (M * M.transpose)) * Matrix.det (A.transpose) := by
                      -- rewrite the left factor using `hAX`
                      rw [hAX]
              _ = Matrix.det A * Matrix.det (M * M.transpose) * Matrix.det (A.transpose) := by
                      simp [mul_assoc]
    _ = 1 * Matrix.det (M * M.transpose) * 1 := by
            simp [hdet, Matrix.det_transpose]
    _ = Matrix.det (M * M.transpose) := by
            simp

/-!
### `projSumForKPrefix` as a `Fin`-indexed sum

This is bookkeeping we’ll reuse to relate the fold-based GS definitions to matrix multiplication.
-/

lemma projSumForKPrefix_eq_fin_sum
    {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ)) :
    projSumForKPrefix (n := n) bk us =
      ∑ i : Fin us.length, (muQPrefix (n := n) bk (us[i.1])) • (us[i.1]) := by
  classical
  let t : (Fin n → ℚ) → (Fin n → ℚ) := fun u => (muQPrefix (n := n) bk u) • u
  have hmap :
      ∀ s : (Fin n → ℚ),
        us.foldl (fun acc u => acc + t u) s = (us.map t).foldl (· + ·) s := by
    induction us with
    | nil =>
        intro s
        simp
    | cons u us ih =>
        intro s
        simp [List.foldl, List.map, ih (s := s + t u), t]

  -- `foldl` over `map t us` equals its `List.sum` since `+` is commutative/associative here.
  have hfoldl_sum :
      (us.map t).foldl (· + ·) (0 : Fin n → ℚ) = (us.map t).sum := by
    -- `List.sum` is `foldr`; for commutative/associative ops, `foldl = foldr`
    letI : Std.Commutative (α := (Fin n → ℚ)) (· + ·) :=
      ⟨by intro a b; simpa using (add_comm a b)⟩
    letI : Std.Associative (α := (Fin n → ℚ)) (· + ·) :=
      ⟨by intro a b c; simpa using (add_assoc a b c)⟩
    have :
        (us.map t).foldl (· + ·) (0 : Fin n → ℚ)
          = (us.map t).foldr (· + ·) (0 : Fin n → ℚ) := by
      simpa using
        (List.foldl_eq_foldr (f := (· + ·)) (a := (0 : Fin n → ℚ)) (l := us.map t))
    -- and `foldr (+) 0` is `List.sum`
    simpa [List.sum] using this

  -- `Fin`-sum of `t (us[i])` is exactly `List.sum (map t us)`.
  have hfin :
      (∑ i : Fin us.length, t (us[i.1])) = (us.map t).sum := by
    -- `Fin.sum_univ_fun_getElem` is the additive version of `prod_univ_fun_getElem`
    simpa [t] using (Fin.sum_univ_fun_getElem (l := us) (f := t))

  -- combine
  calc
    projSumForKPrefix (n := n) bk us
        = us.foldl (fun s u => s + t u) (0 : Fin n → ℚ) := by
            simp [projSumForKPrefix, t]
    _ = (us.map t).foldl (· + ·) (0 : Fin n → ℚ) := by
            simpa using (hmap (s := (0 : Fin n → ℚ)))
    _ = (us.map t).sum := hfoldl_sum
    _ = ∑ i : Fin us.length, t (us[i.1]) := by
            exact hfin.symm
    _ = ∑ i : Fin us.length, (muQPrefix (n := n) bk (us[i.1])) • (us[i.1]) := by
            rfl

/-!
### Row decomposition in terms of GS rows

TODO: package the identity

`b_i = b_i^* + ∑_{j<i} μ_{i,j} b_j^*`

as a matrix statement `prefixRowsQ = U * gsoRowsQ` for a unit lower-triangular `U` (det \(=1\)),
so we can apply `det_mul_mul_transpose_invariant_of_det_one` to finish the GS↔Gram determinant bridge.
-/

lemma rowQ_eq_gsoAtQ_add_projSum_fin
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    let us : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B i.1 (Nat.le_of_lt i.2)
    rowQ (n := n) B i =
      gsoAtQ (n := n) B i +
        ∑ t : Fin us.length, (muQPrefix (n := n) (rowQ (n := n) B i) (us[t.1])) • (us[t.1]) := by
  classical
  intro us
  -- decomposition: `gsoVectorForKPrefix bk us + projSumForKPrefix bk us = bk`
  have hdecomp :
      gsoVectorForKPrefix (n := n) (rowQ (n := n) B i) us +
          projSumForKPrefix (n := n) (rowQ (n := n) B i) us
        = rowQ (n := n) B i := by
    simpa using (gsoVectorForKPrefix_add_projSum_eq_bk (n := n) (bk := rowQ (n := n) B i) (us := us))
  -- rewrite `gsoVectorForKPrefix` as `gsoAtQ`
  have hgso :
      gsoVectorForKPrefix (n := n) (rowQ (n := n) B i) us = gsoAtQ (n := n) B i := by
    -- `gsoAtQ_eq_gsoVectorForKPrefix` gives `gsoAtQ = gsoVector...`
    simpa [us] using (congrArg id (gsoAtQ_eq_gsoVectorForKPrefix (n := n) (B := B) i)).symm
  -- rewrite the projection sum as a `Fin`-indexed sum
  have hproj :
      projSumForKPrefix (n := n) (rowQ (n := n) B i) us =
        ∑ t : Fin us.length,
          (muQPrefix (n := n) (rowQ (n := n) B i) (us[t.1])) • (us[t.1]) := by
    simpa using (projSumForKPrefix_eq_fin_sum (n := n) (bk := rowQ (n := n) B i) (us := us))
  -- conclude
  -- from `gsoVector + projSum = bk`, rewrite both pieces and rearrange
  have : gsoAtQ (n := n) B i +
        ∑ t : Fin us.length,
          (muQPrefix (n := n) (rowQ (n := n) B i) (us[t.1])) • (us[t.1])
      = rowQ (n := n) B i := by
    -- turn the goal into `gsoVectorForKPrefix + projSumForKPrefix = bk`
    rw [← hgso, ← hproj]
    exact hdecomp
  simp [this, add_comm, add_left_comm, add_assoc]

/-!
### The unit lower-triangular “reconstruction” matrix \(U\)

For a prefix of length `k`, define the `k×k` matrix `reconUQ` such that (morally)

`prefixRowsQ = reconUQ * gsoRowsQ`.

`reconUQ` is lower triangular with diagonal entries `1`, hence `det reconUQ = 1`.
-/

def reconUQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    Matrix (Fin k) (Fin k) ℚ :=
  fun i j =>
    if i = j then
      1
    else if j.1 < i.1 then
      muQ (n := n) B (Fin.castLE hk i) (Fin.castLE hk j)
    else
      0

@[simp] lemma reconUQ_diag {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n)
    (i : Fin k) :
    reconUQ (n := n) B k hk i i = 1 := by
  simp [reconUQ]

lemma reconUQ_upper_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n)
    {i j : Fin k} (hij : i < j) :
    reconUQ (n := n) B k hk i j = 0 := by
  have hne : i ≠ j := ne_of_lt hij
  have hnot : ¬ j.1 < i.1 := Nat.not_lt_of_ge (Nat.le_of_lt hij)
  simp [reconUQ, hne, hnot]

lemma reconUQ_blockTriangular_toDual {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    (reconUQ (n := n) B k hk).BlockTriangular (OrderDual.toDual : Fin k → OrderDual (Fin k)) := by
  intro i j hij
  have hij' : i < j := by
    -- `toDual j < toDual i` means `i < j`
    simpa using hij
  exact reconUQ_upper_zero (n := n) (B := B) (k := k) hk hij'

lemma det_reconUQ_eq_one {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    Matrix.det (reconUQ (n := n) B k hk) = 1 := by
  classical
  -- determinant of a lower-triangular matrix is product of diagonals
  have htri :
      (reconUQ (n := n) B k hk).BlockTriangular (OrderDual.toDual : Fin k → OrderDual (Fin k)) :=
    reconUQ_blockTriangular_toDual (n := n) (B := B) (k := k) hk
  -- `det_of_lowerTriangular` lives in `Mathlib.LinearAlgebra.Matrix.Block` (re-exported)
  rw [Matrix.det_of_lowerTriangular (M := reconUQ (n := n) B k hk) htri]
  simp [reconUQ_diag]

/-!
### Expanding `reconUQ * gsoRowsQ`

This is the “easy half” of the reconstruction equation: it shows that the `i`-th reconstructed row
is `gsoAtQ i` plus a linear combination of earlier GS rows.
-/

lemma reconUQ_mul_gsoRowsQ_apply
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n)
    (i : Fin k) (a : Fin n) :
    ((reconUQ (n := n) B k hk) * (gsoRowsQ (n := n) B k hk)) i a
      =
      gsoAtQ (n := n) B (Fin.castLE hk i) a +
        (Finset.univ.filter (fun j : Fin k => j.1 < i.1)).sum (fun j =>
          (muQ (n := n) B (Fin.castLE hk i) (Fin.castLE hk j)) *
            gsoAtQ (n := n) B (Fin.castLE hk j) a) := by
  classical
  -- abbreviate the summand
  let f : Fin k → ℚ := fun j =>
    (reconUQ (n := n) B k hk i j) * (gsoRowsQ (n := n) B k hk j a)
  have hmul :
      ((reconUQ (n := n) B k hk) * (gsoRowsQ (n := n) B k hk)) i a =
        (Finset.univ : Finset (Fin k)).sum f := by
    simp [Matrix.mul_apply, f]

  -- split the sum into `j < i` and `¬ j < i`
  have hsplit :
      (Finset.univ : Finset (Fin k)).sum f =
        ((Finset.univ.filter fun j : Fin k => j.1 < i.1).sum f) +
        ((Finset.univ.filter fun j : Fin k => ¬ (j.1 < i.1)).sum f) := by
    -- `sum_filter_add_sum_filter_not` partitions the finset.
    simpa [add_comm, add_left_comm, add_assoc] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin k)))
        (p := fun j : Fin k => j.1 < i.1) (f := f)).symm

  -- the `¬ j < i` part: only `j = i` contributes (everything above the diagonal is 0)
  have hnot_lt_sum :
      ((Finset.univ.filter fun j : Fin k => ¬ (j.1 < i.1)).sum f) = f i := by
    have hi_mem : i ∈ (Finset.univ.filter fun j : Fin k => ¬ (j.1 < i.1)) := by
      simp
    have hzero :
        ∀ j, j ∈ (Finset.univ.filter fun j : Fin k => ¬ (j.1 < i.1)) → j ≠ i → f j = 0 := by
      intro j hj hji
      have hnot : ¬ (j.1 < i.1) := by
        simpa [Finset.mem_filter] using hj
      have hnot' : ¬ j < i := by
        intro hij
        -- unfold `Fin` order to `Nat` order on `.1`
        have : j.1 < i.1 := (Fin.lt_def).1 hij
        exact hnot this
      have hij_le : i ≤ j := le_of_not_gt hnot'
      have hij : i < j := lt_of_le_of_ne hij_le (by
        intro h
        exact hji h.symm)
      -- above-diagonal entry is 0
      have hrecon : reconUQ (n := n) B k hk i j = 0 :=
        reconUQ_upper_zero (n := n) (B := B) (k := k) hk hij
      simp [f, hrecon]
    -- use the standard “single nonzero term” lemma
    -- (the proof style mirrors `Mathlib/Data/Matrix/Mul.lean`).
    classical
    -- `sum_eq_single` wants a proof that all other terms are zero, plus membership of `i`.
    -- We provide the “others are zero” proof with access to the membership hypothesis.
    simpa [hi_mem] using
      (Finset.sum_eq_single i
        (fun j hj => hzero j hj)
        (by simpa using hi_mem))

  -- the `< i` part: rewrite `reconUQ` to `muQ` and `gsoRowsQ` to `gsoAtQ`
  have hlt_sum :
      ((Finset.univ.filter fun j : Fin k => j.1 < i.1).sum f)
        =
        (Finset.univ.filter (fun j : Fin k => j.1 < i.1)).sum (fun j =>
          (muQ (n := n) B (Fin.castLE hk i) (Fin.castLE hk j)) *
            gsoAtQ (n := n) B (Fin.castLE hk j) a) := by
    -- both sides are the same `filter` sum, but `reconUQ` needs the facts `j < i` and `i ≠ j`.
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hlt : j.1 < i.1 := by
      simpa [Finset.mem_filter] using hj
    have hlt' : j < i := (Fin.lt_def).2 hlt
    have hne : i ≠ j := (ne_of_lt hlt').symm
    -- unfold `f`, and simplify `reconUQ` using `hne` and `hlt`
    dsimp [f]
    have hrecon : reconUQ (n := n) B k hk i j = muQ (n := n) B (Fin.castLE hk i) (Fin.castLE hk j) := by
      -- by definition of `reconUQ`, the diagonal case is excluded and the `<` branch is taken
      simp [reconUQ, hne, hlt]
    -- and `gsoRowsQ` is just `gsoAtQ` on casts
    simp [gsoRowsQ, hrecon]

  -- assemble
  calc
    ((reconUQ (n := n) B k hk) * (gsoRowsQ (n := n) B k hk)) i a
        = (Finset.univ : Finset (Fin k)).sum f := hmul
    _ = ((Finset.univ.filter fun j : Fin k => j.1 < i.1).sum f) +
          ((Finset.univ.filter fun j : Fin k => ¬ (j.1 < i.1)).sum f) := hsplit
    _ = ((Finset.univ.filter fun j : Fin k => j.1 < i.1).sum (fun j =>
            (muQ (n := n) B (Fin.castLE hk i) (Fin.castLE hk j)) *
              gsoAtQ (n := n) B (Fin.castLE hk j) a)) +
          f i := by
          -- rewrite both filtered sums explicitly
          rw [hlt_sum, hnot_lt_sum]
    _ = gsoAtQ (n := n) B (Fin.castLE hk i) a +
          (Finset.univ.filter (fun j : Fin k => j.1 < i.1)).sum (fun j =>
            (muQ (n := n) B (Fin.castLE hk i) (Fin.castLE hk j)) *
              gsoAtQ (n := n) B (Fin.castLE hk j) a) := by
          -- `f i` is the diagonal contribution `1 * gsoAtQ i`
          have hfi : f i = gsoAtQ (n := n) B (Fin.castLE hk i) a := by
            simp [f, reconUQ, gsoRowsQ]
          -- reorder
          simp [hfi, add_comm, add_left_comm, add_assoc]
/-!
### The Gram determinant bridge (assuming the reconstruction matrix equation)

Once we have `prefixRowsQ = reconUQ * gsoRowsQ`, we can transfer determinants across:

`det(gramPrefixQ) = det(gsoRowsQ * gsoRowsQᵀ)`.
-/

lemma det_gramPrefixQ_eq_det_gsoRowsQ_mul_transpose_of_recon
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n)
    (hEq : prefixRowsQ (n := n) B k hk = (reconUQ (n := n) B k hk) * (gsoRowsQ (n := n) B k hk)) :
    Matrix.det (gramPrefixQ (n := n) B k hk)
      =
      Matrix.det (gsoRowsQ (n := n) B k hk * (gsoRowsQ (n := n) B k hk).transpose) := by
  classical
  -- rewrite `gramPrefixQ` as `prefixRowsQ * prefixRowsQᵀ`
  have hGram :=
    gramPrefixQ_eq_prefixRowsQ_mul_transpose (n := n) (B := B) (k := k) hk
  -- rewrite the RHS with the reconstruction equation and cancel `reconUQ` using `det = 1` invariance
  have hdetU : Matrix.det (reconUQ (n := n) B k hk) = 1 :=
    det_reconUQ_eq_one (n := n) (B := B) (k := k) hk
  -- `((U*M) * (U*M)ᵀ)` is exactly the Gram of the reconstructed rows
  have :
      Matrix.det (prefixRowsQ (n := n) B k hk * (prefixRowsQ (n := n) B k hk).transpose)
        =
        Matrix.det (gsoRowsQ (n := n) B k hk * (gsoRowsQ (n := n) B k hk).transpose) := by
    -- rewrite `prefixRowsQ` to `U*M`
    rw [hEq]
    -- now use the invariant lemma
    simpa [Matrix.transpose_mul, Matrix.mul_assoc] using
      (det_mul_mul_transpose_invariant_of_det_one
        (k := k) (n := n)
        (A := reconUQ (n := n) B k hk)
        (M := gsoRowsQ (n := n) B k hk)
        hdetU)
  -- finish by rewriting `gramPrefixQ`
  simpa [hGram] using this

/-!
### The reconstruction matrix equation (TODO)

Remaining “hard” step for the GS-volume ↔ Gram-determinant bridge:

`prefixRowsQ = reconUQ * gsoRowsQ`.

Once proved, we can instantiate
`det_gramPrefixQ_eq_det_gsoRowsQ_mul_transpose_of_recon` and then combine with
`det_gsoRowsQ_mul_transpose_eq_prefixProdNormSqQ_of_RowLIQ`.
-/

lemma prefixRowsQ_eq_reconUQ_mul_gsoRowsQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    prefixRowsQ (n := n) B k hk =
      (reconUQ (n := n) B k hk) * (gsoRowsQ (n := n) B k hk) := by
  classical
  -- TODO: finish (this is the missing GS-volume ↔ Gram determinant bridge step)
  -- Strategy: ext i a; use `reconUQ_mul_gsoRowsQ_apply` and relate to `rowQ_eq_gsoAtQ_add_projSum_fin`.
  ext i a
  -- abbreviations
  let i0 : Fin n := Fin.castLE hk i
  -- rewrite LHS to `rowQ`
  have hL : prefixRowsQ (n := n) B k hk i a = rowQ (n := n) B i0 a := by
    rfl
  -- rewrite RHS using the explicit expansion lemma
  have hR :
      ((reconUQ (n := n) B k hk) * (gsoRowsQ (n := n) B k hk)) i a =
        gsoAtQ (n := n) B i0 a +
          (Finset.univ.filter (fun j : Fin k => j.1 < i.1)).sum (fun j =>
            (muQ (n := n) B i0 (Fin.castLE hk j)) * gsoAtQ (n := n) B (Fin.castLE hk j) a) := by
    simpa [i0] using (reconUQ_mul_gsoRowsQ_apply (n := n) (B := B) (k := k) hk i a)

  -- GS row decomposition at `i0`
  have hrowFn :=
    rowQ_eq_gsoAtQ_add_projSum_fin (n := n) (B := B) i0
  -- evaluate the function equality at coordinate `a`
  have hrow :
      rowQ (n := n) B i0 a =
        gsoAtQ (n := n) B i0 a +
          (let us : List (Fin n → ℚ) :=
              gsoPrefixListQ (n := n) B i0.1 (Nat.le_of_lt i0.2)
            ∑ t : Fin us.length,
              (muQPrefix (n := n) (rowQ (n := n) B i0) (us[t.1])) * (us[t.1] a)) := by
    classical
    -- unfold the `let` in `hrowFn`, then apply `congrArg` and simplify `•` pointwise
    simpa [Pi.add_apply, Pi.smul_apply, mul_assoc, i0] using congrArg (fun v => v a) hrowFn

  -- TODO: reindex the `List`-indexed sum into the `Finset`-indexed sum on `< i`.
  -- We leave this as a separate local lemma to keep the main spine readable.
  have hsum :
      (let us : List (Fin n → ℚ) :=
          gsoPrefixListQ (n := n) B i0.1 (Nat.le_of_lt i0.2)
        ∑ t : Fin us.length,
          (muQPrefix (n := n) (rowQ (n := n) B i0) (us[t.1])) * (us[t.1] a))
        =
        (Finset.univ.filter (fun j : Fin k => j.1 < i.1)).sum (fun j =>
          (muQ (n := n) B i0 (Fin.castLE hk j)) * gsoAtQ (n := n) B (Fin.castLE hk j) a) := by
    classical
    -- name the prefix GS list
    let us : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B i0.1 (Nat.le_of_lt i0.2)
    have hi0 : i0.1 = i.1 := rfl
    have hlen : us.length = i.1 := by
      simpa [us, hi0] using
        (gsoPrefixListQ_length (n := n) (B := B) (k := i0.1) (hk := Nat.le_of_lt i0.2))

    -- embedding `Fin us.length ↪ Fin k` by the same nat value
    let emb : Fin us.length → Fin k := fun t =>
      ⟨t.1, Nat.lt_trans (by simpa [hlen] using t.2) i.2⟩
    have hemb_inj : Function.Injective emb := by
      intro t₁ t₂ h
      apply Fin.ext
      have : (emb t₁).1 = (emb t₂).1 := congrArg (fun x : Fin k => x.1) h
      simpa [emb] using this

    -- the image of `emb` is exactly `{j : Fin k | j.1 < i.1}`
    have himage :
        (Finset.univ.image emb) = (Finset.univ.filter (fun j : Fin k => j.1 < i.1)) := by
      ext j
      constructor
      · intro hj
        rcases Finset.mem_image.mp hj with ⟨t, ht, rfl⟩
        have ht' : t.1 < i.1 := by
          simpa [hlen] using t.2
        -- show membership directly (avoid rewriting to `<` on `Fin`)
        refine Finset.mem_filter.mpr ?_
        constructor
        · simp
        · simpa [emb] using ht'
      · intro hj
        have hj' : j.1 < i.1 := by
          simpa [Finset.mem_filter] using hj
        -- choose the preimage `t` with the same nat value
        let t : Fin us.length := ⟨j.1, by simpa [hlen] using hj'⟩
        refine Finset.mem_image.mpr ⟨t, by simp, ?_⟩
        apply Fin.ext
        rfl

    -- rewrite the RHS sum as a sum over `Fin us.length` using `sum_image`
    have hR :
        (Finset.univ.filter (fun j : Fin k => j.1 < i.1)).sum (fun j =>
            (muQ (n := n) B i0 (Fin.castLE hk j)) * gsoAtQ (n := n) B (Fin.castLE hk j) a)
          =
        (Finset.univ : Finset (Fin us.length)).sum (fun t =>
          (muQ (n := n) B i0 (Fin.castLE hk (emb t))) * gsoAtQ (n := n) B (Fin.castLE hk (emb t)) a) := by
      -- swap sides via `himage`
      rw [← himage]
      -- `sum_image` needs injectivity
      simpa [Finset.sum_image, hemb_inj]

    -- identify the per-index term with the `List`-indexed projection term
    have hterm :
        (∑ t : Fin us.length,
            (muQPrefix (n := n) (rowQ (n := n) B i0) (us[t.1])) * (us[t.1] a))
          =
        (Finset.univ : Finset (Fin us.length)).sum (fun t =>
          (muQ (n := n) B i0 (Fin.castLE hk (emb t))) * gsoAtQ (n := n) B (Fin.castLE hk (emb t)) a) := by
      -- both are `Fintype` sums over `Fin us.length`; show termwise equality
      classical
      apply (Fintype.sum_congr _ _)
      intro t
      -- set `jn : Fin n` with value `t.1`
      have ht_i : t.1 < i0.1 := by
        have : t.1 < us.length := t.2
        simpa [hlen, hi0] using this
      let jn : Fin n := ⟨t.1, Nat.lt_trans ht_i i0.2⟩
      -- identify `us[t] = gsoAtQ B jn`
      have hget :
          us[t.1] = gsoAtQ (n := n) B jn := by
        have hk' : i0.1 ≤ n := Nat.le_of_lt i0.2
        have hgetD :
            us.getD t.1 (zeroVecQ (n := n)) = gsoAtQ (n := n) B jn := by
          -- avoid `simp` here: `List.getD` can reprint as `l[n]?.getD _`, and simp may unfold it.
          change
              (gsoPrefixListQ (n := n) B i0.1 (Nat.le_of_lt i0.2)).getD t.1 (zeroVecQ (n := n))
                = gsoAtQ (n := n) B jn
          -- `t.1 = jn.1` by definition, and `getD` on the `i0.1`-prefix list gives `gsoAtQ`.
          exact
            (gsoPrefixListQ_getD_eq_gsoAtQ_of_lt (n := n) (B := B)
              (k := i0.1) (hk := hk') (j := jn) (hjk := ht_i))
        -- convert `getD` to `getElem` at an in-bounds index
        have hgetD_eq : us.getD t.1 (zeroVecQ (n := n)) = us[t.1] := by
          simpa using (List.getD_eq_getElem (l := us) (d := zeroVecQ (n := n)) (hn := t.2) (n := t.1))
        exact hgetD_eq.symm.trans hgetD
      -- rewrite `Fin.castLE hk (emb t)` to `jn`
      have hcast : Fin.castLE hk (emb t) = jn := by
        apply Fin.ext
        rfl
      -- compare the terms
      simp [hget, hcast, emb, muQ, muQPrefix]

    -- finish: unfold the outer `let us` and combine `hterm` with `hR`
    -- LHS of the goal is the `Fintype` sum; RHS is the filtered `Finset` sum.
    -- We rewrite RHS using `hR` and then use `hterm`.
    -- (note: `∑ t : Fin us.length, ...` is definitional `Fintype.sum`, which matches `Fintype.sum_congr` above)
    -- rewrite the goal's `let us` to our `us`
    have : (∑ t : Fin us.length,
        (muQPrefix (n := n) (rowQ (n := n) B i0) (us[t.1])) * (us[t.1] a))
        =
      (Finset.univ.filter (fun j : Fin k => j.1 < i.1)).sum (fun j =>
        (muQ (n := n) B i0 (Fin.castLE hk j)) * gsoAtQ (n := n) B (Fin.castLE hk j) a) := by
      -- rewrite RHS to the `Finset.univ.sum` form, then use `hterm`
      calc
        (∑ t : Fin us.length,
            (muQPrefix (n := n) (rowQ (n := n) B i0) (us[t.1])) * (us[t.1] a))
            =
          (Finset.univ : Finset (Fin us.length)).sum (fun t =>
            (muQ (n := n) B i0 (Fin.castLE hk (emb t))) * gsoAtQ (n := n) B (Fin.castLE hk (emb t)) a) := by
              simpa using hterm
        _ =
          (Finset.univ.filter (fun j : Fin k => j.1 < i.1)).sum (fun j =>
            (muQ (n := n) B i0 (Fin.castLE hk j)) * gsoAtQ (n := n) B (Fin.castLE hk j) a) := by
              simpa using hR.symm
    simpa [us] using this

  -- finish
  -- `rowQ = gsoAtQ + (List sum)` and the RHS expands to `gsoAtQ + (Finset sum)`
  -- so it suffices to substitute `hsum` and compare.
  calc
    prefixRowsQ (n := n) B k hk i a
        = rowQ (n := n) B i0 a := hL
    _ = gsoAtQ (n := n) B i0 a +
          (let us : List (Fin n → ℚ) :=
              gsoPrefixListQ (n := n) B i0.1 (Nat.le_of_lt i0.2)
            ∑ t : Fin us.length,
              (muQPrefix (n := n) (rowQ (n := n) B i0) (us[t.1])) * (us[t.1] a)) := hrow
    _ = gsoAtQ (n := n) B i0 a +
          (Finset.univ.filter (fun j : Fin k => j.1 < i.1)).sum (fun j =>
            (muQ (n := n) B i0 (Fin.castLE hk j)) * gsoAtQ (n := n) B (Fin.castLE hk j) a) := by
          simpa [hsum]
    _ = ((reconUQ (n := n) B k hk) * (gsoRowsQ (n := n) B k hk)) i a := by
          simpa [hR, add_comm]

/-!
### The GS-volume ↔ Gram determinant bridge (completed)

With the reconstruction equation in hand, the determinant bridge becomes unconditional.
-/

lemma det_gramPrefixQ_eq_prefixProdNormSqQ_of_RowLIQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n)
    (hli : RowLIQ (n := n) B) :
    Matrix.det (gramPrefixQ (n := n) B k hk) = prefixProdNormSqQ (n := n) B k hk := by
  classical
  have hrecon :
      prefixRowsQ (n := n) B k hk =
        (reconUQ (n := n) B k hk) * (gsoRowsQ (n := n) B k hk) :=
    prefixRowsQ_eq_reconUQ_mul_gsoRowsQ (n := n) (B := B) (k := k) hk
  have hdet_bridge :
      Matrix.det (gramPrefixQ (n := n) B k hk) =
        Matrix.det (gsoRowsQ (n := n) B k hk * (gsoRowsQ (n := n) B k hk).transpose) :=
    det_gramPrefixQ_eq_det_gsoRowsQ_mul_transpose_of_recon (n := n) (B := B) (k := k) hk hrecon
  have hgso :
      Matrix.det (gsoRowsQ (n := n) B k hk * (gsoRowsQ (n := n) B k hk).transpose)
        =
        prefixProdNormSqQ (n := n) B k hk :=
    det_gsoRowsQ_mul_transpose_eq_prefixProdNormSqQ_of_RowLIQ (n := n) (B := B) (k := k) hk hli
  exact hdet_bridge.trans hgso

/-!
### Integer Gram matrix (for discrete lower bounds later)

`gramPrefixZ` is the same prefix Gram matrix but computed in `ℤ`. This is the object whose
determinant is an integer “volume squared” invariant of the prefix lattice span.

We’ll use it to get a discrete lower bound on swap-driven shrinkage.
-/

def dotZ {n : ℕ} (v w : Fin n → ℤ) : ℤ :=
  ∑ i, v i * w i

def gramPrefixZ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    Matrix (Fin k) (Fin k) ℤ :=
  fun i j =>
    dotZ (n := n)
      (B (Fin.castLE hk i))
      (B (Fin.castLE hk j))

/-!
For determinant arguments it is useful to view the prefix Gram matrix as
`prefixRowsZ * prefixRowsZᵀ`.
-/

def prefixRowsZ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    Matrix (Fin k) (Fin n) ℤ :=
  fun i j => B (Fin.castLE hk i) j

@[simp] lemma prefixRowsZ_apply {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n)
    (i : Fin k) (j : Fin n) :
    prefixRowsZ (n := n) B k hk i j = B (Fin.castLE hk i) j := by
  rfl

lemma gramPrefixZ_eq_prefixRowsZ_mul_transpose
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    gramPrefixZ (n := n) B k hk =
      prefixRowsZ (n := n) B k hk * (prefixRowsZ (n := n) B k hk).transpose := by
  classical
  ext i j
  -- unfold the matrix product and compare to `dotZ`
  simp [gramPrefixZ, prefixRowsZ, dotZ, Matrix.mul_apply, Matrix.transpose_apply]

/-!
### Prefix Gram determinant invariance under size-reduction within the prefix

If `a,b : Fin k` are indices inside the first `k` rows, and we update row `a` by
`row_a := row_a - q * row_b`, then the `k×k` integer Gram determinant is unchanged.

This is the exact invariance needed for the “potential is bounded below by an integer”
termination argument.
-/

lemma prefixRowsZ_size_reduceZ_within_prefix
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k : Nat) (hk : k ≤ n) (a b : Fin k) (q : ℤ) (hab : a ≠ b) :
    prefixRowsZ (n := n) (size_reduceZ (n := n) B (Fin.castLE hk a) (Fin.castLE hk b) q) k hk =
      (Matrix.transvection a b (-q) : Matrix (Fin k) (Fin k) ℤ) * prefixRowsZ (n := n) B k hk := by
  classical
  ext i t
  by_cases hia : i = a
  · subst hia
    -- updated row in the prefix: expand `transvection = 1 + single` against a rectangular matrix
    simp [Matrix.transvection, Matrix.add_mul, Matrix.one_mul,
      Matrix.single_mul_eq_updateRow_zero, Matrix.updateRow_self, Matrix.updateRow_ne,
      prefixRowsZ, size_reduceZ, Pi.sub_apply, Pi.smul_apply,
      sub_eq_add_neg, smul_eq_mul, hab, mul_assoc]
  · -- unchanged row in the prefix
    have hne : i ≠ a := hia
    -- `Fin.castLE` is injective, so `castLE hk i ≠ castLE hk a`
    have hne' : Fin.castLE hk i ≠ Fin.castLE hk a := by
      intro h
      exact hne (Fin.castLE_inj.mp h)
    -- outside row `a`, the `single` part contributes zero
    simp [Matrix.transvection, Matrix.add_mul, Matrix.one_mul,
      Matrix.single_mul_eq_updateRow_zero, Matrix.updateRow_self, Matrix.updateRow_ne,
      prefixRowsZ, size_reduceZ, Matrix.updateRow_ne, hne', hne]

lemma det_gramPrefixZ_size_reduceZ_within_prefix
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k : Nat) (hk : k ≤ n) (a b : Fin k) (q : ℤ) (hab : a ≠ b) :
    Matrix.det (gramPrefixZ (n := n)
      (size_reduceZ (n := n) B (Fin.castLE hk a) (Fin.castLE hk b) q) k hk)
      =
      Matrix.det (gramPrefixZ (n := n) B k hk) := by
  classical
  let E : Matrix (Fin k) (Fin k) ℤ := Matrix.transvection a b (-q)
  have hE : Matrix.det E = 1 := by
    simpa [E] using (Matrix.det_transvection_of_ne (i := a) (j := b) (R := ℤ) hab (-q))
  -- rewrite `gramPrefixZ` as `P * Pᵀ` and apply the row-update factorization
  have hP :
      prefixRowsZ (n := n) (size_reduceZ (n := n) B (Fin.castLE hk a) (Fin.castLE hk b) q) k hk
        = E * prefixRowsZ (n := n) B k hk := by
    simpa [E] using
      prefixRowsZ_size_reduceZ_within_prefix (n := n) (B := B) (k := k) hk (a := a) (b := b) (q := q) hab
  calc
    Matrix.det (gramPrefixZ (n := n)
          (size_reduceZ (n := n) B (Fin.castLE hk a) (Fin.castLE hk b) q) k hk)
        = Matrix.det
            (prefixRowsZ (n := n)
              (size_reduceZ (n := n) B (Fin.castLE hk a) (Fin.castLE hk b) q) k hk
              * (prefixRowsZ (n := n)
                  (size_reduceZ (n := n) B (Fin.castLE hk a) (Fin.castLE hk b) q) k hk).transpose) := by
            simp [gramPrefixZ_eq_prefixRowsZ_mul_transpose]
    _ = Matrix.det ((E * prefixRowsZ (n := n) B k hk) * ((E * prefixRowsZ (n := n) B k hk)).transpose) := by
            simp [hP]
    _ = Matrix.det ((E * prefixRowsZ (n := n) B k hk) * ((prefixRowsZ (n := n) B k hk).transpose * E.transpose)) := by
            simp [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = Matrix.det ((E * (prefixRowsZ (n := n) B k hk * (prefixRowsZ (n := n) B k hk).transpose)) * E.transpose) := by
            -- reassociate so the final factor is square (k×k)
            simp [Matrix.mul_assoc]
    _ = Matrix.det (E * (prefixRowsZ (n := n) B k hk * (prefixRowsZ (n := n) B k hk).transpose)) *
          Matrix.det (E.transpose) := by
            simp [Matrix.det_mul]
    _ = (Matrix.det E * Matrix.det (prefixRowsZ (n := n) B k hk * (prefixRowsZ (n := n) B k hk).transpose)) *
          Matrix.det (E.transpose) := by
            simp [Matrix.det_mul, Matrix.mul_assoc]
    _ = Matrix.det (prefixRowsZ (n := n) B k hk * (prefixRowsZ (n := n) B k hk).transpose) := by
            simp [hE, Matrix.det_transpose, mul_assoc]
    _ = Matrix.det (gramPrefixZ (n := n) B k hk) := by
            simp [gramPrefixZ_eq_prefixRowsZ_mul_transpose]

@[simp] lemma prefixRowsZ_full {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    prefixRowsZ (n := n) B n (le_rfl) = B := by
  classical
  ext i j
  simp [prefixRowsZ]

@[simp] lemma gramPrefixZ_full {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    gramPrefixZ (n := n) B n (le_rfl) = B * B.transpose := by
  simpa [gramPrefixZ_eq_prefixRowsZ_mul_transpose] using
    (gramPrefixZ_eq_prefixRowsZ_mul_transpose (n := n) (B := B) (k := n) (hk := le_rfl))

/-!
### Size-reduction as a transvection

Updating a row by `row_k := row_k - q • row_j` is exactly left-multiplication by the transvection
matrix `transvection k j (-q)`. This makes determinant-invariance proofs (via `det = 1`) clean.
-/

lemma size_reduceZ_eq_transvection_mul
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) (q : ℤ) (hkj : k ≠ j) :
    size_reduceZ (n := n) B k j q =
      (Matrix.transvection k j (-q) : Matrix (Fin n) (Fin n) ℤ) * B := by
  classical
  ext a b
  by_cases ha : a = k
  · subst ha
    -- transvection adds `(-q)` times row `j` to row `k`
    simp [size_reduceZ, Matrix.updateRow_self, Matrix.transvection_mul_apply_same, add_comm, add_left_comm,
      add_assoc, sub_eq_add_neg, smul_eq_mul]
  · -- other rows unchanged
    simp [size_reduceZ, Matrix.updateRow_ne, ha, Matrix.transvection_mul_apply_of_ne]

lemma det_gramPrefixZ_size_reduceZ_full
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) (q : ℤ) (hkj : k ≠ j) :
    Matrix.det (gramPrefixZ (n := n) (size_reduceZ (n := n) B k j q) n (le_rfl)) =
      Matrix.det (gramPrefixZ (n := n) B n (le_rfl)) := by
  classical
  -- We avoid a matrix-level conjugation proof and work purely at the determinant level:
  -- `gramPrefixZ B n = B * Bᵀ`, and `size_reduceZ` is left-multiplication by a transvection
  -- with determinant 1, so `det(B') = det(B)` and hence `det(B' * B'ᵀ) = det(B * Bᵀ)`.
  let E : Matrix (Fin n) (Fin n) ℤ := Matrix.transvection k j (-q)
  have hB' : size_reduceZ (n := n) B k j q = E * B := by
    simpa [E] using
      (size_reduceZ_eq_transvection_mul (n := n) (B := B) (k := k) (j := j) (q := q) hkj)
  have hdetE : Matrix.det E = 1 := by
    simpa [E] using (Matrix.det_transvection_of_ne (i := k) (j := j) (R := ℤ) hkj (-q))
  have hdetB' : Matrix.det (size_reduceZ (n := n) B k j q) = Matrix.det B := by
    calc
      Matrix.det (size_reduceZ (n := n) B k j q)
          = Matrix.det (E * B) := by simpa [hB']
      _ = Matrix.det E * Matrix.det B := by simp [Matrix.det_mul]
      _ = Matrix.det B := by simp [hdetE]
  -- now compare `det(gram)` via `B * Bᵀ`
  calc
    Matrix.det (gramPrefixZ (n := n) (size_reduceZ (n := n) B k j q) n (le_rfl))
        = Matrix.det ((size_reduceZ (n := n) B k j q) * (size_reduceZ (n := n) B k j q).transpose) := by
            simp [gramPrefixZ_full]
    _ = Matrix.det (size_reduceZ (n := n) B k j q) * Matrix.det ((size_reduceZ (n := n) B k j q).transpose) := by
            simp [Matrix.det_mul]
    _ = Matrix.det (size_reduceZ (n := n) B k j q) * Matrix.det (size_reduceZ (n := n) B k j q) := by
            simp [Matrix.det_transpose]
    _ = Matrix.det B * Matrix.det B := by
            simp [hdetB']
    _ = Matrix.det (B * B.transpose) := by
            -- `det (B * Bᵀ) = det(B) * det(B)`
            simp [Matrix.det_mul, Matrix.det_transpose, mul_assoc]
    _ = Matrix.det (gramPrefixZ (n := n) B n (le_rfl)) := by
            simp [gramPrefixZ_full]

lemma gramPrefixQ_eq_cast_gramPrefixZ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    gramPrefixQ (n := n) B k hk =
      fun i j => ((gramPrefixZ (n := n) B k hk i j : ℤ) : ℚ) := by
  classical
  ext i j
  -- unfold to `Finset` sums and use `intCast` distributivity
  simp [gramPrefixQ, gramPrefixZ, dotQ, dotZ, rowQ]

lemma det_gramPrefixQ_eq_cast_det_gramPrefixZ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    Matrix.det (gramPrefixQ (n := n) B k hk) =
      ((Matrix.det (gramPrefixZ (n := n) B k hk) : ℤ) : ℚ) := by
  classical
  -- rewrite `gramPrefixQ` as an entrywise cast of the ℤ Gram matrix
  have hcast := gramPrefixQ_eq_cast_gramPrefixZ (n := n) (B := B) (k := k) hk
  have hdet := congrArg Matrix.det hcast
  -- turn `det (cast matrix)` into `cast (det matrix)`
  -- (`Int.cast_det` is stated as `(M.det : R) = (M.map (fun x => (x : R))).det`)
  -- so we use it in the reverse direction.
  have hdet_cast :
      ((Matrix.det (gramPrefixZ (n := n) B k hk) : ℤ) : ℚ)
        =
        Matrix.det ((gramPrefixZ (n := n) B k hk).map fun x => (x : ℚ)) := by
    simpa using (Int.cast_det (R := ℚ) (M := gramPrefixZ (n := n) B k hk))
  -- finish: identify the RHS matrix with the one from `hcast`
  -- (both are definitional entrywise casts)
  simpa [Matrix.map_apply] using hdet.trans hdet_cast.symm

/-!
#### Swap invariance at full prefix `k = n`

This is the easy, “no `Fin` embedding pain” case: when the prefix length equals the ambient
dimension, the swap is just a reindexing on `Fin n`, so determinant invariance follows directly
from `Matrix.det_reindex_self`.
-/

lemma gramPrefixQ_swap_vectors_reindex_full
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) :
    gramPrefixQ (n := n) (swap_vectors (n := n) B k j) n (le_rfl) =
      Matrix.reindex (Equiv.swap k j) (Equiv.swap k j) (gramPrefixQ (n := n) B n (le_rfl)) := by
  classical
  have hrow : ∀ i : Fin n,
      rowQ (n := n) (swap_vectors (n := n) B k j) i =
        rowQ (n := n) B ((Equiv.swap k j) i) := by
    intro i
    by_cases hik : i = k
    · subst hik
      ext t
      simp [rowQ, swap_vectors]
    · by_cases hij : i = j
      · subst hij
        ext t
        simp [rowQ, swap_vectors]
      · -- neither index is swapped
        have : (Equiv.swap k j) i = i := Equiv.swap_apply_of_ne_of_ne hik hij
        -- `rowQ` unchanged for indices other than `k,j`
        have hsame :
            rowQ (n := n) (swap_vectors (n := n) B k j) i = rowQ (n := n) B i :=
          rowQ_swap_vectors_other (n := n) (B := B) (k := k) (j := j) (i := i) hik hij
        simpa [this] using hsame
  ext i0 j0
  -- unfold both sides and rewrite swapped rows through `hrow`
  simp [gramPrefixQ, Matrix.reindex, hrow]

lemma det_gramPrefixQ_swap_vectors_full
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) :
    Matrix.det (gramPrefixQ (n := n) (swap_vectors (n := n) B k j) n (le_rfl)) =
      Matrix.det (gramPrefixQ (n := n) B n (le_rfl)) := by
  classical
  -- rewrite the swapped Gram matrix as a reindexing, then apply det invariance
  have hreindex :=
    gramPrefixQ_swap_vectors_reindex_full (n := n) (B := B) (k := k) (j := j)
  have hdet := congrArg Matrix.det hreindex
  -- `det (reindex e e M) = det M`
  simpa using hdet.trans
    (Matrix.det_reindex_self (R := ℚ) (e := Equiv.swap k j) (A := gramPrefixQ (n := n) B n (le_rfl)))

/-!
#### Swap invariance for an arbitrary prefix `k ≤ n`

If we swap two indices *inside* the first `k` rows (i.e. swap `a b : Fin k`, lifted to `Fin n`),
the `k×k` Gram matrix is reindexed by `Equiv.swap a b`, and the determinant is unchanged.
-/

private lemma swap_castLE
    {k n : ℕ} (hk : k ≤ n) (a b i : Fin k) :
    Equiv.swap (Fin.castLE hk a) (Fin.castLE hk b) (Fin.castLE hk i) =
      Fin.castLE hk (Equiv.swap a b i) := by
  classical
  apply Fin.ext
  by_cases hia : i = a
  · subst hia
    simp
  · by_cases hib : i = b
    · subst hib
      simp
    · -- neither `a` nor `b`
      have hne_a : Fin.castLE hk i ≠ Fin.castLE hk a := by
        intro h
        exact hia (Fin.castLE_injective hk h)
      have hne_b : Fin.castLE hk i ≠ Fin.castLE hk b := by
        intro h
        exact hib (Fin.castLE_injective hk h)
      simp [Equiv.swap_apply_of_ne_of_ne, hia, hib, hne_a, hne_b]

lemma gramPrefixQ_swap_vectors_reindex
    {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hk : k ≤ n) (a b : Fin k) :
    gramPrefixQ (n := n)
        (swap_vectors (n := n) B (Fin.castLE hk a) (Fin.castLE hk b))
        k hk
      =
      Matrix.reindex (Equiv.swap a b) (Equiv.swap a b) (gramPrefixQ (n := n) B k hk) := by
  classical
  ext i j
  -- rewrite the swapped rows, then commute `swap` with `castLE` (inside the prefix).
  have hrow_i :
      rowQ (n := n)
          (swap_vectors (n := n) B (Fin.castLE hk a) (Fin.castLE hk b))
          (Fin.castLE hk i)
        =
        rowQ (n := n) B
          (Fin.castLE hk ((Equiv.swap a b) i)) := by
    ext t
    -- expand `rowQ` and `swap_vectors`, then commute the swap through the prefix cast
    simp [rowQ, swap_vectors, swap_castLE (hk := hk)]
  have hrow_j :
      rowQ (n := n)
          (swap_vectors (n := n) B (Fin.castLE hk a) (Fin.castLE hk b))
          (Fin.castLE hk j)
        =
        rowQ (n := n) B
          (Fin.castLE hk ((Equiv.swap a b) j)) := by
    ext t
    simp [rowQ, swap_vectors, swap_castLE (hk := hk)]
  -- now both sides match by definitional unfolding
  simp [gramPrefixQ, Matrix.reindex, hrow_i, hrow_j]

lemma det_gramPrefixQ_swap_vectors
    {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hk : k ≤ n) (a b : Fin k) :
    Matrix.det (gramPrefixQ (n := n)
        (swap_vectors (n := n) B (Fin.castLE hk a) (Fin.castLE hk b))
        k hk)
      =
      Matrix.det (gramPrefixQ (n := n) B k hk) := by
  classical
  have hreindex := gramPrefixQ_swap_vectors_reindex (n := n) (k := k) (B := B) (hk := hk) (a := a) (b := b)
  have hdet := congrArg Matrix.det hreindex
  simpa using hdet.trans
    (Matrix.det_reindex_self (R := ℚ) (e := Equiv.swap a b) (A := gramPrefixQ (n := n) B k hk))

/-!
### Prefix invariance of `prefixProdNormSqQ` under a swap outside the prefix

If `m < k`, then swapping rows `k` and `k-1` happens strictly *after* the first `m` rows, so the
`m`-prefix Gram matrix (and hence the `m`-prefix GS-volume via the bridge) is unchanged.
-/

lemma prefixProdNormSqQ_swap_adj_of_lt
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k : Nat) (hk : k < n) (hk0 : 0 < k)
    (m : Nat) (hm : m < k) (hli : RowLIQ (n := n) B) :
    let k' : Fin n := ⟨k, hk⟩
    let km1Nat : Nat := k - 1
    have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) hk
    let km1' : Fin n := ⟨km1Nat, hkm1⟩
    prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') m (Nat.le_of_lt (Nat.lt_trans hm hk)) =
      prefixProdNormSqQ (n := n) B m (Nat.le_of_lt (Nat.lt_trans hm hk)) := by
  classical
  intro k' km1Nat hkm1 km1'
  -- show the prefix Gram determinant is unchanged (the swap indices are ≥ m)
  have hk_m : m ≤ n := Nat.le_of_lt (Nat.lt_trans hm hk)
  have hGramEq :
      gramPrefixQ (n := n) (swap_vectors (n := n) B k' km1') m hk_m =
        gramPrefixQ (n := n) B m hk_m := by
    classical
    ext i j
    -- the row indices `castLE hk_m i` and `castLE hk_m j` have value < m < k
    have hi_lt_k : (Fin.castLE hk_m i).1 < k := Nat.lt_trans i.2 hm
    have hj_lt_k : (Fin.castLE hk_m j).1 < k := Nat.lt_trans j.2 hm
    have hik : (Fin.castLE hk_m i : Fin n) ≠ k' := by
      intro h
      exact (Nat.ne_of_lt hi_lt_k) (congrArg Fin.val h)
    have hjk : (Fin.castLE hk_m j : Fin n) ≠ k' := by
      intro h
      exact (Nat.ne_of_lt hj_lt_k) (congrArg Fin.val h)
    have hikm1 : (Fin.castLE hk_m i : Fin n) ≠ km1' := by
      intro h
      have : (Fin.castLE hk_m i).1 = km1Nat := congrArg Fin.val h
      -- `castLE hk_m i` has value < m ≤ k-1, so it cannot equal `k-1`
      have hi_lt_km1 : (Fin.castLE hk_m i).1 < km1Nat := by
        -- `i.1 < m < k` gives `i.1 ≤ k-1`, and in fact `< k-1` unless `m = k-1`.
        -- We only need a contradiction with equality, which follows from `i.1 < m ≤ k-1`.
        have : (Fin.castLE hk_m i).1 < m := i.2
        have hm_le : m ≤ km1Nat := by
          -- `m < k` implies `m ≤ k-1`
          simpa [km1Nat] using (Nat.le_pred_of_lt hm)
        exact Nat.lt_of_lt_of_le this hm_le
      exact (Nat.ne_of_lt hi_lt_km1) this
    have hjkm1 : (Fin.castLE hk_m j : Fin n) ≠ km1' := by
      intro h
      have : (Fin.castLE hk_m j).1 = km1Nat := congrArg Fin.val h
      have hj_lt_km1 : (Fin.castLE hk_m j).1 < km1Nat := by
        have hj_lt_m : (Fin.castLE hk_m j).1 < m := j.2
        have hm_le : m ≤ km1Nat := by
          simpa [km1Nat] using (Nat.le_pred_of_lt hm)
        exact Nat.lt_of_lt_of_le hj_lt_m hm_le
      exact (Nat.ne_of_lt hj_lt_km1) this
    -- unfold the dot-product definition and rewrite swapped rows to original rows
    simp [gramPrefixQ, dotQ,
      rowQ_swap_vectors_other (n := n) (B := B) (k := k') (j := km1') (i := Fin.castLE hk_m i) hik hikm1,
      rowQ_swap_vectors_other (n := n) (B := B) (k := k') (j := km1') (i := Fin.castLE hk_m j) hjk hjkm1]
  have hdet :
      Matrix.det (gramPrefixQ (n := n) (swap_vectors (n := n) B k' km1') m hk_m) =
        Matrix.det (gramPrefixQ (n := n) B m hk_m) := by
    simpa [hGramEq]
  -- transfer determinants to `prefixProdNormSqQ` via the completed bridge
  have hli' : RowLIQ (n := n) (swap_vectors (n := n) B k' km1') :=
    RowLIQ_swap_vectors (n := n) (B := B) (k := k') (j := km1') hli
  have hbridge1 :=
    det_gramPrefixQ_eq_prefixProdNormSqQ_of_RowLIQ (n := n)
      (B := swap_vectors (n := n) B k' km1') (k := m) (hk := hk_m) hli'
  have hbridge0 :=
    det_gramPrefixQ_eq_prefixProdNormSqQ_of_RowLIQ (n := n)
      (B := B) (k := m) (hk := hk_m) hli
  -- conclude by rewriting both sides to determinants
  have : prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') m hk_m =
      prefixProdNormSqQ (n := n) B m hk_m := by
    -- `det gram = prefixProd` on both sides
    simpa [hbridge1, hbridge0] using hdet
  simpa using this

lemma gsoNormSqQ_swap_vectors_of_lt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k j t : Fin n) (hjk : (j : ℕ) < (k : ℕ)) (ht : (t : ℕ) < (j : ℕ)) :
    gsoNormSqQ (n := n) (swap_vectors (n := n) B k j) t = gsoNormSqQ (n := n) B t := by
  simp [gsoNormSqQ, gsoAtQ_swap_vectors_of_lt (n := n) (B := B) (k := k) (j := j) (t := t) hjk ht]

lemma gsoNormSqQ_pos_of_RowLIQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Nat) (hi : i + 1 < n)
    (hli : RowLIQ (n := n) B) :
    (0 : ℚ) < gsoNormSqQ (n := n) B ⟨i, Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_of_lt hi)⟩ := by
  classical
  -- Nondegeneracy for the `(i+1)` prefix list (this contains `gsoAtQ i`).
  have hnz_at : HNZAt (n := n) B (i + 1) hi := HNZAt_of_RowLIQ (n := n) (B := B) (k := i + 1) hi hli
  have hk1 : i + 1 ≤ n := Nat.le_of_lt hi
  let ii : Fin n := ⟨i, Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hk1⟩
  have hgetD :
      (gsoPrefixListQ (n := n) B (i + 1) hk1).getD i (zeroVecQ (n := n)) = gsoAtQ (n := n) B ii := by
    -- `i < i+1`
    simpa [ii] using
      (gsoPrefixListQ_getD_eq_gsoAtQ_of_lt (n := n) (B := B) (k := i + 1) (hk := hk1) (j := ii)
        (hjk := Nat.lt_succ_self i))
  have hlen : (gsoPrefixListQ (n := n) B (i + 1) hk1).length = i + 1 := by
    simpa using gsoPrefixListQ_length (n := n) (B := B) (k := i + 1) hk1
  have hi_lt_len : i < (gsoPrefixListQ (n := n) B (i + 1) hk1).length := by
    simpa [hlen] using Nat.lt_succ_self i
  let idx : Fin (gsoPrefixListQ (n := n) B (i + 1) hk1).length := ⟨i, hi_lt_len⟩
  have hmem_getD :
      (gsoPrefixListQ (n := n) B (i + 1) hk1).getD i (zeroVecQ (n := n)) ∈
        gsoPrefixListQ (n := n) B (i + 1) hk1 := by
    have hget_eq :
        (gsoPrefixListQ (n := n) B (i + 1) hk1).getD idx (zeroVecQ (n := n)) =
          (gsoPrefixListQ (n := n) B (i + 1) hk1).get idx := by
      simpa using
        (List.getD_eq_get (l := gsoPrefixListQ (n := n) B (i + 1) hk1) (d := zeroVecQ (n := n)) idx)
    have hget_mem : (gsoPrefixListQ (n := n) B (i + 1) hk1).get idx ∈ gsoPrefixListQ (n := n) B (i + 1) hk1 :=
      List.get_mem _ _
    -- rewrite `get` back to `getD i`
    have : (gsoPrefixListQ (n := n) B (i + 1) hk1).getD idx (zeroVecQ (n := n)) ∈
        gsoPrefixListQ (n := n) B (i + 1) hk1 := by
      simpa [hget_eq] using hget_mem
    simpa [idx] using this
  have hmem : gsoAtQ (n := n) B ii ∈ gsoPrefixListQ (n := n) B (i + 1) hk1 := by
    simpa [hgetD] using hmem_getD
  have hdot_ne0 : dotQ (n := n) (gsoAtQ (n := n) B ii) (gsoAtQ (n := n) B ii) ≠ 0 :=
    hnz_at (gsoAtQ (n := n) B ii) hmem
  have hnn : (0 : ℚ) ≤ gsoNormSqQ (n := n) B ii := gsoNormSqQ_nonneg (n := n) B ii
  have hne : gsoNormSqQ (n := n) B ii ≠ 0 := by
    simpa [gsoNormSqQ] using hdot_ne0
  exact lt_of_le_of_ne hnn (Ne.symm hne)

lemma prefixProdNormSqQ_pos_of_RowLIQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n)
    (hli : RowLIQ (n := n) B) :
    (0 : ℚ) < prefixProdNormSqQ (n := n) B k (Nat.le_of_lt hk) := by
  classical
  -- product of strictly positive factors
  refine Finset.prod_pos ?_
  intro i hi
  -- each factor is a GS norm square at an index `< k < n`, so `i+1 < n`
  have hik : i.1 + 1 ≤ k := Nat.succ_le_of_lt i.2
  have hi1 : i.1 + 1 < n := Nat.lt_of_le_of_lt hik hk
  simpa using gsoNormSqQ_pos_of_RowLIQ (n := n) (B := B) (i := i.1) hi1 hli

lemma prefixProdNormSqQ_swap_adj_eq
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n) (hk0 : 0 < k) :
    let k' : Fin n := ⟨k, hk⟩
    let km1Nat : Nat := k - 1
    have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) hk
    let km1' : Fin n := ⟨km1Nat, hkm1⟩
    prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') k (Nat.le_of_lt hk) =
      prefixProdNormSqQ (n := n) B km1Nat (Nat.le_of_lt hkm1) *
        gsoNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1' := by
  classical
  intro k' km1Nat hkm1 km1'
  have hk_succ : km1Nat + 1 = k := Nat.succ_pred_eq_of_pos hk0
  -- use the “split off last index” product lemma on the swapped basis
  have hsplit :
      prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') k (Nat.le_of_lt hk) =
        prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1Nat (Nat.le_of_lt hkm1) *
          gsoNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1' := by
    -- rewrite `k` as `(k-1)+1`
    simpa [hk_succ, km1Nat] using
      (prefixProdNormSqQ_succ (n := n) (B := swap_vectors (n := n) B k' km1') km1Nat (by
        simpa [hk_succ] using (Nat.le_of_lt hk)))

  -- show the `(k-1)` prefix product is unchanged by swapping rows `k` and `k-1`
  have hjk : (km1' : ℕ) < (k' : ℕ) := by
    have hkPred : Nat.pred k < k := Nat.pred_lt (Nat.ne_of_gt hk0)
    have hkSub1 : k - 1 < k := by simpa [Nat.pred_eq_sub_one] using hkPred
    simpa [km1Nat, k', km1'] using hkSub1
  have hprefix_same :
      prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1Nat (Nat.le_of_lt hkm1) =
        prefixProdNormSqQ (n := n) B km1Nat (Nat.le_of_lt hkm1) := by
    -- products over indices `< k-1`, and `gsoNormSqQ` is stable there
    unfold prefixProdNormSqQ
    refine Finset.prod_congr rfl ?_
    intro i _hi
    -- `i < k-1`
    have ht : (i.1 : ℕ) < (km1' : ℕ) := by
      simpa [km1Nat, km1'] using i.2
    have hi_lt_n : (i.1 : ℕ) < n := Nat.lt_of_lt_of_le i.2 (Nat.le_of_lt hkm1)
    let t : Fin n := ⟨i.1, hi_lt_n⟩
    have ht' : (t : ℕ) < (km1' : ℕ) := by simpa [t] using ht
    -- rewrite the embedded indices back to the `Fin n` view, then use the stable GS lemma
    simpa [t] using
      (gsoNormSqQ_swap_vectors_of_lt (n := n) (B := B) (k := k') (j := km1') (t := t) hjk ht')

  simpa [hsplit, hprefix_same]

/-!
### Swap step: the key algebraic inequality target

For an adjacent swap `(k, k-1)`, the only nontrivial prefix determinant changes at prefix length `k`.
At the GS level, the new GS vector at index `k-1` is:

`u'_{k-1} = u_k + μ_{k,k-1} • u_{k-1}`,

so its squared norm is:

`‖u'_{k-1}‖² = ‖u_k‖² + μ² ‖u_{k-1}‖²`

by orthogonality. Under Lovász failure, this is strictly `< δ ‖u_{k-1}‖²`.
-/

lemma gsoAtQ_swap_adj_pred
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n) (hk0 : 0 < k)
    (_hli : RowLIQ (n := n) B) :
    let k' : Fin n := ⟨k, hk⟩
    let km1Nat : Nat := k - 1
    have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) hk
    let km1' : Fin n := ⟨km1Nat, hkm1⟩
    gsoAtQ (n := n) (swap_vectors (n := n) B k' km1') km1' =
      gsoAtQ (n := n) B k' + (muQ (n := n) B k' km1') • (gsoAtQ (n := n) B km1') := by
  classical
  intro k' km1Nat hkm1 km1'
  have hjk : (km1' : ℕ) < (k' : ℕ) := by
    -- `k-1 < k`
    have hkPred : Nat.pred k < k := Nat.pred_lt (Nat.ne_of_gt hk0)
    have hkSub1 : k - 1 < k := by simpa [Nat.pred_eq_sub_one] using hkPred
    simpa [km1Nat, k', km1'] using hkSub1

  -- Let `us0` be the GS prefix list up to `k-1`.
  let us0 : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B km1Nat (Nat.le_of_lt hkm1)

  -- Swapping `k` and `k-1` does not affect rows `< k-1`, hence `us0` is unchanged.
  have hmn : km1Nat ≤ n := Nat.le_of_lt hkm1
  have hswap_prefix :
      gsoPrefixListQ (n := n) (swap_vectors (n := n) B k' km1') km1Nat (Nat.le_of_lt hkm1) = us0 := by
    -- instantiate the general “swap doesn’t change prefix ≤ j” lemma with `j = k-1`, `m = k-1`
    simpa [us0] using
      (gsoPrefixListQ_swap_vectors_of_le (n := n) (B := B) (k := k') (j := km1')
        (hjk := hjk) (m := km1Nat) (hmj := le_rfl) (hmn := hmn))

  -- Rewrite `gsoAtQ` at `k-1` on the swapped matrix to a `gsoVectorForKPrefix` over `us0`.
  have hk1 : km1Nat + 1 ≤ n := Nat.succ_le_of_lt hkm1
  have hrow_km1_swap :
      rowQ (n := n) (swap_vectors (n := n) B k' km1') km1' = rowQ (n := n) B k' := by
    ext t
    simp [rowQ, swap_vectors]

  have hgs_swap :
      gsoAtQ (n := n) (swap_vectors (n := n) B k' km1') km1' =
        gsoVectorForKPrefix (n := n) (rowQ (n := n) B k') us0 := by
    -- `gsoAtQ_eq_gsoVectorForKPrefix` + `hswap_prefix` + the swapped row identity
    -- (make the `km1Nat` vs `km1'.val` coercions explicit with `simp`)
    simpa [km1', hrow_km1_swap, hswap_prefix] using
      (gsoAtQ_eq_gsoVectorForKPrefix (n := n) (B := swap_vectors (n := n) B k' km1') km1')

  -- Also rewrite `gsoAtQ` at `k` on the original matrix as folding over `us0 ++ [u_{k-1}]`.
  have hprefix_k :
      gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk) = us0 ++ [gsoAtQ (n := n) B km1'] := by
    -- unfold the `(k-1)+1` prefix and identify the last element with `gsoAtQ B (k-1)`
    have hk_succ : km1Nat + 1 = k := Nat.succ_pred_eq_of_pos hk0
    -- `gsoPrefixListQ_succ_eq_append` gives `us0 ++ [bstar]` for the last row at index `k-1`.
    rcases gsoPrefixListQ_succ_eq_append (n := n) (B := B) km1Nat (by simpa [hk_succ] using (Nat.le_of_lt hk))
      with ⟨us, bstar, hEq, hUs, hB⟩
    subst hUs
    -- `bstar` is exactly the `gsoAtQ` vector at `k-1`.
    have hbstar : bstar = gsoAtQ (n := n) B km1' := by
      -- `gsoAtQ_eq_gsoVectorForKPrefix` gives the same fold definition.
      simpa [gsoAtQ_eq_gsoVectorForKPrefix (n := n) (B := B) km1', us0] using hB
    -- rewrite the goal in terms of `hEq`
    simpa [hk_succ, us0, hbstar] using hEq

  have hgs_k :
      gsoAtQ (n := n) B k' =
        gsoVectorForKPrefix (n := n) (rowQ (n := n) B k') (us0 ++ [gsoAtQ (n := n) B km1']) := by
    -- `gsoAtQ` is `gsoVectorForKPrefix` against the `k`-prefix list.
    simpa [gsoAtQ_eq_gsoVectorForKPrefix (n := n) (B := B) k', hprefix_k, k']

  -- Finally, relate the “prefix-km1 GS vector for row k” to `gsoAtQ B k` by undoing the last update.
  -- `gsoAtQ B k = gsoVectorForKPrefix bk (us0 ++ [u]) = v - μ•u`, so `v = gsoAtQ B k + μ•u`.
  have : gsoVectorForKPrefix (n := n) (rowQ (n := n) B k') us0 =
      gsoAtQ (n := n) B k' + (muQ (n := n) B k' km1') • (gsoAtQ (n := n) B km1') := by
    -- start from the append-singleton lemma and rearrange
    have hmu : muQPrefix (n := n) (rowQ (n := n) B k') (gsoAtQ (n := n) B km1') =
        muQ (n := n) B k' km1' := by
      simp [muQ, muQPrefix]
    -- `gsoAtQ` rewrite (as a fold over `us0 ++ [u_{k-1}]`)
    have hfold :
        gsoVectorForKPrefix (n := n) (rowQ (n := n) B k') (us0 ++ [gsoAtQ (n := n) B km1']) =
          gsoVectorForKPrefix (n := n) (rowQ (n := n) B k') us0 -
            (muQ (n := n) B k' km1') • (gsoAtQ (n := n) B km1') := by
      simpa [hmu] using
        (gsoVectorForKPrefix_append_singleton (n := n) (bk := rowQ (n := n) B k') (us := us0)
          (u := gsoAtQ (n := n) B km1'))
    -- substitute `gsoAtQ B k'` for the LHS and solve for the prefix vector:
    -- `gsoAtQ = v - μ•u` implies `v = gsoAtQ + μ•u`.
    have hsub :
        gsoAtQ (n := n) B k' =
          gsoVectorForKPrefix (n := n) (rowQ (n := n) B k') us0 -
            (muQ (n := n) B k' km1') • (gsoAtQ (n := n) B km1') := by
      simpa [hgs_k] using hfold
    -- add back the subtracted term
    have :
        gsoVectorForKPrefix (n := n) (rowQ (n := n) B k') us0 =
          gsoAtQ (n := n) B k' + (muQ (n := n) B k' km1') • (gsoAtQ (n := n) B km1') := by
      -- `v = (v - a) + a` and rewrite `(v - a)` using `hsub.symm`
      calc
        gsoVectorForKPrefix (n := n) (rowQ (n := n) B k') us0
            =
            (gsoVectorForKPrefix (n := n) (rowQ (n := n) B k') us0 -
              (muQ (n := n) B k' km1') • (gsoAtQ (n := n) B km1')) +
              (muQ (n := n) B k' km1') • (gsoAtQ (n := n) B km1') := by
              abel
        _ = gsoAtQ (n := n) B k' + (muQ (n := n) B k' km1') • (gsoAtQ (n := n) B km1') := by
              simpa [hsub] using rfl
    exact this

  -- Combine the swapped-GS rewrite with the rearranged identity.
  simpa [hgs_swap] using this

lemma gsoNormSqQ_swap_adj_pred_eq
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n) (hk0 : 0 < k)
    (hli : RowLIQ (n := n) B) :
    let k' : Fin n := ⟨k, hk⟩
    let km1Nat : Nat := k - 1
    have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) hk
    let km1' : Fin n := ⟨km1Nat, hkm1⟩
    gsoNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1' =
      gsoNormSqQ (n := n) B k' + (muQ (n := n) B k' km1') ^ 2 * gsoNormSqQ (n := n) B km1' := by
  classical
  intro k' km1Nat hkm1 km1'
  let us0 : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B km1Nat (Nat.le_of_lt hkm1)
  -- shorthand
  let u_k : Fin n → ℚ := gsoAtQ (n := n) B k'
  let u_km1 : Fin n → ℚ := gsoAtQ (n := n) B km1'
  let μ : ℚ := muQ (n := n) B k' km1'
  have hswap :
      gsoAtQ (n := n) (swap_vectors (n := n) B k' km1') km1' = u_k + μ • u_km1 := by
    simpa [u_k, u_km1, μ] using
      (gsoAtQ_swap_adj_pred (n := n) (B := B) (k := k) (hk := hk) (hk0 := hk0) hli)

  -- Orthogonality: `u_k ⟂ u_km1` (GS vector is orthogonal to all previous prefix vectors).
  have hnz_k : ∀ u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk), dotQ (n := n) u u ≠ 0 := by
    exact HNZAt_of_RowLIQ (n := n) (B := B) (k := k) hk hli
  have horth_k :
      (gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk)).Pairwise (fun u w => dotQ (n := n) u w = 0) :=
    gsoPrefixListQ_pairwise_orth (n := n) (B := B) (k := k) (hk := Nat.le_of_lt hk) hnz_k

  -- show `u_km1 ∈ gsoPrefixListQ B k`
  have hu_km1_mem :
      u_km1 ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk) := by
    have hk_succ : km1Nat + 1 = k := Nat.succ_pred_eq_of_pos hk0
    rcases gsoPrefixListQ_succ_eq_append (n := n) (B := B) km1Nat (by simpa [hk_succ] using (Nat.le_of_lt hk))
      with ⟨us, bstar, hEq, hUs, hB⟩
    subst hUs
    have hbstar : bstar = u_km1 := by
      -- `bstar` is the GS vector for row `k-1`, which is exactly `gsoAtQ B (k-1)`.
      -- (`us0` is the `(k-1)` prefix list.)
      simpa [u_km1, us0, gsoAtQ_eq_gsoVectorForKPrefix (n := n) (B := B) km1'] using hB
    have hEq' :
        gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk) = us0 ++ [u_km1] := by
      simpa [hk_succ, us0, hbstar] using hEq
    -- membership in the appended singleton, then rewrite via `hEq'`
    have : u_km1 ∈ us0 ++ [u_km1] := by simp
    simpa [hEq'] using this

  have hdot : dotQ (n := n) u_k u_km1 = 0 := by
    -- `u_k` is the GS vector for row `k` against the `k`-prefix list; it is orthogonal to members of that list.
    have hu_k :
        u_k = gsoVectorForKPrefix (n := n) (rowQ (n := n) B k') (gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk)) := by
      simpa [u_k] using (gsoAtQ_eq_gsoVectorForKPrefix (n := n) (B := B) k')
    -- apply the fold orthogonality lemma for `u_km1 ∈ us`
    have : dotQ (n := n) (gsoVectorForKPrefix (n := n) (rowQ (n := n) B k') (gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk))) u_km1 = 0 := by
      exact dotQ_gsoVectorForKPrefix_mem_eq_zero (n := n)
        (bk := rowQ (n := n) B k')
        (us := gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk))
        horth_k hnz_k u_km1 hu_km1_mem
    simpa [hu_k] using this

  -- Expand the squared norm on the swapped side.
  calc
    gsoNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1'
        = dotQ (n := n) (gsoAtQ (n := n) (swap_vectors (n := n) B k' km1') km1')
            (gsoAtQ (n := n) (swap_vectors (n := n) B k' km1') km1') := by
            simp [gsoNormSqQ]
    _ = dotQ (n := n) (u_k + μ • u_km1) (u_k + μ • u_km1) := by
            simp [hswap]
    _ = dotQ (n := n) u_k u_k + (μ * μ) * dotQ (n := n) u_km1 u_km1 := by
            -- bilinearity + `dot(u_k,u_km1)=0`
            -- expand and kill cross terms using `hdot`
            simp [dotQ_add_left, dotQ_add_right, dotQ_smul_left, dotQ_smul_right, hdot, dotQ_comm,
              mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm, sub_eq_add_neg]
    _ = gsoNormSqQ (n := n) B k' + (muQ (n := n) B k' km1') ^ 2 * gsoNormSqQ (n := n) B km1' := by
            -- rewrite `μ*μ` as `μ^2` and unfold norms
            simp [gsoNormSqQ, u_k, u_km1, μ, pow_two, mul_assoc]

set_option maxHeartbeats 600000 in
lemma gsoNormSqQ_swap_adj_pred_lt_mul_delta_of_lovasz_fail
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (k : Nat) (hk : k < n) (hk0 : 0 < k) (hli : RowLIQ (n := n) B) :
    let k' : Fin n := ⟨k, hk⟩
    let km1Nat : Nat := k - 1
    have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) hk
    let km1' : Fin n := ⟨km1Nat, hkm1⟩
    lovaszQ (n := n) B k' km1' δ = false →
      gsoNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1' <
        δ * gsoNormSqQ (n := n) B km1' := by
  classical
  intro k' km1Nat hkm1 km1' hlov
  -- unpack the Lovász failure into an inequality
  have hnot_ge :
      ¬ (gsoNormSqQ (n := n) B k' ≥
          (δ - (muQ (n := n) B k' km1') ^ 2) * gsoNormSqQ (n := n) B km1') := by
    -- `lovaszQ` is `decide (lhs ≥ rhs)`
    have : decide
        (gsoNormSqQ (n := n) B k' ≥
          (δ - (muQ (n := n) B k' km1') ^ 2) * gsoNormSqQ (n := n) B km1') = false := by
      simpa [lovaszQ, k', km1'] using hlov
    exact (decide_eq_false_iff_not).1 this

  have hlt :
      gsoNormSqQ (n := n) B k' <
        (δ - (muQ (n := n) B k' km1') ^ 2) * gsoNormSqQ (n := n) B km1' :=
    lt_of_not_ge hnot_ge

  -- rewrite the swapped norm via the explicit GS update formula, then add `μ^2 * ‖u_{k-1}‖²` to both sides
  have hswap_eq :
      gsoNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1' =
        gsoNormSqQ (n := n) B k' +
          (muQ (n := n) B k' km1') ^ 2 * gsoNormSqQ (n := n) B km1' := by
    simpa [k', km1', km1Nat] using
      (gsoNormSqQ_swap_adj_pred_eq (n := n) (B := B) (k := k) (hk := hk) (hk0 := hk0) hli)

  -- add the same term to the strict inequality
  have hlt' :
      gsoNormSqQ (n := n) B k' + (muQ (n := n) B k' km1') ^ 2 * gsoNormSqQ (n := n) B km1' <
        (δ - (muQ (n := n) B k' km1') ^ 2) * gsoNormSqQ (n := n) B km1' +
          (muQ (n := n) B k' km1') ^ 2 * gsoNormSqQ (n := n) B km1' :=
    by
      -- add `μ^2 * ‖u_{k-1}‖²` to the right of both sides
      have h := add_lt_add_right hlt ((muQ (n := n) B k' km1') ^ 2 * gsoNormSqQ (n := n) B km1')
      -- normalize the (commutative) additions into the target shape
      simpa [add_assoc, add_left_comm, add_comm] using h

  -- simplify the RHS to `δ * ‖u_{k-1}‖²`
  have hsum :
      (δ - (muQ (n := n) B k' km1') ^ 2) * gsoNormSqQ (n := n) B km1' +
          (muQ (n := n) B k' km1') ^ 2 * gsoNormSqQ (n := n) B km1'
        =
      δ * gsoNormSqQ (n := n) B km1' := by
    -- `(δ - b) * a + b * a = δ * a`
    simp [sub_eq_add_neg, add_mul, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]

  -- conclude
  simpa [hswap_eq, hsum] using hlt'

lemma prefixProdNormSqQ_swap_adj_lt_mul_delta_of_lovasz_fail
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (k : Nat) (hk : k < n) (hk0 : 0 < k) (hli : RowLIQ (n := n) B) :
    let k' : Fin n := ⟨k, hk⟩
    let km1Nat : Nat := k - 1
    have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) hk
    let km1' : Fin n := ⟨km1Nat, hkm1⟩
    lovaszQ (n := n) B k' km1' δ = false →
      prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') k (Nat.le_of_lt hk) <
        δ * prefixProdNormSqQ (n := n) B k (Nat.le_of_lt hk) := by
  classical
  intro k' km1Nat hkm1 km1' hlov
  have hk_succ : km1Nat + 1 = k := Nat.succ_pred_eq_of_pos hk0

  -- expand the prefix products at `k = (k-1)+1`
  have hP :
      prefixProdNormSqQ (n := n) B k (Nat.le_of_lt hk) =
        prefixProdNormSqQ (n := n) B km1Nat (Nat.le_of_lt hkm1) * gsoNormSqQ (n := n) B km1' := by
    simpa [hk_succ, km1Nat] using
      (prefixProdNormSqQ_succ (n := n) (B := B) km1Nat (by
        simpa [hk_succ] using (Nat.le_of_lt hk)))

  have hPswap :
      prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') k (Nat.le_of_lt hk) =
        prefixProdNormSqQ (n := n) B km1Nat (Nat.le_of_lt hkm1) *
          gsoNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1' := by
    simpa [k', km1Nat, km1'] using
      (prefixProdNormSqQ_swap_adj_eq (n := n) (B := B) (k := k) (hk := hk) (hk0 := hk0))

  -- the strict shrink on the swapped GS norm (Lovász failure leaf)
  have hshrink :
      gsoNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1' <
        δ * gsoNormSqQ (n := n) B km1' := by
    simpa [k', km1Nat, km1'] using
      (gsoNormSqQ_swap_adj_pred_lt_mul_delta_of_lovasz_fail (n := n) (B := B) (δ := δ)
        (k := k) (hk := hk) (hk0 := hk0) hli hlov)

  -- multiply the strict inequality by the positive prefix product up to `k-1`
  have hpos :
      (0 : ℚ) < prefixProdNormSqQ (n := n) B km1Nat (Nat.le_of_lt hkm1) := by
    simpa [km1Nat] using prefixProdNormSqQ_pos_of_RowLIQ (n := n) (B := B) (k := km1Nat) hkm1 hli

  have hmul : prefixProdNormSqQ (n := n) B km1Nat (Nat.le_of_lt hkm1) *
        gsoNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1' <
      prefixProdNormSqQ (n := n) B km1Nat (Nat.le_of_lt hkm1) * (δ * gsoNormSqQ (n := n) B km1') :=
    mul_lt_mul_of_pos_left hshrink hpos

  -- rearrange to match the goal
  calc
    prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') k (Nat.le_of_lt hk)
        = prefixProdNormSqQ (n := n) B km1Nat (Nat.le_of_lt hkm1) *
            gsoNormSqQ (n := n) (swap_vectors (n := n) B k' km1') km1' := by
            simpa [hPswap]
    _ < prefixProdNormSqQ (n := n) B km1Nat (Nat.le_of_lt hkm1) * (δ * gsoNormSqQ (n := n) B km1') := hmul
    _ = δ * (prefixProdNormSqQ (n := n) B km1Nat (Nat.le_of_lt hkm1) * gsoNormSqQ (n := n) B km1') := by
            ring_nf
    _ = δ * prefixProdNormSqQ (n := n) B k (Nat.le_of_lt hk) := by
            simpa [hP, mul_assoc]

/-!
### Swap-step decrease for `potentialVQ`

All prefix factors except the `k`-prefix are invariant under an adjacent swap at `k`;
the `k`-prefix factor shrinks by a `δ` factor when `lovaszQ` fails.
-/

lemma potentialVQ_swap_adj_lt_mul_delta_of_lovasz_fail
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (k : Nat) (hk : k < n) (hk0 : 0 < k) (hli : RowLIQ (n := n) B) :
    let k' : Fin n := ⟨k, hk⟩
    let km1Nat : Nat := k - 1
    have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) hk
    let km1' : Fin n := ⟨km1Nat, hkm1⟩
    lovaszQ (n := n) B k' km1' δ = false →
      potentialVQ (n := n) (swap_vectors (n := n) B k' km1') < δ * potentialVQ (n := n) B := by
  classical
  intro k' km1Nat hkm1 km1' hlov
  let fB : Fin n → ℚ := fun t => prefixProdNormSqQ (n := n) B t.1 (Nat.le_of_lt t.2)
  let fS : Fin n → ℚ := fun t =>
    prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') t.1 (Nat.le_of_lt t.2)

  have hk_mem : k' ∈ (Finset.univ : Finset (Fin n)) := by simp

  -- For `t ≠ k'`, the prefix factor is unchanged (swap is either outside the prefix or a pure reindex).
  have h_other : ∀ t : Fin n, t ≠ k' → fS t = fB t := by
    intro t htne
    by_cases hlt : (t.1 : Nat) < k
    · -- swap is outside the prefix
      simpa [fB, fS, k', km1Nat, km1'] using
        (prefixProdNormSqQ_swap_adj_of_lt (n := n) (B := B)
          (k := k) (hk := hk) (hk0 := hk0) (m := t.1) hlt hli)
    · -- `t.1 ≥ k`; since `t ≠ k'`, we have `t.1 > k`, so the swap is within the prefix and only reindexes.
      have hgt : k < t.1 := by
        have hle : k ≤ t.1 := Nat.le_of_not_gt hlt
        have hne : t.1 ≠ k := by
          intro h
          apply htne
          apply Fin.ext
          simpa [k'] using h
        exact lt_of_le_of_ne hle (by simpa [eq_comm] using hne)
      have hkm1_lt_t : km1Nat < t.1 := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) hgt
      have ht_le_n : t.1 ≤ n := Nat.le_of_lt t.2
      -- re-express the swap indices as casts from the `t.1`-prefix, then use determinant invariance + bridge.
      let a : Fin t.1 := ⟨k, hgt⟩
      let b : Fin t.1 := ⟨km1Nat, hkm1_lt_t⟩
      have hcast_a : Fin.castLE ht_le_n a = k' := by
        apply Fin.ext; rfl
      have hcast_b : Fin.castLE ht_le_n b = km1' := by
        apply Fin.ext; rfl
      have hdet :
          Matrix.det
              (gramPrefixQ (n := n)
                  (swap_vectors (n := n) B (Fin.castLE ht_le_n a) (Fin.castLE ht_le_n b))
                  t.1 ht_le_n)
            =
            Matrix.det (gramPrefixQ (n := n) B t.1 ht_le_n) := by
        simpa using (det_gramPrefixQ_swap_vectors (n := n) (B := B) (hk := ht_le_n) (a := a) (b := b))
      have hliS : RowLIQ (n := n) (swap_vectors (n := n) B k' km1') :=
        RowLIQ_swap_vectors (n := n) (B := B) (k := k') (j := km1') hli
      have hbridgeS :=
        det_gramPrefixQ_eq_prefixProdNormSqQ_of_RowLIQ (n := n)
          (B := swap_vectors (n := n) B k' km1') (k := t.1) (hk := ht_le_n) hliS
      have hbridgeB :=
        det_gramPrefixQ_eq_prefixProdNormSqQ_of_RowLIQ (n := n)
          (B := B) (k := t.1) (hk := ht_le_n) hli
      -- rewrite the `swap_vectors` in `hdet` to our concrete swap using the cast equalities
      have hdet' :
          Matrix.det
              (gramPrefixQ (n := n) (swap_vectors (n := n) B k' km1') t.1 ht_le_n)
            =
            Matrix.det (gramPrefixQ (n := n) B t.1 ht_le_n) := by
        simpa [hcast_a, hcast_b] using hdet
      -- now transfer determinants to `prefixProdNormSqQ`
      have :
          prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') t.1 ht_le_n =
            prefixProdNormSqQ (n := n) B t.1 ht_le_n := by
        simpa [hbridgeS, hbridgeB] using hdet'
      simpa [fB, fS] using this

  -- the `k`-prefix strict shrink
  have hk_shrink :
      prefixProdNormSqQ (n := n) (swap_vectors (n := n) B k' km1') k (Nat.le_of_lt hk) <
        δ * prefixProdNormSqQ (n := n) B k (Nat.le_of_lt hk) := by
    simpa [k', km1Nat, km1'] using
      (prefixProdNormSqQ_swap_adj_lt_mul_delta_of_lovasz_fail (n := n) (B := B) (δ := δ)
        (k := k) (hk := hk) (hk0 := hk0) hli hlov)

  -- split the product at `k'` using `insert/erase`
  have hunivS :
      (Finset.univ : Finset (Fin n)).prod fS =
        fS k' * ((Finset.univ : Finset (Fin n)).erase k').prod fS := by
    -- `mul_prod_erase` is the stable way to split a product at one element.
    simpa using
      (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n))) (f := fS) hk_mem).symm

  have hunivB :
      (Finset.univ : Finset (Fin n)).prod fB =
        fB k' * ((Finset.univ : Finset (Fin n)).erase k').prod fB := by
    simpa using
      (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n))) (f := fB) hk_mem).symm

  -- the erased product is unchanged
  have herase :
      ((Finset.univ : Finset (Fin n)).erase k').prod fS =
        ((Finset.univ : Finset (Fin n)).erase k').prod fB := by
    refine Finset.prod_congr rfl ?_
    intro t ht
    have htne : t ≠ k' := (Finset.mem_erase.mp ht).1
    simpa using (h_other t htne)

  -- positivity of the other-factor product
  have hpos_other :
      (0 : ℚ) < ((Finset.univ : Finset (Fin n)).erase k').prod fB := by
    refine Finset.prod_pos ?_
    intro t ht
    -- `prefixProdNormSqQ_pos_of_RowLIQ` gives positivity for every prefix
    simpa [fB] using
      (prefixProdNormSqQ_pos_of_RowLIQ (n := n) (B := B) (k := t.1) t.2 hli)

  -- combine the strict shrink at `k` with invariance of all other factors
  have hmain :
      (Finset.univ : Finset (Fin n)).prod fS < δ * (Finset.univ : Finset (Fin n)).prod fB := by
    rw [hunivS, hunivB, herase]
    have hk_term : fS k' < δ * fB k' := by
      simpa [fB, fS, k'] using hk_shrink
    have hmul := mul_lt_mul_of_pos_right hk_term hpos_other
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

  simpa [potentialVQ, fB, fS] using hmain

/-!
## Termination: a Nat-valued potential + a strictly decreasing measure

`lllRunExactGo` is fuel-bounded by construction. A termination proof here means:

- there exists a bound `T(B, δ)` such that for all `limit ≥ T`, the runner reaches `.finished`.

We avoid `Real.log` by using:
- an **integer** version of the prefix-volume potential (`potentialVZ`), and
- a **Nat** measure that strictly decreases each runner step.
-/

/-!
### Integer / Nat potential

Each `k`-prefix Gram determinant is an integer (in fact, a nonnegative integer), and under `RowLIQ`
it is strictly positive. We package the product of these determinants as an integer potential,
then take `Int.toNat` to get a well-founded `Nat` measure.
-/

def potentialVZ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℤ :=
  (Finset.univ : Finset (Fin n)).prod (fun k =>
    Matrix.det (gramPrefixZ (n := n) B k.1 (Nat.le_of_lt k.2)))

def potentialVN {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Nat :=
  Int.toNat (potentialVZ (n := n) B)

lemma prefixProdNormSqQ_eq_cast_det_gramPrefixZ_of_RowLIQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n)
    (hli : RowLIQ (n := n) B) :
    prefixProdNormSqQ (n := n) B k hk =
      ((Matrix.det (gramPrefixZ (n := n) B k hk) : ℤ) : ℚ) := by
  classical
  have hbridge :=
    det_gramPrefixQ_eq_prefixProdNormSqQ_of_RowLIQ (n := n) (B := B) (k := k) hk hli
  have hcast :=
    det_gramPrefixQ_eq_cast_det_gramPrefixZ (n := n) (B := B) (k := k) hk
  -- both sides are equal to `det (gramPrefixQ ...)`
  exact (hbridge.symm.trans hcast)

lemma potentialVQ_eq_cast_potentialVZ_of_RowLIQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hli : RowLIQ (n := n) B) :
    potentialVQ (n := n) B = ((potentialVZ (n := n) B : ℤ) : ℚ) := by
  classical
  -- expand both products; use the per-prefix cast lemma
  simp [potentialVQ, potentialVZ, prefixProdNormSqQ_eq_cast_det_gramPrefixZ_of_RowLIQ (n := n) (B := B) (hli := hli)]

lemma potentialVZ_pos_of_RowLIQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hli : RowLIQ (n := n) B) :
    (0 : ℤ) < potentialVZ (n := n) B := by
  classical
  -- cast to `ℚ` and use positivity of each prefix product
  have hq :
      (0 : ℚ) < ((potentialVZ (n := n) B : ℤ) : ℚ) := by
    -- rewrite cast potential as the rational potential, then use `prod_pos`
    have hEq := (potentialVQ_eq_cast_potentialVZ_of_RowLIQ (n := n) (B := B) hli).symm
    -- `potentialVQ` is a product of positive factors under `RowLIQ`
    have hpos : (0 : ℚ) < potentialVQ (n := n) B := by
      -- each factor is positive
      refine Finset.prod_pos ?_
      intro k hk
      simpa [potentialVQ] using
        (prefixProdNormSqQ_pos_of_RowLIQ (n := n) (B := B) (k := k.1) k.2 hli)
    simpa [hEq] using hpos
  -- now reflect back to `ℤ`
  exact_mod_cast hq

/-!
### Size-reduction preserves `potentialVZ` / `potentialVN`

`sizeReduceAllExactWithPrefix` is a fold of `size_reduceZ` updates at indices `(k,j)` with `j<k`.
For any prefix length `m`:
- if `m ≤ k`, the update happens *after* the prefix, so the prefix Gram matrix is unchanged;
- if `k < m`, the update is within the prefix, so the prefix Gram determinant is unchanged by
  `det_gramPrefixZ_size_reduceZ_within_prefix`.

Therefore the *product over all prefix determinants* is invariant.
-/

lemma det_gramPrefixZ_size_reduceZ_at_kj
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k j : Nat) (hk : k < n) (hj : j < k)
    (q : ℤ) (m : Nat) (hm : m ≤ n) :
    Matrix.det (gramPrefixZ (n := n) (size_reduceZ (n := n) B ⟨k, hk⟩ ⟨j, Nat.lt_trans hj hk⟩ q) m hm) =
      Matrix.det (gramPrefixZ (n := n) B m hm) := by
  classical
  by_cases hm_le : m ≤ k
  · -- `k` is outside the `m`-prefix, so `prefixRowsZ` is unchanged
    have hk_out : ∀ i : Fin m, (Fin.castLE hm i : Fin n) ≠ ⟨k, hk⟩ := by
      intro i hEq
      have : (Fin.castLE hm i).1 = k := congrArg Fin.val hEq
      have hi_lt : (Fin.castLE hm i).1 < k := by
        -- `i.1 < m ≤ k`
        have : (Fin.castLE hm i).1 < m := i.2
        exact Nat.lt_of_lt_of_le this hm_le
      exact (Nat.ne_of_lt hi_lt) this
    have hPR :
        prefixRowsZ (n := n) (size_reduceZ (n := n) B ⟨k, hk⟩ ⟨j, Nat.lt_trans hj hk⟩ q) m hm =
          prefixRowsZ (n := n) B m hm := by
      ext i t
      have hne : (Fin.castLE hm i : Fin n) ≠ ⟨k, hk⟩ := hk_out i
      -- `size_reduceZ` only updates row `k`
      simp [prefixRowsZ, size_reduceZ, Matrix.updateRow_ne, hne]
    -- rewrite Gram via `P*Pᵀ`
    calc
      Matrix.det (gramPrefixZ (n := n) (size_reduceZ (n := n) B ⟨k, hk⟩ ⟨j, Nat.lt_trans hj hk⟩ q) m hm)
          = Matrix.det
              (prefixRowsZ (n := n) (size_reduceZ (n := n) B ⟨k, hk⟩ ⟨j, Nat.lt_trans hj hk⟩ q) m hm *
                (prefixRowsZ (n := n) (size_reduceZ (n := n) B ⟨k, hk⟩ ⟨j, Nat.lt_trans hj hk⟩ q) m hm).transpose) := by
                simp [gramPrefixZ_eq_prefixRowsZ_mul_transpose]
      _ = Matrix.det (prefixRowsZ (n := n) B m hm * (prefixRowsZ (n := n) B m hm).transpose) := by
                simp [hPR]
      _ = Matrix.det (gramPrefixZ (n := n) B m hm) := by
                simp [gramPrefixZ_eq_prefixRowsZ_mul_transpose]
  · -- `k < m`: the update is within the prefix, use the within-prefix determinant invariance lemma
    have hk_m : k < m := Nat.lt_of_not_ge hm_le
    have hj_m : j < m := Nat.lt_trans hj hk_m
    let a : Fin m := ⟨k, hk_m⟩
    let b : Fin m := ⟨j, hj_m⟩
    have hab : a ≠ b := by
      intro h
      have : k = j := congrArg Fin.val h
      exact (Nat.ne_of_gt hj) this
    have hk_cast : (Fin.castLE hm a : Fin n) = ⟨k, hk⟩ := by
      apply Fin.ext; rfl
    have hj_cast : (Fin.castLE hm b : Fin n) = ⟨j, Nat.lt_trans hj hk⟩ := by
      apply Fin.ext; rfl
    -- apply the within-prefix lemma, then rewrite casts
    have hdet :=
      det_gramPrefixZ_size_reduceZ_within_prefix (n := n) (B := B) (k := m) hm (a := a) (b := b) (q := q) hab
    simpa [hk_cast, hj_cast] using hdet

lemma potentialVZ_size_reduceZ_at_kj
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k j : Nat) (hk : k < n) (hj : j < k) (q : ℤ) :
    potentialVZ (n := n) (size_reduceZ (n := n) B ⟨k, hk⟩ ⟨j, Nat.lt_trans hj hk⟩ q) =
      potentialVZ (n := n) B := by
  classical
  -- pointwise determinant invariance for every prefix length `m < n`
  refine Finset.prod_congr rfl ?_
  intro m hm
  have hm' : (m.1 : Nat) ≤ n := Nat.le_of_lt m.2
  simpa [potentialVZ] using
    (det_gramPrefixZ_size_reduceZ_at_kj (n := n) (B := B) (k := k) (j := j) hk hj q (m := m.1) hm')

lemma potentialVZ_sizeReduceAllExactWithUs
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n) (us : List (Fin n → ℚ)) :
    potentialVZ (n := n) (sizeReduceAllExactWithUs (n := n) B k hk us) = potentialVZ (n := n) B := by
  classical
  unfold sizeReduceAllExactWithUs
  set js : List (Fin k) := List.ofFn (α := Fin k) (fun j : Fin k => j)
  let k' : Fin n := ⟨k, hk⟩
  let step : Fin k → Matrix (Fin n) (Fin n) ℤ → Matrix (Fin n) (Fin n) ℤ :=
    fun (j : Fin k) acc =>
      let j' : Fin n := ⟨(j : Nat), Nat.lt_trans j.2 hk⟩
      let uj : Fin n → ℚ := us.getD j.val (zeroVecQ (n := n))
      let bk : Fin n → ℚ := rowQ (n := n) acc k'
      let μ : ℚ := muQPrefix (n := n) bk uj
      let q : ℤ := roundQ μ
      size_reduceZ (n := n) acc k' j' q
  -- prove invariance by induction over the explicit `Fin k` list
  revert B
  induction js with
  | nil =>
      intro B
      simp [js, step, potentialVZ]
  | cons a tl ih =>
      intro B
      have ha_lt : (a : ℕ) < k := a.2
      -- foldr recursion: `step a (foldr step B tl)`
      have hrest : potentialVZ (n := n) (List.foldr step B tl) = potentialVZ (n := n) B := by
        simpa [js] using ih (B := B)
      -- one-step invariance at `(k,a)` (the concrete `q` doesn't matter)
      have hstep :
          potentialVZ (n := n) (step a (List.foldr step B tl)) =
            potentialVZ (n := n) (List.foldr step B tl) := by
        -- unfold the step and apply `potentialVZ_size_reduceZ_at_kj`
        simp [step, k', potentialVZ_size_reduceZ_at_kj (n := n) (k := k) (hk := hk) (j := a.1) (hj := ha_lt)]
      -- combine: `foldr step B (a::tl) = step a (foldr step B tl)`
      calc
        potentialVZ (n := n) (List.foldr step B (a :: tl))
            = potentialVZ (n := n) (step a (List.foldr step B tl)) := by rfl
        _ = potentialVZ (n := n) (List.foldr step B tl) := hstep
        _ = potentialVZ (n := n) B := hrest

lemma potentialVZ_sizeReduceAllExactWithPrefix
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n) :
    potentialVZ (n := n) (sizeReduceAllExactWithPrefix (n := n) B k hk) = potentialVZ (n := n) B := by
  classical
  simp [sizeReduceAllExactWithPrefix, potentialVZ_sizeReduceAllExactWithUs (n := n) (B := B) (k := k) hk]

lemma potentialVN_sizeReduceAllExactWithPrefix
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n) :
    potentialVN (n := n) (sizeReduceAllExactWithPrefix (n := n) B k hk) = potentialVN (n := n) B := by
  simp [potentialVN, potentialVZ_sizeReduceAllExactWithPrefix (n := n) (B := B) (k := k) hk]

/-!
### Swap strictly decreases the integer/Nat potential (when \(0<\delta<1\))
-/

lemma potentialVZ_swap_adj_lt_of_lovasz_fail
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (k : Nat) (hk : k < n) (hk0 : 0 < k)
    (hli : RowLIQ (n := n) B) (hδlt : δ < 1) :
    let k' : Fin n := ⟨k, hk⟩
    let km1Nat : Nat := k - 1
    have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) hk
    let km1' : Fin n := ⟨km1Nat, hkm1⟩
    lovaszQ (n := n) B k' km1' δ = false →
      potentialVZ (n := n) (swap_vectors (n := n) B k' km1') < potentialVZ (n := n) B := by
  classical
  intro k' km1Nat hkm1 km1' hlov
  let B2 : Matrix (Fin n) (Fin n) ℤ := swap_vectors (n := n) B k' km1'
  have hli2 : RowLIQ (n := n) B2 := RowLIQ_swap_vectors (n := n) (B := B) (k := k') (j := km1') hli
  have hVQ :
      potentialVQ (n := n) B2 < δ * potentialVQ (n := n) B := by
    simpa [B2] using
      (potentialVQ_swap_adj_lt_mul_delta_of_lovasz_fail (n := n) (B := B) (δ := δ)
        (k := k) (hk := hk) (hk0 := hk0) hli hlov)
  -- rewrite both potentials as casts of `potentialVZ`
  have hcastB : potentialVQ (n := n) B = ((potentialVZ (n := n) B : ℤ) : ℚ) :=
    potentialVQ_eq_cast_potentialVZ_of_RowLIQ (n := n) (B := B) hli
  have hcast2 : potentialVQ (n := n) B2 = ((potentialVZ (n := n) B2 : ℤ) : ℚ) :=
    potentialVQ_eq_cast_potentialVZ_of_RowLIQ (n := n) (B := B2) hli2
  have hVQ' :
      ((potentialVZ (n := n) B2 : ℤ) : ℚ) < δ * ((potentialVZ (n := n) B : ℤ) : ℚ) := by
    -- avoid simp-unfolding `potentialVQ`; rewrite explicitly
    have h := hVQ
    -- rewrite both sides to the casted-integer form
    -- (use `rw` to avoid triggering `[simp]` unfolding of `potentialVQ`)
    rw [hcast2, hcastB] at h
    simpa using h
  have hz_pos : (0 : ℤ) < potentialVZ (n := n) B := potentialVZ_pos_of_RowLIQ (n := n) (B := B) hli
  have hz_posQ : (0 : ℚ) < ((potentialVZ (n := n) B : ℤ) : ℚ) := by exact_mod_cast hz_pos
  have hmul_lt : δ * ((potentialVZ (n := n) B : ℤ) : ℚ) < ((potentialVZ (n := n) B : ℤ) : ℚ) := by
    -- `δ < 1` and the cast is positive
    have := mul_lt_mul_of_pos_right hδlt hz_posQ
    simpa [one_mul] using this
  have hltQ : ((potentialVZ (n := n) B2 : ℤ) : ℚ) < ((potentialVZ (n := n) B : ℤ) : ℚ) :=
    lt_trans hVQ' hmul_lt
  exact_mod_cast hltQ

lemma potentialVN_swap_adj_lt_of_lovasz_fail
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (k : Nat) (hk : k < n) (hk0 : 0 < k)
    (hli : RowLIQ (n := n) B) (hδlt : δ < 1) :
    let k' : Fin n := ⟨k, hk⟩
    let km1Nat : Nat := k - 1
    have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) hk
    let km1' : Fin n := ⟨km1Nat, hkm1⟩
    lovaszQ (n := n) B k' km1' δ = false →
      potentialVN (n := n) (swap_vectors (n := n) B k' km1') < potentialVN (n := n) B := by
  classical
  intro k' km1Nat hkm1 km1' hlov
  have hz_pos : (0 : ℤ) < potentialVZ (n := n) B := potentialVZ_pos_of_RowLIQ (n := n) (B := B) hli
  have hz_lt : potentialVZ (n := n) (swap_vectors (n := n) B k' km1') < potentialVZ (n := n) B :=
    potentialVZ_swap_adj_lt_of_lovasz_fail (n := n) (B := B) (δ := δ)
      (k := k) (hk := hk) (hk0 := hk0) hli hδlt hlov
  -- convert strict ℤ inequality to strict Nat inequality via `Int.toNat_lt_toNat`
  have : Int.toNat (potentialVZ (n := n) (swap_vectors (n := n) B k' km1')) <
      Int.toNat (potentialVZ (n := n) B) := by
    exact (Int.toNat_lt_toNat hz_pos).mpr hz_lt
  simpa [potentialVN] using this

/-!
### A strictly-decreasing measure for the runner

We use

\[
M(B,k) := \mathrm{potentialVN}(B)\cdot(n+1) + (n-k).
\]

- size-reduction preserves `potentialVN`;
- Lovász-success increases `k` (so `n-k` decreases);
- Lovász-failure swaps and strictly decreases `potentialVN` (enough to dominate the `+1` bump in `n-k`).
-/

def termMeasure {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) : Nat :=
  potentialVN (n := n) B * (n + 1) + (n - k)

lemma termMeasure_k0_lt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hn : 0 < n) :
    termMeasure (n := n) B 1 < termMeasure (n := n) B 0 := by
  -- only the `(n-k)` tail changes
  have hn' : n ≠ 0 := Nat.ne_of_gt hn
  have hpred : n - 1 < n := by
    -- `Nat.pred n < n` for `n ≠ 0`
    simpa [Nat.pred_eq_sub_one] using (Nat.pred_lt hn')
  -- `termMeasure B 1 = pot*(n+1) + (n-1)` and `termMeasure B 0 = pot*(n+1) + n`
  simpa [termMeasure, Nat.sub_zero] using
    (Nat.add_lt_add_left hpred (potentialVN (n := n) B * (n + 1)))

lemma termMeasure_lovasz_success_lt
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n) :
    termMeasure (n := n) B (k + 1) < termMeasure (n := n) B k := by
  -- same potential, and `n-(k+1) < n-k`
  have hsub : n - (k + 1) < n - k := by
    -- use `Nat.sub_sub` to rewrite `n - (k+1) = (n-k) - 1`, then apply `pred_lt`
    have hpos : 0 < n - k := Nat.sub_pos_of_lt hk
    have hne : n - k ≠ 0 := Nat.ne_of_gt hpos
    have hpred : (n - k) - 1 < n - k := by
      simpa [Nat.pred_eq_sub_one] using (Nat.pred_lt hne)
    -- `(n-k) - 1 = n - (k+1)`
    have hrew : (n - k) - 1 = n - (k + 1) := by
      -- `(n-k) - 1 = n - (k+1)` via `sub_sub`
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Nat.sub_sub n k 1)
    simpa [hrew] using hpred
  -- add a common constant term
  simpa [termMeasure, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (Nat.add_lt_add_left hsub (potentialVN (n := n) B * (n + 1)))

lemma termMeasure_swap_lt
    {n : ℕ} (B1 B2 : Matrix (Fin n) (Fin n) ℤ) (k : Nat)
    (hk0 : 0 < k) (hk : k < n)
    (hpot : potentialVN (n := n) B2 < potentialVN (n := n) B1) :
    termMeasure (n := n) B2 (k - 1) < termMeasure (n := n) B1 k := by
  -- set `a = pot(B1)`, `b = pot(B2)`
  set a : Nat := potentialVN (n := n) B1
  set b : Nat := potentialVN (n := n) B2
  have hn : 0 < n := Nat.lt_trans hk0 hk
  have hone : 1 < n + 1 := Nat.succ_lt_succ hn
  have hb1le : b + 1 ≤ a := Nat.succ_le_of_lt (by simpa [a, b] using hpot)
  have hmul_le : (b + 1) * (n + 1) ≤ a * (n + 1) := Nat.mul_le_mul_right (n + 1) hb1le
  have hlt1 : b * (n + 1) + 1 < (b + 1) * (n + 1) := by
    -- `b*(n+1)+1 < b*(n+1)+(n+1) = (b+1)*(n+1)` because `1 < n+1`
    have : b * (n + 1) + 1 < b * (n + 1) + (n + 1) := Nat.add_lt_add_left hone (b * (n + 1))
    simpa [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using this
  have hmul_lt : b * (n + 1) + 1 < a * (n + 1) := lt_of_lt_of_le hlt1 hmul_le
  -- rewrite the `n - (k-1)` tail as `(n-k)+1` using `k = succ k'`
  cases k with
  | zero =>
      cases (Nat.lt_irrefl 0 hk0)
  | succ k' =>
      -- now `k - 1 = k'` and `k = k'+1`
      have hk' : k' < n := Nat.lt_of_succ_lt hk
      let x : Nat := n - k'
      have hxpos : 0 < x := Nat.sub_pos_of_lt hk'
      -- relate the tails: `(n-(k'+1)) + 1 = n-k'`
      have htail : (n - (k' + 1)) + 1 = x := by
        -- `x - 1 = n - (k'+1)` by `sub_sub`
        have hxrew : x - 1 = n - (k' + 1) := by
          -- `(n-k') - 1 = n - (k'+1)`
          simpa [x, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (Nat.sub_sub n k' 1)
        have hxback : (x - 1) + 1 = x := by
          -- `pred x + 1 = x` for `x>0`
          have : Nat.pred x + 1 = x := by
            simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hxpos)
          simpa [Nat.pred_eq_sub_one, Nat.add_assoc] using this
        -- rewrite `n - (k'+1)` to `x-1` and finish
        calc
          (n - (k' + 1)) + 1 = (x - 1) + 1 := by simpa [hxrew] using rfl
          _ = x := hxback
      -- add `(n-(k'+1))` to `b*(n+1)+1 < a*(n+1)`
      have h := Nat.add_lt_add_right hmul_lt (n - (k' + 1))
      -- normalize to the `termMeasure` shapes
      -- LHS: `b*(n+1) + (n-k')`  (since `(n-(k'+1))+1 = n-k'`)
      -- RHS: `a*(n+1) + (n-(k'+1))`
      have h' :
          b * (n + 1) + x < a * (n + 1) + (n - (k' + 1)) := by
        -- rewrite `x = (n-(k'+1)) + 1` and reassociate
        have hx : x = (n - (k' + 1)) + 1 := by
          -- `htail : (n-(k'+1))+1 = x`
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htail.symm
        -- now `b*(n+1)+x = (b*(n+1)+1)+(n-(k'+1))`
        calc
          b * (n + 1) + x
              = (b * (n + 1) + 1) + (n - (k' + 1)) := by
                  -- commute the `+1` to the front of the tail
                  simp [hx, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          _ < a * (n + 1) + (n - (k' + 1)) := by
                  simpa [Nat.add_assoc] using h
      -- now match the goal `termMeasure B2 k' < termMeasure B1 (k'+1)`
      simpa [termMeasure, a, b, x, Nat.succ_eq_add_one] using h'

lemma termMeasure_congr_potentialVN
    {n : ℕ} {B B' : Matrix (Fin n) (Fin n) ℤ} (k : Nat)
    (h : potentialVN (n := n) B' = potentialVN (n := n) B) :
    termMeasure (n := n) B' k = termMeasure (n := n) B k := by
  simp [termMeasure, h]

/-!
### Fuel bound: `lllRunExactGo` reaches `.finished`

We prove a concrete bound: if `fuel ≥ termMeasure(B,k)+1`, then the runner reaches `.finished`.

This yields an explicit witness limit for `lllRunExact` (start state `k=1, steps=0`).
-/

theorem lllRunExactGo_finished_of_fuel_ge_termMeasure
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (k steps fuel : Nat)
    (hli : RowLIQ (n := n) B) (hδlt : δ < 1)
    (hfuel : termMeasure (n := n) B k + 1 ≤ fuel) :
    (lllRunExactGo (n := n) B δ k steps fuel).reason = .finished := by
  classical
  induction fuel generalizing B k steps with
  | zero =>
      -- impossible: `termMeasure + 1 ≤ 0`
      exact False.elim (Nat.not_succ_le_zero _ hfuel)
  | succ fuel ih =>
      -- unfold one runner step
      by_cases hk : k < n
      · by_cases h0 : k = 0
        · subst h0
          -- `k=0` branch: move to `k=1` without changing `B`
          have hn : 0 < n := hk
          have hdec : termMeasure (n := n) B 1 < termMeasure (n := n) B 0 :=
            termMeasure_k0_lt (n := n) B hn
          have hfuel0 : termMeasure (n := n) B 0 ≤ fuel := by
            -- from `termMeasure 0 + 1 ≤ fuel+1`
            have := hfuel
            simpa [Nat.succ_eq_add_one] using (Nat.succ_le_succ_iff.mp this)
          have hfuel1 : termMeasure (n := n) B 1 + 1 ≤ fuel := by
            have : termMeasure (n := n) B 1 + 1 ≤ termMeasure (n := n) B 0 := Nat.succ_le_of_lt hdec
            exact this.trans hfuel0
          -- apply IH to the recursive call with smaller fuel
          simpa [lllRunExactGo, hk] using
            ih (B := B) (k := 1) (steps := steps + 1) hli hfuel1
        · -- `k>0` branch: size-reduce then (advance or swap)
          have hk0 : 0 < k := Nat.pos_of_ne_zero h0
          let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
          have hpot1 : potentialVN (n := n) B1 = potentialVN (n := n) B :=
            potentialVN_sizeReduceAllExactWithPrefix (n := n) (B := B) (k := k) hk
          have hli1 : RowLIQ (n := n) B1 :=
            RowLIQ_sizeReduceAllExactWithPrefix (n := n) (B := B) (k := k) (hk := hk) hli
          let km1 : Nat := k - 1
          have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
          let k' : Fin n := ⟨k, hk⟩
          let km1' : Fin n := ⟨km1, hkm1⟩
          by_cases hL : lovaszQ (n := n) B1 k' km1' δ
          · -- Lovász holds: advance to `k+1`, potential unchanged
            have hdec' : termMeasure (n := n) B1 (k + 1) < termMeasure (n := n) B1 k :=
              termMeasure_lovasz_success_lt (n := n) (B := B1) (k := k) hk
            have hEqk : termMeasure (n := n) B1 k = termMeasure (n := n) B k :=
              termMeasure_congr_potentialVN (n := n) (k := k) (B := B) (B' := B1) hpot1
            have hdec : termMeasure (n := n) B1 (k + 1) < termMeasure (n := n) B k := by
              simpa [hEqk] using hdec'
            have hfuel0 : termMeasure (n := n) B k ≤ fuel := by
              have := hfuel
              simpa [Nat.succ_eq_add_one] using (Nat.succ_le_succ_iff.mp this)
            have hfuel' : termMeasure (n := n) B1 (k + 1) + 1 ≤ fuel := by
              exact (Nat.succ_le_of_lt hdec).trans hfuel0
            simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL] using
              ih (B := B1) (k := k + 1) (steps := steps + 1) hli1 hfuel'
          · -- Lovász fails: swap to `km1`, potential strictly decreases
            let B2 := swap_vectors (n := n) B1 k' km1'
            have hpot2 : potentialVN (n := n) B2 < potentialVN (n := n) B1 := by
              -- use the swap-decrease lemma on `B1`
              have : lovaszQ (n := n) B1 k' km1' δ = false := by
                simpa using (Bool.eq_false_of_not_eq_true (by intro h; exact hL (by simpa using h)))
              simpa [B2] using
                (potentialVN_swap_adj_lt_of_lovasz_fail (n := n) (B := B1) (δ := δ)
                  (k := k) (hk := hk) (hk0 := hk0) (hli := hli1) hδlt this)
            have hdec' : termMeasure (n := n) B2 km1 < termMeasure (n := n) B1 k :=
              termMeasure_swap_lt (n := n) (B1 := B1) (B2 := B2) (k := k) hk0 hk hpot2
            have hEqk : termMeasure (n := n) B1 k = termMeasure (n := n) B k :=
              termMeasure_congr_potentialVN (n := n) (k := k) (B := B) (B' := B1) hpot1
            have hdec : termMeasure (n := n) B2 km1 < termMeasure (n := n) B k := by
              simpa [hEqk] using hdec'
            have hfuel0 : termMeasure (n := n) B k ≤ fuel := by
              have := hfuel
              simpa [Nat.succ_eq_add_one] using (Nat.succ_le_succ_iff.mp this)
            have hfuel' : termMeasure (n := n) B2 km1 + 1 ≤ fuel := by
              exact (Nat.succ_le_of_lt hdec).trans hfuel0
            have hli2 : RowLIQ (n := n) B2 := RowLIQ_swap_vectors (n := n) (B := B1) (k := k') (j := km1') hli1
            simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL, B2] using
              ih (B := B2) (k := km1) (steps := steps + 1) hli2 hfuel'
      · -- already finished (`k ≥ n`)
        simp [lllRunExactGo, hk]

theorem lllRunExact_finished_of_RowLIQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (hli : RowLIQ (n := n) B) (hδlt : δ < 1) :
    ∃ limit : Nat, (lllRunExact (n := n) B δ limit).reason = .finished := by
  refine ⟨termMeasure (n := n) B 1 + 1, ?_⟩
  -- apply the general fuel bound at the start state
  have hfuel : termMeasure (n := n) B 1 + 1 ≤ termMeasure (n := n) B 1 + 1 := le_rfl
  simpa [lllRunExact] using
    (lllRunExactGo_finished_of_fuel_ge_termMeasure (n := n) (B := B) (δ := δ)
      (k := 1) (steps := 0) (fuel := termMeasure (n := n) B 1 + 1) hli hδlt hfuel)

theorem lllRunExact_finished_of_limit_ge_termMeasure
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (limit : Nat)
    (hli : RowLIQ (n := n) B) (hδlt : δ < 1)
    (hlimit : termMeasure (n := n) B 1 + 1 ≤ limit) :
    (lllRunExact (n := n) B δ limit).reason = .finished := by
  -- same proof as the witness lemma, but for any larger fuel/limit
  simpa [lllRunExact] using
    (lllRunExactGo_finished_of_fuel_ge_termMeasure (n := n) (B := B) (δ := δ)
      (k := 1) (steps := 0) (fuel := limit) hli hδlt hlimit)

theorem lllRunExact_exists_limit_LLLReducedQ_of_RowLIQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (hli : RowLIQ (n := n) B) (hδlt : δ < 1) :
    ∃ limit : Nat, LLLReducedQ (n := n) (lllRunExact (n := n) B δ limit).basis δ := by
  rcases lllRunExact_finished_of_RowLIQ (n := n) (B := B) (δ := δ) hli hδlt with ⟨limit, hfin⟩
  refine ⟨limit, ?_⟩
  -- reuse the established postcondition lemma from `LLLExactProofs`
  exact GeometryOfNumbers.Computable.lllRunExact_finished_LLLReducedQ_of_RowLIQ
    (n := n) (B := B) (δ := δ) (limit := limit) hli hfin

/-!
## A tiny “complexity counter”: how many swaps did we do?

To move toward recognizable complexity bounds, it helps to have a computable counter that mirrors
the runner and increments exactly on Lovász-failing branches (the swap steps).

This is not yet a *textbook* swap bound; it’s a thin hook we can use to state “swap count ≤ fuel”
and then later refine it using potential arguments.
-/

def swapCountGo {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k fuel : Nat) : Nat :=
  match fuel with
  | 0 => 0
  | fuel' + 1 =>
      if hk : k < n then
        if h0 : k = 0 then
          swapCountGo (n := n) B δ 1 fuel'
        else
          let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
          let km1 : Nat := k - 1
          have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
          let k' : Fin n := ⟨k, hk⟩
          let km1' : Fin n := ⟨km1, hkm1⟩
          if lovaszQ (n := n) B1 k' km1' δ then
            swapCountGo (n := n) B1 δ (k + 1) fuel'
          else
            let B2 := swap_vectors (n := n) B1 k' km1'
            1 + swapCountGo (n := n) B2 δ km1 fuel'
      else
        0

def swapCount {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (limit : Nat) : Nat :=
  swapCountGo (n := n) B δ 1 limit

theorem swapCountGo_le_fuel
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k fuel : Nat) :
    swapCountGo (n := n) B δ k fuel ≤ fuel := by
  induction fuel generalizing B k with
  | zero =>
      simp [swapCountGo]
  | succ fuel ih =>
      by_cases hk : k < n
      · by_cases h0 : k = 0
        · subst h0
          -- `swapCountGo ... 1 fuel ≤ fuel`, so also `≤ fuel+1`
          have h := ih (B := B) (k := 1)
          simpa [swapCountGo, hk] using (le_trans h (Nat.le_succ fuel))
        · -- `k>0`: size-reduce, then either advance or swap
          let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
          let km1 : Nat := k - 1
          have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
          let k' : Fin n := ⟨k, hk⟩
          let km1' : Fin n := ⟨km1, hkm1⟩
          by_cases hL : lovaszQ (n := n) B1 k' km1' δ
          · -- no swap: recurse without increment
            have h := ih (B := B1) (k := k + 1)
            simpa [swapCountGo, hk, h0, B1, km1, hkm1, k', km1', hL] using (le_trans h (Nat.le_succ fuel))
          · -- swap: `1 + rec ≤ fuel+1`
            let B2 := swap_vectors (n := n) B1 k' km1'
            have h := ih (B := B2) (k := km1)
            have h' : swapCountGo (n := n) B2 δ km1 fuel + 1 ≤ fuel + 1 :=
              Nat.add_le_add_right h 1
            -- rewrite `x + 1` as `1 + x`
            simpa [swapCountGo, hk, h0, B1, km1, hkm1, k', km1', hL, B2, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using h'
      · simp [swapCountGo, hk]

theorem swapCount_le_limit
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (limit : Nat) :
    swapCount (n := n) B δ limit ≤ limit := by
  simpa [swapCount] using swapCountGo_le_fuel (n := n) (B := B) (δ := δ) (k := 1) (fuel := limit)

theorem swapCount_at_termMeasure_le
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) :
    swapCount (n := n) B δ (termMeasure (n := n) B 1 + 1) ≤ termMeasure (n := n) B 1 + 1 := by
  simpa using swapCount_le_limit (n := n) (B := B) (δ := δ) (limit := termMeasure (n := n) B 1 + 1)



end GeometryOfNumbers.Computable

