import GeometryOfNumbers.Computable.LLLExact
import GeometryOfNumbers.Computable.LLLExactProofs
import Mathlib.LinearAlgebra.Matrix.Transvection

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
    simpa [hEq'] using (by simp : u_km1 ∈ us0 ++ [u_km1])

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

end GeometryOfNumbers.Computable

