import GeometryOfNumbers.Computable.LLLExact
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.List.ChainOfFn
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection

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

open Function Set Submodule

lemma rowQ_size_reduceZ_other {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j i : Fin n) (q : ℤ)
    (hki : i ≠ k) :
    rowQ (n := n) (size_reduceZ (n := n) B k j q) i = rowQ (n := n) B i := by
  ext t
  -- `updateRow` only changes row `k`
  simp [rowQ, size_reduceZ, Matrix.updateRow, hki]

theorem gsoPrefixListQ_size_reduceZ_of_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k j : Fin n) (q : ℤ) (m : Nat) (hm : m ≤ (k : Nat)) (hmn : m ≤ n) :
    gsoPrefixListQ (n := n) (size_reduceZ (n := n) B k j q) m hmn =
      gsoPrefixListQ (n := n) B m hmn := by
  -- size reduction changes only row `k`, so any prefix of length `m ≤ k` is unchanged.
  induction m with
  | zero =>
      simp [gsoPrefixListQ]
  | succ m ih =>
      have hmn' : m ≤ n := Nat.le_trans (Nat.le_succ m) hmn
      have hm' : m ≤ (k : Nat) := Nat.le_trans (Nat.le_succ m) hm
      -- unfold the prefix recursion at `m+1`
      have hm_lt_k : m < (k : Nat) := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm
      have hm_lt_n : m < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hmn
      let i' : Fin n := ⟨m, hm_lt_n⟩
      have hki' : i' ≠ k := by
        intro hEq
        have := congrArg Fin.val hEq
        exact (Nat.ne_of_lt hm_lt_k) this
      have hrow : rowQ (n := n) (size_reduceZ (n := n) B k j q) i' = rowQ (n := n) B i' :=
        rowQ_size_reduceZ_other (n := n) (B := B) (k := k) (j := j) (i := i') q hki'
      -- after rewriting the `i'` row, both sides are identical
      simp [gsoPrefixListQ, ih (hm := hm') (hmn := hmn'), i', hrow]

theorem gsoAtQ_size_reduceZ_of_lt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k j t : Fin n) (q : ℤ) (htk : (t : ℕ) < (k : ℕ)) :
    gsoAtQ (n := n) (size_reduceZ (n := n) B k j q) t = gsoAtQ (n := n) B t := by
  -- `gsoAtQ t` only depends on the prefix list of length `t+1`, which is unchanged when updating row `k` with `k>t`.
  have htp1_le_k : t.1 + 1 ≤ (k : Nat) := Nat.succ_le_of_lt htk
  have htp1_le_n : t.1 + 1 ≤ n := Nat.succ_le_of_lt t.2
  have htp1_le_n' : t.1 + 1 ≤ n := htp1_le_n
  simp [gsoAtQ]
  -- apply prefix-stability at `m = t+1`
  have :=
    gsoPrefixListQ_size_reduceZ_of_le (n := n) (B := B) (k := k) (j := j) (q := q)
      (m := t.1 + 1) (hm := htp1_le_k) (hmn := htp1_le_n')
  -- now use it to rewrite the list from which we take `getD`
  simpa using congrArg (fun us => us.getD t.1 (zeroVecQ (n := n))) this

lemma rowQ_size_reduceZ_self {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) (q : ℤ) :
    rowQ (n := n) (size_reduceZ (n := n) B k j q) k = rowQ (n := n) B k - (q : ℚ) • rowQ (n := n) B j := by
  ext t
  -- `updateRow` changes only row `k`.
  simp [rowQ, size_reduceZ, Matrix.updateRow_self, Pi.sub_apply, Pi.smul_apply, sub_eq_add_neg]

lemma dotQ_comm {n : ℕ} (v w : Fin n → ℚ) : dotQ (n := n) v w = dotQ (n := n) w v := by
  simp [dotQ, mul_comm]

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

/-!
### Rounding lemma (used by size reduction)

Our rounding is `roundQ x = ⌊x + 1/2⌋ : ℤ`. The standard bound is:
\(|x - roundQ(x)| \le 1/2\).
-/

theorem abs_sub_roundQ_le_half (x : ℚ) :
    |x - (roundQ x : ℚ)| ≤ (1 / 2 : ℚ) := by
  -- Let q = floor(x + 1/2). Then q ≤ x+1/2 < q+1.
  set q : ℤ := roundQ x
  have hq_le : (q : ℚ) ≤ x + (1 / 2 : ℚ) := by
    -- `Int.floor_le` / `Int.floor_le` via `q = ⌊x+1/2⌋`
    simpa [q, roundQ] using (Int.floor_le (x + (1 / 2 : ℚ)))
  have hlt : x + (1 / 2 : ℚ) < (q : ℚ) + 1 := by
    have hlt0 : x + (1 / 2 : ℚ) < ((roundQ x : ℤ) : ℚ) + 1 := by
      dsimp [roundQ]
      exact Int.lt_floor_add_one (x + (1 / 2 : ℚ))
    simpa [q] using hlt0
  have hge : (- (1 / 2 : ℚ)) ≤ x - (q : ℚ) := by
    -- from q ≤ x + 1/2
    linarith
  have hle : x - (q : ℚ) ≤ (1 / 2 : ℚ) := by
    -- from x + 1/2 < q + 1  ⇒  x - q < 1/2
    have : x - (q : ℚ) < (1 / 2 : ℚ) := by
      linarith
    exact le_of_lt this
  -- turn into abs bound
  simpa [abs_le] using And.intro hge hle

/-!
### Size reduction: how `μ` changes under `size_reduceZ`

This is the core algebraic fact behind size reduction correctness. It is intentionally stated with
one extra hypothesis:

`dotQ (rowQ B j) uj = dotQ uj uj`

which is the standard Gram–Schmidt identity for the `j`-th basis vector and its `j`-th GS vector.
Once we prove that GS identity for `gsoPrefixListQ`, we can instantiate this lemma directly in the
LLL loop.
-/

theorem muQPrefix_size_reduceZ_shift {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n)
    (uj : Fin n → ℚ) (hden : dotQ (n := n) uj uj ≠ 0) (hgs : dotQ (n := n) (rowQ (n := n) B j) uj = dotQ (n := n) uj uj) :
    let μ : ℚ := muQPrefix (n := n) (rowQ (n := n) B k) uj
    let q : ℤ := roundQ μ
    let B' : Matrix (Fin n) (Fin n) ℤ := size_reduceZ (n := n) B k j q
    muQPrefix (n := n) (rowQ (n := n) B' k) uj = μ - (q : ℚ) := by
  intro μ q B'
  have hrow : rowQ (n := n) B' k = rowQ (n := n) B k - (q : ℚ) • rowQ (n := n) B j := by
    simpa [B'] using rowQ_size_reduceZ_self (n := n) B k j q
  let denom : ℚ := dotQ (n := n) uj uj
  have hdot :
      dotQ (n := n) (rowQ (n := n) B' k) uj = dotQ (n := n) (rowQ (n := n) B k) uj - denom * (q : ℚ) := by
    -- compute dot after the row update and use the GS identity `dot(bj,uj)=dot(uj,uj)`
    calc
      dotQ (n := n) (rowQ (n := n) B' k) uj
          = dotQ (n := n) (rowQ (n := n) B k - (q : ℚ) • rowQ (n := n) B j) uj := by
              simp [hrow]
      _ = dotQ (n := n) (rowQ (n := n) B k) uj - (q : ℚ) * dotQ (n := n) (rowQ (n := n) B j) uj := by
              simp [dotQ_sub_left, dotQ_smul_left]
      _ = dotQ (n := n) (rowQ (n := n) B k) uj - (q : ℚ) * denom := by
              simp [denom, hgs]
      _ = dotQ (n := n) (rowQ (n := n) B k) uj - denom * (q : ℚ) := by
              ring_nf
  have hμ : μ = dotQ (n := n) (rowQ (n := n) B k) uj / denom := by
    simp [μ, muQPrefix, denom, hden]
  -- unfold `muQPrefix` (denom ≠ 0) and use the shift formula
  calc
    muQPrefix (n := n) (rowQ (n := n) B' k) uj
        = dotQ (n := n) (rowQ (n := n) B' k) uj / denom := by
            simp [muQPrefix, denom, hden]
    _ = (dotQ (n := n) (rowQ (n := n) B k) uj - denom * (q : ℚ)) / denom := by
            simp [hdot]
    _ = dotQ (n := n) (rowQ (n := n) B k) uj / denom - (q : ℚ) := by
            -- (a - denom*q)/denom = a/denom - q  (field calculation)
            set a : ℚ := dotQ (n := n) (rowQ (n := n) B k) uj
            -- unfold `/` and reduce to cancelling `denom⁻¹ * denom`
            simp [a, div_eq_mul_inv, sub_eq_add_neg, add_mul, mul_assoc]
            -- remaining goal is the cancellation `denom * (denom⁻¹ * q) = q`
            calc
              denom * ((q : ℚ) * denom⁻¹) = (q : ℚ) * (denom * denom⁻¹) := by
                simp [mul_assoc, mul_comm]
              _ = (q : ℚ) * (1 : ℚ) := by
                have : denom * denom⁻¹ = (1 : ℚ) := by
                  exact mul_inv_cancel₀ hden
                simp [this]
              _ = (q : ℚ) := by
                simp
    _ = μ - (q : ℚ) := by
            simp [hμ]

theorem abs_muQPrefix_after_size_reduceZ_le_half {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n)
    (uj : Fin n → ℚ) (hden : dotQ (n := n) uj uj ≠ 0)
    (hgs : dotQ (n := n) (rowQ (n := n) B j) uj = dotQ (n := n) uj uj) :
    let μ : ℚ := muQPrefix (n := n) (rowQ (n := n) B k) uj
    let q : ℤ := roundQ μ
    let B' : Matrix (Fin n) (Fin n) ℤ := size_reduceZ (n := n) B k j q
    |muQPrefix (n := n) (rowQ (n := n) B' k) uj| ≤ (1 / 2 : ℚ) := by
  intro μ q B'
  have hshift :
      muQPrefix (n := n) (rowQ (n := n) B' k) uj = μ - (q : ℚ) := by
    simpa [μ, q, B'] using muQPrefix_size_reduceZ_shift (n := n) B k j uj hden hgs
  -- Use the rounding bound: |μ - roundQ μ| ≤ 1/2.
  simpa [hshift, q, sub_eq_add_neg, add_comm] using (abs_sub_roundQ_le_half μ)

/-!
### Small, “postcondition-shaped” lemmas

We start with a fully concrete lemma for the first nontrivial case `n = 2` and `k = 1`:
`sizeReduceAllExactWithPrefix` performs exactly one size-reduction step, and we can prove the
standard \(|\mu_{1,0}| \le 1/2\) bound under a non-degeneracy hypothesis (`row 0` has nonzero norm).

This is a stepping stone toward a full postcondition theorem for the instrumented runner.
-/

lemma gsoAtQ_fin2_zero_eq_rowQ (B : Matrix (Fin 2) (Fin 2) ℤ) :
    gsoAtQ (n := 2) B (0 : Fin 2) = rowQ (n := 2) B (0 : Fin 2) := by
  -- `gsoListQ` starts with `bstar_0 = row_0` (empty prefix).
  simp [gsoAtQ, gsoPrefixListQ, rowQ, dotQ]

theorem sizeReduceAllExactWithPrefix_fin2_k1_mu_small
    (B : Matrix (Fin 2) (Fin 2) ℤ)
    (hden : dotQ (n := 2) (rowQ (n := 2) B (0 : Fin 2)) (rowQ (n := 2) B (0 : Fin 2)) ≠ 0) :
    let B1 := sizeReduceAllExactWithPrefix (n := 2) B 1 (by decide)
    |muQ (n := 2) B1 (1 : Fin 2) (0 : Fin 2)| ≤ (1 / 2 : ℚ) := by
  intro B1
  -- Expand `B1` to the single `size_reduceZ` step that happens when `k = 1`.
  have hk : (1 : Nat) < 2 := by decide
  have hB1 :
      B1 =
        size_reduceZ (n := 2) B (1 : Fin 2) (0 : Fin 2)
          (roundQ (muQPrefix (n := 2) (rowQ (n := 2) B (1 : Fin 2)) (rowQ (n := 2) B (0 : Fin 2)))) := by
    -- `gsoPrefixListQ B 1 = [row0]`, and the `Fin 1` foldr is a single step at `j=0`.
    simp [B1, sizeReduceAllExactWithPrefix, sizeReduceAllExactWithUs, gsoPrefixListQ]
  -- Apply the one-step size-reduction bound for `muQPrefix` against `uj = row0`.
  have hμprefix :
      |muQPrefix (n := 2) (rowQ (n := 2) B1 (1 : Fin 2)) (rowQ (n := 2) B (0 : Fin 2))| ≤ (1 / 2 : ℚ) := by
    rw [hB1]
    -- here `uj = row0`, so the GS identity is trivial
    have hgs :
        dotQ (n := 2) (rowQ (n := 2) B (0 : Fin 2)) (rowQ (n := 2) B (0 : Fin 2)) =
          dotQ (n := 2) (rowQ (n := 2) B (0 : Fin 2)) (rowQ (n := 2) B (0 : Fin 2)) := rfl
    simpa using
      abs_muQPrefix_after_size_reduceZ_le_half (n := 2) (B := B) (k := (1 : Fin 2)) (j := (0 : Fin 2))
        (uj := rowQ (n := 2) B (0 : Fin 2)) hden hgs
  -- Relate `muQ` at `(1,0)` to `muQPrefix` using `gsoAtQ 0 = row 0` and `denom ≠ 0`.
  have hrow0 : rowQ (n := 2) B1 (0 : Fin 2) = rowQ (n := 2) B (0 : Fin 2) := by
    rw [hB1]
    simpa using
      (rowQ_size_reduceZ_other (n := 2) (B := B) (k := (1 : Fin 2)) (j := (0 : Fin 2)) (i := (0 : Fin 2))
        (q := roundQ (muQPrefix (n := 2) (rowQ (n := 2) B (1 : Fin 2)) (rowQ (n := 2) B (0 : Fin 2))))
        (hki := by decide))
  have hgso0 : gsoAtQ (n := 2) B1 (0 : Fin 2) = rowQ (n := 2) B1 (0 : Fin 2) := by
    simpa using (gsoAtQ_fin2_zero_eq_rowQ (B := B1))
  have hmu :
      muQ (n := 2) B1 (1 : Fin 2) (0 : Fin 2) =
        muQPrefix (n := 2) (rowQ (n := 2) B1 (1 : Fin 2)) (rowQ (n := 2) B (0 : Fin 2)) := by
    -- unfold, then use `hgso0` and `hrow0` to rewrite the denominator to the nonzero `hden` case.
    simp [muQ, muQPrefix, hgso0, hrow0, hden]
  -- Finish.
  simpa [hmu] using hμprefix

theorem sizeReduceAllExactWithPrefix_fin2_k1_mu_small_any
    (B : Matrix (Fin 2) (Fin 2) ℤ) :
    let B1 := sizeReduceAllExactWithPrefix (n := 2) B 1 (by decide)
    |muQ (n := 2) B1 (1 : Fin 2) (0 : Fin 2)| ≤ (1 / 2 : ℚ) := by
  intro B1
  by_cases hden : dotQ (n := 2) (rowQ (n := 2) B (0 : Fin 2)) (rowQ (n := 2) B (0 : Fin 2)) = 0
  · -- degenerate: `muQ` uses `μ = 0`, so the bound is trivial
    have hk : (1 : Nat) < 2 := by decide
    have hB1 :
        B1 =
          size_reduceZ (n := 2) B (1 : Fin 2) (0 : Fin 2)
            (roundQ (muQPrefix (n := 2) (rowQ (n := 2) B (1 : Fin 2)) (rowQ (n := 2) B (0 : Fin 2)))) := by
      simp [B1, sizeReduceAllExactWithPrefix, sizeReduceAllExactWithUs, gsoPrefixListQ]
    -- row 0 is unchanged by size-reduction; so denom remains 0 and `muQ = 0`
    have hrow0 : rowQ (n := 2) B1 (0 : Fin 2) = rowQ (n := 2) B (0 : Fin 2) := by
      rw [hB1]
      simpa using
        (rowQ_size_reduceZ_other (n := 2) (B := B) (k := (1 : Fin 2)) (j := (0 : Fin 2)) (i := (0 : Fin 2))
          (q := roundQ (muQPrefix (n := 2) (rowQ (n := 2) B (1 : Fin 2)) (rowQ (n := 2) B (0 : Fin 2))))
          (hki := by decide))
    have hgso0 : gsoAtQ (n := 2) B1 (0 : Fin 2) = rowQ (n := 2) B1 (0 : Fin 2) := by
      simpa using (gsoAtQ_fin2_zero_eq_rowQ (B := B1))
    have hden1 : dotQ (n := 2) (gsoAtQ (n := 2) B1 (0 : Fin 2)) (gsoAtQ (n := 2) B1 (0 : Fin 2)) = 0 := by
      -- rewrite via `hgso0` and `hrow0`
      simpa [hgso0, hrow0] using hden
    have hdenRow0 : dotQ (n := 2) (rowQ (n := 2) B1 (0 : Fin 2)) (rowQ (n := 2) B1 (0 : Fin 2)) = 0 := by
      simpa [hgso0] using hden1
    -- now `muQ` is definitionally 0
    simp [muQ, hgso0, hdenRow0]
  · -- nondegenerate: use the stronger lemma
    have hden' :
        dotQ (n := 2) (rowQ (n := 2) B (0 : Fin 2)) (rowQ (n := 2) B (0 : Fin 2)) ≠ 0 := by
      exact hden
    simpa [B1] using sizeReduceAllExactWithPrefix_fin2_k1_mu_small (B := B) hden'

/-!
### Postcondition (first real one): `n = 2` (small but honest)

If the instrumented runner finishes (i.e. reaches `k ≥ n`), then for `n = 2` the returned basis
satisfies:

- the **size-reduction** boolean check at the only relevant pair `(1,0)`, and
- the **Lovász** boolean check at the only relevant adjacent pair `(1,0)`.

This is the smallest nontrivial instance: it exercises both the size-reduction lemma and the
“why we finished” logic for Lovász, without getting stuck expanding the full `isSizeReducedQ`
enumeration machinery.
-/

theorem lllRunExactGo_fin2_finished_postcond
    (B : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℚ) (k steps fuel : Nat)
    (hk_le : k ≤ 1) :
    (lllRunExactGo (n := 2) B δ k steps fuel).reason = .finished →
      (sizeReducedMuQ (n := 2) (lllRunExactGo (n := 2) B δ k steps fuel).basis (1 : Fin 2) (0 : Fin 2) = true ∧
       lovaszQ (n := 2) (lllRunExactGo (n := 2) B δ k steps fuel).basis (1 : Fin 2) (0 : Fin 2) δ = true) := by
  induction fuel generalizing B k steps with
  | zero =>
      intro h
      simp [lllRunExactGo] at h
  | succ fuel ih =>
      intro h
      -- Case split on `k < 2` (the loop condition for n=2).
      by_cases hk2 : k < 2
      · -- unfold one step of the runner
        simp [lllRunExactGo, hk2] at h ⊢
        by_cases hk0 : k = 0
        · subst hk0
          have hk1_le : (1 : Nat) ≤ 1 := by decide
          -- bounce to k=1 then apply IH
          simpa [lllRunExactGo] using ih (B := B) (k := 1) (steps := steps + 1) hk1_le (by simpa using h)
        · -- with `k < 2` and `k ≠ 0`, we must be at `k = 1`
          have hk1 : k = 1 := by omega
          subst hk1
          have hk' : (1 : Nat) < 2 := by decide
          set B1 : Matrix (Fin 2) (Fin 2) ℤ := sizeReduceAllExactWithPrefix (n := 2) B 1 hk'
          set k' : Fin 2 := (1 : Fin 2)
          set km1' : Fin 2 := (0 : Fin 2)
          by_cases hL : lovaszQ (n := 2) B1 k' km1' δ = true
          · -- finish immediately with basis=B1
            have hsize : |muQ (n := 2) B1 (1 : Fin 2) (0 : Fin 2)| ≤ (2⁻¹ : ℚ) := by
              -- `2⁻¹ = 1/2` in ℚ
              simpa [B1] using (sizeReduceAllExactWithPrefix_fin2_k1_mu_small_any (B := B))
            have hsizeBool : sizeReducedMuQ (n := 2) B1 (1 : Fin 2) (0 : Fin 2) = true := by
              simp [sizeReducedMuQ, hsize]
            -- In this branch, the next call is at `k=2`, which immediately returns with `basis = B1`.
            have hbasis : (lllRunExactGo (n := 2) B1 δ 2 (steps + 1) fuel).basis = B1 := by
              cases fuel <;> simp [lllRunExactGo]
            -- Reduce the postcondition goal to the basis `B1`.
            have : (sizeReducedMuQ (n := 2) (lllRunExactGo (n := 2) B δ 1 steps (fuel + 1)).basis (1 : Fin 2) (0 : Fin 2) = true ∧
                lovaszQ (n := 2) (lllRunExactGo (n := 2) B δ 1 steps (fuel + 1)).basis (1 : Fin 2) (0 : Fin 2) δ = true) := by
              -- unfold the step (k=1) and then rewrite the inner (k=2) basis to `B1`
              -- (avoid unfolding `lovaszQ` itself)
              simpa [lllRunExactGo, hk2, hk0, B1, k', km1', hL, hbasis] using And.intro hsizeBool hL
            exact this
          · -- swap and recurse with k=0
            have hk0_le : (0 : Nat) ≤ 1 := by decide
            -- apply IH to the recursive call
            have := ih (B := swap_vectors (n := 2) B1 k' km1') (k := 0) (steps := steps + 1) hk0_le
              (by simpa [lllRunExactGo, hk2, hk0, B1, k', km1', hL] using h)
            -- result basis is the recursive basis
            simpa [lllRunExactGo, hk2, hk0, B1, k', km1', hL] using this
      · -- if `k < 2` is false, we are already finished; but this case is impossible under `k ≤ 1`
        have : False := by
          have hk_lt2 : k < 2 := Nat.lt_of_le_of_lt hk_le (by decide)
          exact hk2 hk_lt2
        exact this.elim

theorem lllRunExact_fin2_finished_postcond
    (B : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℚ) (limit : Nat) :
    (lllRunExact (n := 2) B δ limit).reason = .finished →
      (sizeReducedMuQ (n := 2) (lllRunExact (n := 2) B δ limit).basis (1 : Fin 2) (0 : Fin 2) = true ∧
       lovaszQ (n := 2) (lllRunExact (n := 2) B δ limit).basis (1 : Fin 2) (0 : Fin 2) δ = true) := by
  intro h
  have hk_le : (1 : Nat) ≤ 1 := by decide
  simpa [lllRunExact] using
    (lllRunExactGo_fin2_finished_postcond (B := B) (δ := δ) (k := 1) (steps := 0) (fuel := limit) hk_le h)

/-!
### `n = 2` boolean bridges

The computable predicates `isSizeReducedQ` / `isLovaszReducedQ` are written generically via list
enumerations. For `n = 2` they simplify to exactly one nontrivial check (the pair `(1,0)`).
-/

lemma isSizeReducedQ_fin2_eq (B : Matrix (Fin 2) (Fin 2) ℤ) :
    isSizeReducedQ (n := 2) B = sizeReducedMuQ (n := 2) B (1 : Fin 2) (0 : Fin 2) := by
  -- compute the finite enumeration explicitly
  simp [isSizeReducedQ, List.foldl, List.map, List.all, sizeReducedMuQ]

lemma isLovaszReducedQ_fin2_eq (B : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℚ) :
    isLovaszReducedQ (n := 2) B δ = lovaszQ (n := 2) B (1 : Fin 2) (0 : Fin 2) δ := by
  -- only `k=1` contributes a constraint; `k=0` is vacuous
  simp [isLovaszReducedQ, lovaszQ]

theorem isLLLReducedQ_fin2_of_pair
    (B : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℚ)
    (hsize : sizeReducedMuQ (n := 2) B (1 : Fin 2) (0 : Fin 2) = true)
    (hL : lovaszQ (n := 2) B (1 : Fin 2) (0 : Fin 2) δ = true) :
    isLLLReducedQ (n := 2) B δ = true := by
  -- expand and reduce to the two primitive checks
  simp [isLLLReducedQ, isSizeReducedQ_fin2_eq, isLovaszReducedQ_fin2_eq, hsize, hL]

theorem lllRunExact_fin2_finished_isLLLReducedQ
    (B : Matrix (Fin 2) (Fin 2) ℤ) (δ : ℚ) (limit : Nat) :
    (lllRunExact (n := 2) B δ limit).reason = .finished →
      isLLLReducedQ (n := 2) (lllRunExact (n := 2) B δ limit).basis δ = true := by
  intro h
  have hpost := lllRunExact_fin2_finished_postcond (B := B) (δ := δ) (limit := limit) h
  rcases hpost with ⟨hsize, hL⟩
  exact isLLLReducedQ_fin2_of_pair (B := (lllRunExact (n := 2) B δ limit).basis) (δ := δ) hsize hL

/-!
### Semantic lemmas for boolean checkers (all `n`)

The executable predicates in `LLLExact` are written using list enumerations so they can run in
`lean_exe`. For proofs, we want “semantic” lemmas that let us *avoid* expanding those lists.

These are intentionally one-way (“if the semantic property holds, then the boolean checker returns
`true`”). That’s enough to prove postconditions.
-/

theorem isSizeReducedQ_of_forall {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (h : ∀ i j : Fin n, (j : ℕ) < (i : ℕ) → sizeReducedMuQ (n := n) B i j = true) :
    isSizeReducedQ (n := n) B = true := by
  classical
  unfold isSizeReducedQ
  -- After unfolding, the goal is a `List.all` over some list of pairs.
  -- Use `List.all_eq_true` without needing to analyze membership in that list: `h` is universal.
  refine (List.all_eq_true).2 ?_
  intro ij _hmem
  rcases ij with ⟨i, j⟩
  by_cases hij : (j : ℕ) < (i : ℕ)
  · simpa [hij] using h i j hij
  · simp [hij]

theorem isLovaszReducedQ_of_forall {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (h :
      ∀ k : Fin n,
        (hk0 : (0 : ℕ) < (k : ℕ)) →
          let km1Nat : ℕ := (k : ℕ) - 1
          have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) k.2
          let km1 : Fin n := ⟨km1Nat, hkm1⟩
          lovaszQ (n := n) B k km1 δ = true) :
    isLovaszReducedQ (n := n) B δ = true := by
  classical
  unfold isLovaszReducedQ
  refine (List.all_eq_true).2 ?_
  intro k _hk_mem
  by_cases hk0 : (0 : ℕ) < (k : ℕ)
  · -- nontrivial adjacent check
    have := h k hk0
    -- unfold the local `km1` construction and use the hypothesis
    simpa [hk0] using this
  · -- k = 0 case is vacuous
    simp [hk0]

theorem isLLLReducedQ_of_forall {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ)
    (hsize : ∀ i j : Fin n, (j : ℕ) < (i : ℕ) → sizeReducedMuQ (n := n) B i j = true)
    (hlov :
      ∀ k : Fin n,
        (hk0 : (0 : ℕ) < (k : ℕ)) →
          let km1Nat : ℕ := (k : ℕ) - 1
          have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) k.2
          let km1 : Fin n := ⟨km1Nat, hkm1⟩
          lovaszQ (n := n) B k km1 δ = true) :
    isLLLReducedQ (n := n) B δ = true := by
  have hs : isSizeReducedQ (n := n) B = true := isSizeReducedQ_of_forall (n := n) (B := B) hsize
  have hl : isLovaszReducedQ (n := n) B δ = true := isLovaszReducedQ_of_forall (n := n) (B := B) (δ := δ) hlov
  -- `isLLLReducedQ` is a boolean `&&` of the two checks.
  simp [isLLLReducedQ, hs, hl]

/-!
### Prop-level specs (thin wrappers over the executable checkers)

These specs are intentionally “thin”: they state that the corresponding **computable** checker returns `true`.
They are stable and easy to use as postconditions, and they compose cleanly.
-/

def SizeReducedSpecQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  isSizeReducedQ (n := n) B = true

def LovaszReducedSpecQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) : Prop :=
  isLovaszReducedQ (n := n) B δ = true

def LLLReducedSpecQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) : Prop :=
  isLLLReducedQ (n := n) B δ = true

theorem LLLReducedSpecQ_iff {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) :
    LLLReducedSpecQ (n := n) B δ ↔ SizeReducedSpecQ (n := n) B ∧ LovaszReducedSpecQ (n := n) B δ := by
  simp [LLLReducedSpecQ, SizeReducedSpecQ, LovaszReducedSpecQ, isLLLReducedQ, Bool.and_eq_true]

/-!
### Size reduction: invariance for “unrelated” GS vectors

If we update row `k` by subtracting an integer multiple of row `j`, then the coefficient
`muQPrefix(b_k, u)` is unchanged for any `u` orthogonal to row `j`.

This is the core reason descending order matters: later reductions using `j' < j` do not re-break
the already-reduced coefficient at `j` because `row_{j'}` lies in the span of earlier GS vectors,
which are orthogonal to `u_j`.
-/

theorem muQPrefix_size_reduceZ_invariant_of_dot_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k j : Fin n) (q : ℤ) (u : Fin n → ℚ) (hden : dotQ (n := n) u u ≠ 0)
    (hz : dotQ (n := n) (rowQ (n := n) B j) u = 0) :
    muQPrefix (n := n) (rowQ (n := n) (size_reduceZ (n := n) B k j q) k) u =
      muQPrefix (n := n) (rowQ (n := n) B k) u := by
  have hrow : rowQ (n := n) (size_reduceZ (n := n) B k j q) k =
      rowQ (n := n) B k - (q : ℚ) • rowQ (n := n) B j := by
    simpa using rowQ_size_reduceZ_self (n := n) B k j q
  -- unfold muQPrefix (denom ≠ 0) and simplify the dot-product
  simp [muQPrefix, hden, hrow]
  -- reduce numerator using hz
  calc
    dotQ (n := n) (rowQ (n := n) B k - (q : ℚ) • rowQ (n := n) B j) u
        = dotQ (n := n) (rowQ (n := n) B k) u - (q : ℚ) * dotQ (n := n) (rowQ (n := n) B j) u := by
            simp [dotQ_sub_left, dotQ_smul_left]
    _ = dotQ (n := n) (rowQ (n := n) B k) u := by
            simp [hz]

/-!
### Gram–Schmidt fold lemma (meaty invariant)

`gsoVectorForKPrefix` uses a fold that subtracts projections onto a list of already-orthogonal
vectors `us`, with coefficients computed from the *original* vector `bk`.

The key invariant is:
if `us` is pairwise orthogonal and each `u ∈ us` has `dotQ u u ≠ 0`, then after folding, the
result is orthogonal to every `u ∈ us`.
-/

def gsUpdate {n : ℕ} (bk : Fin n → ℚ) (v uj : Fin n → ℚ) : Fin n → ℚ :=
  let μ := muQPrefix (n := n) bk uj
  v - μ • uj

def gsoVectorForKPrefixFrom {n : ℕ} (bk : Fin n → ℚ) (v0 : Fin n → ℚ) (us : List (Fin n → ℚ)) :
    Fin n → ℚ :=
  us.foldl (gsUpdate (n := n) bk) v0

lemma gsoVectorForKPrefixFrom_nil {n : ℕ} (bk v0 : Fin n → ℚ) :
    gsoVectorForKPrefixFrom (n := n) bk v0 [] = v0 := by
  rfl

lemma gsoVectorForKPrefixFrom_cons {n : ℕ} (bk v0 u : Fin n → ℚ) (us : List (Fin n → ℚ)) :
    gsoVectorForKPrefixFrom (n := n) bk v0 (u :: us) =
      gsoVectorForKPrefixFrom (n := n) bk (gsUpdate (n := n) bk v0 u) us := by
  rfl

lemma dotQ_gsUpdate_right {n : ℕ} (bk v u w : Fin n → ℚ) :
    dotQ (n := n) (gsUpdate (n := n) bk v u) w =
      dotQ (n := n) v w - (muQPrefix (n := n) bk u) * dotQ (n := n) u w := by
  simp [gsUpdate, dotQ_sub_left, dotQ_smul_left]

lemma dotQ_gsUpdate_left {n : ℕ} (bk v u w : Fin n → ℚ) :
    dotQ (n := n) w (gsUpdate (n := n) bk v u) =
      dotQ (n := n) w v - (muQPrefix (n := n) bk u) * dotQ (n := n) w u := by
  -- use symmetry + previous lemma
  simpa [dotQ_comm, mul_comm] using (dotQ_gsUpdate_right (n := n) bk v u w)

lemma dotQ_gsoVectorForKPrefixFrom_preserve_dot {n : ℕ} (bk v0 u0 : Fin n → ℚ) (us : List (Fin n → ℚ))
    (h0 : ∀ a ∈ us, dotQ (n := n) a u0 = 0) :
    dotQ (n := n) (gsoVectorForKPrefixFrom (n := n) bk v0 us) u0 = dotQ (n := n) v0 u0 := by
  induction us generalizing v0 with
  | nil =>
      simp [gsoVectorForKPrefixFrom]
  | cons a us ih =>
      have ha0 : dotQ (n := n) a u0 = 0 := by
        exact h0 a (by simp)
      -- one update doesn't change dot with u0 when a ⟂ u0
      have : dotQ (n := n) (gsUpdate (n := n) bk v0 a) u0 = dotQ (n := n) v0 u0 := by
        simp [dotQ_gsUpdate_right, ha0]
      -- then apply IH to the tail
      simpa [gsoVectorForKPrefixFrom, this] using
        (ih (v0 := gsUpdate (n := n) bk v0 a) (fun b hb => h0 b (by simp [hb])))

theorem dotQ_gsoVectorForKPrefixFrom_mem_eq_zero {n : ℕ} (bk v0 : Fin n → ℚ) (us : List (Fin n → ℚ))
    (horth : us.Pairwise (fun u w => dotQ (n := n) u w = 0))
    (hnz : ∀ u ∈ us, dotQ (n := n) u u ≠ 0)
    (hdot : ∀ u ∈ us, dotQ (n := n) v0 u = dotQ (n := n) bk u) :
    ∀ u ∈ us, dotQ (n := n) (gsoVectorForKPrefixFrom (n := n) bk v0 us) u = 0 := by
  induction us generalizing v0 with
  | nil =>
      intro u hu
      cases hu
  | cons u us ih =>
      intro w hw
      cases horth with
      | cons hrel horth_tail =>
          have hdot_u : dotQ (n := n) v0 u = dotQ (n := n) bk u := by
            exact hdot u (by simp)
          have hnz_u : dotQ (n := n) u u ≠ 0 := by
            exact hnz u (by simp)
          have hnz_tail : ∀ a ∈ us, dotQ (n := n) a a ≠ 0 := by
            intro a ha
            exact hnz a (by simp [ha])
          have hdot_tail : ∀ a ∈ us, dotQ (n := n) (gsUpdate (n := n) bk v0 u) a = dotQ (n := n) bk a := by
            intro a ha
            have hua : dotQ (n := n) u a = 0 := hrel a ha
            calc
              dotQ (n := n) (gsUpdate (n := n) bk v0 u) a
                  = dotQ (n := n) v0 a - (muQPrefix (n := n) bk u) * dotQ (n := n) u a := by
                      simpa using dotQ_gsUpdate_right (n := n) bk v0 u a
              _ = dotQ (n := n) v0 a := by
                      simp [hua]
              _ = dotQ (n := n) bk a := by
                      exact (hdot a (by simp [ha]))
          have htail_au : ∀ a ∈ us, dotQ (n := n) a u = 0 := by
            intro a ha
            simpa [dotQ_comm] using (hrel a ha)
          have hwOr : w = u ∨ w ∈ us := by
            simpa using (List.mem_cons.1 hw)
          cases hwOr with
          | inl hwu =>
              -- first update makes v0 orthogonal to u
              have hμ : muQPrefix (n := n) bk u = dotQ (n := n) v0 u / dotQ (n := n) u u := by
                simp [muQPrefix, hnz_u, hdot_u.symm]
              have hu0 : dotQ (n := n) (gsUpdate (n := n) bk v0 u) u = 0 := by
                have : dotQ (n := n) (gsUpdate (n := n) bk v0 u) u =
                    dotQ (n := n) (v0 - (dotQ (n := n) v0 u / dotQ (n := n) u u) • u) u := by
                  simp [gsUpdate, hμ]
                have hz :
                    dotQ (n := n) (v0 - (dotQ (n := n) v0 u / dotQ (n := n) u u) • u) u = 0 := by
                  simpa using (dotQ_proj_update_zero (n := n) u v0 hnz_u)
                simpa [this] using hz
              -- folding over the tail preserves dot with u
              have hpres :
                  dotQ (n := n) (gsoVectorForKPrefixFrom (n := n) bk (gsUpdate (n := n) bk v0 u) us) u =
                    dotQ (n := n) (gsUpdate (n := n) bk v0 u) u := by
                simpa using
                  (dotQ_gsoVectorForKPrefixFrom_preserve_dot (n := n) bk (gsUpdate (n := n) bk v0 u) u us htail_au)
              -- now finish: rewrite goal to the tail-fold form, then transport via hpres
              have hfold0 :
                  dotQ (n := n) (gsoVectorForKPrefixFrom (n := n) bk (gsUpdate (n := n) bk v0 u) us) u = 0 := by
                simpa [hpres] using hu0
              have hfinal_u : dotQ (n := n) (gsoVectorForKPrefixFrom (n := n) bk v0 (u :: us)) u = 0 := by
                simpa [gsoVectorForKPrefixFrom] using hfold0
              simpa [hwu] using hfinal_u
          | inr hwtail =>
              -- apply IH to tail, with updated v0
              have : dotQ (n := n)
                    (gsoVectorForKPrefixFrom (n := n) bk (gsUpdate (n := n) bk v0 u) us) w = 0 := by
                exact ih (v0 := gsUpdate (n := n) bk v0 u) horth_tail hnz_tail hdot_tail w hwtail
              simpa [gsoVectorForKPrefixFrom] using this

theorem dotQ_gsoVectorForKPrefix_mem_eq_zero {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ))
    (horth : us.Pairwise (fun u w => dotQ (n := n) u w = 0))
    (hnz : ∀ u ∈ us, dotQ (n := n) u u ≠ 0) :
    ∀ u ∈ us, dotQ (n := n) (gsoVectorForKPrefix (n := n) bk us) u = 0 := by
  -- unfold as the special case `v0=bk`
  have hdot : ∀ u ∈ us, dotQ (n := n) bk u = dotQ (n := n) bk u := by
    intro u hu; rfl
  simpa [gsoVectorForKPrefix, gsoVectorForKPrefixFrom] using
    (dotQ_gsoVectorForKPrefixFrom_mem_eq_zero (n := n) bk bk us horth hnz hdot)

/-!
### Gram–Schmidt identity: `dot(b, u) = dot(u, u)`

If `u` is the Gram–Schmidt vector obtained by subtracting projections of `bk` onto an already
orthogonal list `us`, then:

- `bk = u + (sum of projection components in span(us))`, and
- `u ⟂ span(us)`,

so `dot(bk, u) = dot(u, u)`.
-/

def projSumForKPrefix {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ)) : Fin n → ℚ :=
  us.foldl (fun s u => s + (muQPrefix (n := n) bk u) • u) (0 : Fin n → ℚ)

lemma dotQ_foldl_add_proj_preserve {n : ℕ} (bk uj : Fin n → ℚ) (us : List (Fin n → ℚ)) (s0 : Fin n → ℚ)
    (h0 : ∀ u ∈ us, dotQ (n := n) u uj = 0) :
    dotQ (n := n) (us.foldl (fun s u => s + (muQPrefix (n := n) bk u) • u) s0) uj = dotQ (n := n) s0 uj := by
  induction us generalizing s0 with
  | nil =>
      simp
  | cons u us ih =>
      have hu0 : dotQ (n := n) u uj = 0 := h0 u (by simp)
      have h0' : ∀ a ∈ us, dotQ (n := n) a uj = 0 := by
        intro a ha
        exact h0 a (by simp [ha])
      -- one step: dot(s0 + μu, uj) = dot(s0,uj) + μ dot(u,uj) = dot(s0,uj)
      simpa [List.foldl, dotQ_add_left, dotQ_smul_left, hu0] using (ih (s0 := s0 + (muQPrefix (n := n) bk u) • u) h0')

theorem dotQ_projSumForKPrefix_right_eq_zero {n : ℕ} (bk uj : Fin n → ℚ) (us : List (Fin n → ℚ))
    (h0 : ∀ u ∈ us, dotQ (n := n) u uj = 0) :
    dotQ (n := n) (projSumForKPrefix (n := n) bk us) uj = 0 := by
  -- reduce to the general fold lemma with `s0=0`
  simpa [projSumForKPrefix, dotQ] using (dotQ_foldl_add_proj_preserve (n := n) bk uj us (0 : Fin n → ℚ) h0)

def gsFoldPairFrom {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ)) (p0 : (Fin n → ℚ) × (Fin n → ℚ)) :
    (Fin n → ℚ) × (Fin n → ℚ) :=
  us.foldl
    (fun p u =>
      let μ := muQPrefix (n := n) bk u
      (p.1 - μ • u, p.2 + μ • u))
    p0

def projSumForKPrefixFrom {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ)) (s0 : Fin n → ℚ) : Fin n → ℚ :=
  us.foldl (fun s u => s + (muQPrefix (n := n) bk u) • u) s0

lemma gsFoldPairFrom_invariant {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ)) (p0 : (Fin n → ℚ) × (Fin n → ℚ)) :
    (gsFoldPairFrom (n := n) bk us p0).1 + (gsFoldPairFrom (n := n) bk us p0).2 = p0.1 + p0.2 := by
  induction us generalizing p0 with
  | nil =>
      simp [gsFoldPairFrom]
  | cons u us ih =>
      -- unfold one `foldl` step
      have := ih ((p0.1 - (muQPrefix (n := n) bk u) • u, p0.2 + (muQPrefix (n := n) bk u) • u))
      -- rewrite `foldl` on cons
      simpa [gsFoldPairFrom, List.foldl, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this

lemma gsFoldPairFrom_fst_eq_gsoVectorForKPrefixFrom {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ))
    (p0 : (Fin n → ℚ) × (Fin n → ℚ)) :
    (gsFoldPairFrom (n := n) bk us p0).1 = gsoVectorForKPrefixFrom (n := n) bk p0.1 us := by
  induction us generalizing p0 with
  | nil =>
      simp [gsFoldPairFrom, gsoVectorForKPrefixFrom]
  | cons u us ih =>
      -- unfold one `foldl` step and apply IH
      have := ih ((p0.1 - (muQPrefix (n := n) bk u) • u, p0.2 + (muQPrefix (n := n) bk u) • u))
      -- `gsoVectorForKPrefixFrom` on cons performs the same update to the first component
      simpa [gsFoldPairFrom, gsoVectorForKPrefixFrom, gsUpdate, List.foldl] using this

lemma gsFoldPairFrom_snd_eq_projSumForKPrefixFrom {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ))
    (p0 : (Fin n → ℚ) × (Fin n → ℚ)) :
    (gsFoldPairFrom (n := n) bk us p0).2 = projSumForKPrefixFrom (n := n) bk us p0.2 := by
  induction us generalizing p0 with
  | nil =>
      simp [gsFoldPairFrom, projSumForKPrefixFrom]
  | cons u us ih =>
      have := ih ((p0.1 - (muQPrefix (n := n) bk u) • u, p0.2 + (muQPrefix (n := n) bk u) • u))
      simpa [gsFoldPairFrom, projSumForKPrefixFrom, List.foldl] using this

theorem gsoVectorForKPrefix_add_projSum_eq_bk {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ)) :
    gsoVectorForKPrefix (n := n) bk us + projSumForKPrefix (n := n) bk us = bk := by
  -- evaluate the pair fold invariant at `(bk,0)` and rewrite the components
  have hinv :
      (gsFoldPairFrom (n := n) bk us (bk, 0)).1 + (gsFoldPairFrom (n := n) bk us (bk, 0)).2 = bk := by
    simpa using (gsFoldPairFrom_invariant (n := n) bk us (bk, (0 : Fin n → ℚ)))
  have hfst : (gsFoldPairFrom (n := n) bk us (bk, 0)).1 = gsoVectorForKPrefix (n := n) bk us := by
    -- `gsoVectorForKPrefix` is the `v0=bk` special case
    simpa [gsoVectorForKPrefix] using (gsFoldPairFrom_fst_eq_gsoVectorForKPrefixFrom (n := n) bk us (bk, (0 : Fin n → ℚ)))
  have hsnd : (gsFoldPairFrom (n := n) bk us (bk, 0)).2 = projSumForKPrefix (n := n) bk us := by
    -- unfold projSumForKPrefix as the `s0=0` special case
    simpa [projSumForKPrefix, projSumForKPrefixFrom] using
      (gsFoldPairFrom_snd_eq_projSumForKPrefixFrom (n := n) bk us (bk, (0 : Fin n → ℚ)))
  simpa [hfst, hsnd] using hinv

theorem dotQ_bk_eq_dotQ_gsoVector_normSq {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ))
    (horth : us.Pairwise (fun u w => dotQ (n := n) u w = 0))
    (hnz : ∀ u ∈ us, dotQ (n := n) u u ≠ 0) :
    let uj := gsoVectorForKPrefix (n := n) bk us
    dotQ (n := n) bk uj = dotQ (n := n) uj uj := by
  intro uj
  have hsum : bk = uj + projSumForKPrefix (n := n) bk us := by
    -- rearrange the decomposition lemma
    simpa [uj, add_comm, add_left_comm, add_assoc] using
      (gsoVectorForKPrefix_add_projSum_eq_bk (n := n) bk us).symm
  have h0 : ∀ u ∈ us, dotQ (n := n) u uj = 0 := by
    intro u hu
    have : dotQ (n := n) uj u = 0 := dotQ_gsoVectorForKPrefix_mem_eq_zero (n := n) bk us horth hnz u hu
    simpa [dotQ_comm] using this
  have hproj0 : dotQ (n := n) (projSumForKPrefix (n := n) bk us) uj = 0 :=
    dotQ_projSumForKPrefix_right_eq_zero (n := n) bk uj us h0
  -- now expand dot(bk,uj)
  calc
    dotQ (n := n) bk uj
        = dotQ (n := n) (uj + projSumForKPrefix (n := n) bk us) uj := by
            exact congrArg (fun x => dotQ (n := n) x uj) hsum
    _ = dotQ (n := n) uj uj + dotQ (n := n) (projSumForKPrefix (n := n) bk us) uj := by
            simp [dotQ_add_left]
    _ = dotQ (n := n) uj uj := by
            simp [hproj0]

/-!
### Connecting `gsoPrefixListQ` to GS identities

To lift size-reduction correctness from a single update to the full `foldr` loop used by
`sizeReduceAllExactWithUs`, we need:

- the `j`-th prefix GS vector is **orthogonal** to all earlier GS vectors, and
- the GS identity `dot(row_j, u_j) = dot(u_j, u_j)` for that `u_j`.

These lemmas are proved under a simple nondegeneracy hypothesis saying all prefix GS norms are
nonzero (the intended “basis is independent” regime).
-/

lemma gsoPrefixListQ_length {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    (gsoPrefixListQ (n := n) B k hk).length = k := by
  induction k with
  | zero =>
      simp [gsoPrefixListQ]
  | succ k ih =>
      simp [gsoPrefixListQ, ih]

lemma gsoPrefixListQ_succ_eq_append {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k + 1 ≤ n) :
    ∃ us bstar,
      gsoPrefixListQ (n := n) B (k + 1) hk = us ++ [bstar] ∧
      us = gsoPrefixListQ (n := n) B k (Nat.le_trans (Nat.le_succ k) hk) ∧
      bstar = gsoVectorForKPrefix (n := n) (rowQ (n := n) B ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩) us := by
  -- just unfold the definition at `k+1`
  let us : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B k (Nat.le_trans (Nat.le_succ k) hk)
  let bstar : Fin n → ℚ :=
    gsoVectorForKPrefix (n := n) (rowQ (n := n) B ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩) us
  refine ⟨us, bstar, ?_, rfl, rfl⟩
  -- unfold `gsoPrefixListQ` at `k+1` and identify its `bstar` with our definition
  simp [gsoPrefixListQ, us, bstar, gsoVectorForKPrefix, muQPrefix]

theorem gsoPrefixListQ_pairwise_orth {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n)
    (hnz : ∀ u ∈ gsoPrefixListQ (n := n) B k hk, dotQ (n := n) u u ≠ 0) :
    (gsoPrefixListQ (n := n) B k hk).Pairwise (fun u w => dotQ (n := n) u w = 0) := by
  induction k with
  | zero =>
      simp [gsoPrefixListQ]
  | succ k ih =>
      -- unfold once
      rcases gsoPrefixListQ_succ_eq_append (n := n) B k hk with ⟨us, bstar, hEq, hUs, hB⟩
      -- rewrite goal into the append form
      rw [hEq]
      have hk0 : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hnz_us : ∀ u ∈ us, dotQ (n := n) u u ≠ 0 := by
        intro u hu
        have : u ∈ us ++ [bstar] := List.mem_append_left _ hu
        have : u ∈ gsoPrefixListQ (n := n) B (k + 1) hk := by simpa [hEq] using this
        exact hnz u this
      have hnz_prev : ∀ u ∈ gsoPrefixListQ (n := n) B k hk0, dotQ (n := n) u u ≠ 0 := by
        intro u hu
        have : u ∈ us := by simpa [hUs] using hu
        exact hnz_us u this
      have horth_us : us.Pairwise (fun u w => dotQ (n := n) u w = 0) := by
        -- IH gives Pairwise for the previous prefix list; rewrite via `hUs`
        have : (gsoPrefixListQ (n := n) B k hk0).Pairwise (fun u w => dotQ (n := n) u w = 0) :=
          ih (hk := hk0) (hnz := hnz_prev)
        simpa [hUs] using this
      -- show every `u ∈ us` satisfies `dot(u,bstar)=0`
      have hbstar0 : ∀ u ∈ us, dotQ (n := n) u bstar = 0 := by
        intro u hu
        -- use the general fold orthogonality lemma (and symmetry of dot)
        have h0 : dotQ (n := n) bstar u = 0 := by
          -- rewrite `bstar` using `hB`
          rw [hB]
          exact dotQ_gsoVectorForKPrefix_mem_eq_zero (n := n)
            (rowQ (n := n) B ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩)
            us horth_us hnz_us u hu
        simpa [dotQ_comm] using h0
      -- assemble `Pairwise` for `us ++ [bstar]`
      refine (List.pairwise_append.2 ?_)
      refine ⟨horth_us, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      have hb' : b = bstar := by simpa using hb
      subst hb'
      exact hbstar0 a ha

theorem dotQ_row_prefix_eq_normSq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (j : Nat) (hj : j < n)
    (hnz : ∀ u ∈ gsoPrefixListQ (n := n) B (j + 1) (Nat.succ_le_of_lt hj), dotQ (n := n) u u ≠ 0) :
    let us := gsoPrefixListQ (n := n) B j (Nat.le_of_lt hj)
    let uj := gsoVectorForKPrefix (n := n) (rowQ (n := n) B ⟨j, hj⟩) us
    dotQ (n := n) (rowQ (n := n) B ⟨j, hj⟩) uj = dotQ (n := n) uj uj := by
  intro us uj
  have hnz_us : ∀ u ∈ us, dotQ (n := n) u u ≠ 0 := by
    intro u hu
    exact hnz u (by
      -- `us` is a prefix of the (j+1)-prefix list
      simp [us, gsoPrefixListQ, hu])
  have horth_us :
      us.Pairwise (fun u w => dotQ (n := n) u w = 0) :=
    gsoPrefixListQ_pairwise_orth (n := n) B j (Nat.le_of_lt hj) hnz_us
  simpa [uj] using dotQ_bk_eq_dotQ_gsoVector_normSq (n := n) (rowQ (n := n) B ⟨j, hj⟩) us horth_us hnz_us

lemma gsoPrefixListQ_mem_of_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (m k : Nat) (hmk : m ≤ k) (hmn : m ≤ n) (hkn : k ≤ n) :
    ∀ u ∈ gsoPrefixListQ (n := n) B m hmn, u ∈ gsoPrefixListQ (n := n) B k hkn := by
  -- monotone-by-membership: prefix lists nest as `k` grows
  induction k generalizing m with
  | zero =>
      intro u hu
      have hm0 : m = 0 := Nat.eq_zero_of_le_zero (Nat.le_trans hmk (Nat.zero_le _))
      subst hm0
      simpa [gsoPrefixListQ] using hu
  | succ k ih =>
      intro u hu
      by_cases hm_eq : m = k + 1
      · subst hm_eq
        simpa using hu
      · have hmk' : m ≤ k := Nat.le_of_lt_succ <| Nat.lt_of_le_of_ne hmk hm_eq
        have hk' : k ≤ n := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hkn
        have hm_in : u ∈ gsoPrefixListQ (n := n) B k hk' := ih (m := m) hmk' hmn hk' u hu
        rcases gsoPrefixListQ_succ_eq_append (n := n) B k (by simpa using hkn) with ⟨us, bstar, hEq, hUs, _hB⟩
        have hEq' :
            gsoPrefixListQ (n := n) B (k + 1) (by simpa using hkn) = (gsoPrefixListQ (n := n) B k hk') ++ [bstar] := by
          -- only the `us = prefix k` identity matters here
          simpa [hUs] using hEq
        -- `prefix (k+1) = prefix k ++ [..]`, so lift membership through the append
        have : u ∈ (gsoPrefixListQ (n := n) B k hk') ++ [bstar] := List.mem_append_left [bstar] hm_in
        simpa [hEq'] using this

lemma gsoPrefixListQ_getD_eq_gsoAtQ_of_lt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k : Nat) (hk : k ≤ n) (j : Fin n) (hjk : (j : Nat) < k) :
    (gsoPrefixListQ (n := n) B k hk).getD j.1 (zeroVecQ (n := n)) = gsoAtQ (n := n) B j := by
  classical
  induction k with
  | zero =>
      cases Nat.not_lt_zero _ hjk
  | succ k ih =>
      -- `k+1` case: either `j = k` or `j < k`
      have hk' : k ≤ n := Nat.le_trans (Nat.le_of_lt (Nat.lt_succ_self k)) hk
      have hj_le : j.1 ≤ k := Nat.le_of_lt_succ hjk
      by_cases hjeq : j.1 = k
      · subst hjeq
        -- now `k = j`, so both sides are `getD j` from the `(j+1)` prefix list
        simp [gsoAtQ]
      · have hj_lt : j.1 < k := Nat.lt_of_le_of_ne hj_le hjeq
        rcases gsoPrefixListQ_succ_eq_append (n := n) B k (by simpa using hk) with ⟨us, bstar, hEq, hUs, _hB⟩
        have hEq' :
            gsoPrefixListQ (n := n) B (k + 1) (by simpa using hk) = (gsoPrefixListQ (n := n) B k hk') ++ [bstar] := by
          simpa [hUs] using hEq
        have hlen : (gsoPrefixListQ (n := n) B k hk').length = k := by
          simpa using gsoPrefixListQ_length (n := n) B k hk'
        have hj_lt_len : j.1 < (gsoPrefixListQ (n := n) B k hk').length := by
          simpa [hlen] using hj_lt
        have hgetD :
            (gsoPrefixListQ (n := n) B (k + 1) (by simpa using hk)).getD j.1 (zeroVecQ (n := n)) =
              (gsoPrefixListQ (n := n) B k hk').getD j.1 (zeroVecQ (n := n)) := by
          -- index `j` is within the left part, so `getD` comes from the prefix `k`
          simpa [hEq'] using
            (List.getD_append (l := gsoPrefixListQ (n := n) B k hk') (l' := [bstar]) (d := (zeroVecQ (n := n)))
              (n := j.1) hj_lt_len)
        -- finish by IH
        calc
          (gsoPrefixListQ (n := n) B (k + 1) (by simpa using hk)).getD j.1 (zeroVecQ (n := n))
              = (gsoPrefixListQ (n := n) B k hk').getD j.1 (zeroVecQ (n := n)) := hgetD
          _ = gsoAtQ (n := n) B j := ih (hk := hk') hj_lt

lemma gsoAtQ_eq_gsoVectorForKPrefix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) :
    gsoAtQ (n := n) B j =
      gsoVectorForKPrefix (n := n) (rowQ (n := n) B j)
        (gsoPrefixListQ (n := n) B j.1 (Nat.le_of_lt j.2)) := by
  -- unfold `gsoPrefixListQ` at `j+1` and use that the last element is the GS vector for row `j`.
  let us0 : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B j.1 (Nat.le_of_lt j.2)
  let ujGS : Fin n → ℚ := gsoVectorForKPrefix (n := n) (rowQ (n := n) B j) us0
  have hprefix :
      gsoPrefixListQ (n := n) B (j.1 + 1) (Nat.succ_le_of_lt j.2) = us0 ++ [ujGS] := by
    rcases gsoPrefixListQ_succ_eq_append (n := n) B j.1 (Nat.succ_le_of_lt j.2) with ⟨us, bstar, hEq, hUs, hB⟩
    subst hUs
    subst hB
    simpa [us0, ujGS] using hEq
  have hus0_len : us0.length = j.1 := by
    simpa [us0] using gsoPrefixListQ_length (n := n) B j.1 (Nat.le_of_lt j.2)
  have hlen_le : us0.length ≤ j.1 := by simpa [hus0_len]
  have hgetD : (us0 ++ [ujGS]).getD j.1 (zeroVecQ (n := n)) = ujGS := by
    -- reduce to the singleton tail
    simpa [hus0_len] using
      (List.getD_append_right (l := us0) (l' := [ujGS]) (d := (zeroVecQ (n := n))) (n := j.1) hlen_le)
  -- conclude by unfolding `gsoAtQ` and rewriting the prefix list
  calc
    gsoAtQ (n := n) B j =
        (gsoPrefixListQ (n := n) B (j.1 + 1) (Nat.succ_le_of_lt j.2)).getD j.1 (zeroVecQ (n := n)) := by
          simp [gsoAtQ]
    _ = (us0 ++ [ujGS]).getD j.1 (zeroVecQ (n := n)) := by
          simpa [hprefix]
    _ = ujGS := hgetD

theorem dotQ_row_lt_gsoAtQ_eq_zero {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n)
    (hij : (i : ℕ) < (j : ℕ))
    (hnz : ∀ u ∈ gsoPrefixListQ (n := n) B (j.1 + 1) (Nat.succ_le_of_lt j.2), dotQ (n := n) u u ≠ 0) :
    dotQ (n := n) (rowQ (n := n) B i) (gsoAtQ (n := n) B j) = 0 := by
  classical
  let us0 : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B j.1 (Nat.le_of_lt j.2)
  let uj : Fin n → ℚ := gsoAtQ (n := n) B j
  have huj : uj = gsoVectorForKPrefix (n := n) (rowQ (n := n) B j) us0 := by
    simpa [uj, us0] using (gsoAtQ_eq_gsoVectorForKPrefix (n := n) (B := B) j)

  -- `us0` inherits nondegeneracy from the `(j+1)` prefix list
  have hnz_us0 : ∀ u ∈ us0, dotQ (n := n) u u ≠ 0 := by
    intro u hu
    have hjp1 : j.1 + 1 ≤ n := Nat.succ_le_of_lt j.2
    have hu_in :
        u ∈ gsoPrefixListQ (n := n) B (j.1 + 1) hjp1 := by
      have := gsoPrefixListQ_mem_of_le (n := n) (B := B) (m := j.1) (k := j.1 + 1)
        (hmk := Nat.le_succ j.1) (hmn := Nat.le_of_lt j.2) (hkn := hjp1) u hu
      simpa [us0] using this
    exact hnz u hu_in

  have horth_us0 : us0.Pairwise (fun u w => dotQ (n := n) u w = 0) :=
    gsoPrefixListQ_pairwise_orth (n := n) (B := B) j.1 (Nat.le_of_lt j.2) hnz_us0

  -- The GS vector for row `j` is orthogonal to every `u ∈ us0`.
  have hdot_uj_left : ∀ u ∈ us0, dotQ (n := n) uj u = 0 := by
    intro u hu
    have :=
      dotQ_gsoVectorForKPrefix_mem_eq_zero (n := n) (bk := rowQ (n := n) B j) (us := us0) horth_us0 hnz_us0 u hu
    simpa [huj] using this
  have hdot_uj_right : ∀ u ∈ us0, dotQ (n := n) u uj = 0 := by
    intro u hu
    simpa [dotQ_comm] using hdot_uj_left u hu

  -- Decompose `row_i` into GS vector + projection sum over the `i`-prefix list.
  let usi : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B i.1 (Nat.le_of_lt i.2)
  let ui : Fin n → ℚ := gsoVectorForKPrefix (n := n) (rowQ (n := n) B i) usi
  have hdecomp :
      ui + projSumForKPrefix (n := n) (rowQ (n := n) B i) usi = rowQ (n := n) B i := by
    simpa [ui] using (gsoVectorForKPrefix_add_projSum_eq_bk (n := n) (bk := rowQ (n := n) B i) (us := usi))

  -- Show `usi ⊆ us0` since `i < j`.
  have husi_sub : ∀ u ∈ usi, u ∈ us0 := by
    intro u hu
    have hij_le : i.1 ≤ j.1 := Nat.le_of_lt hij
    have := gsoPrefixListQ_mem_of_le (n := n) (B := B) (m := i.1) (k := j.1) hij_le
      (hmn := Nat.le_of_lt i.2) (hkn := Nat.le_of_lt j.2) u hu
    simpa [usi, us0] using this

  -- `ui` is the GS vector appended at the end of the `(i+1)` prefix list, hence it lies in `us0`.
  have hui_mem_us0 : ui ∈ us0 := by
    have hip1 : i.1 + 1 ≤ n := Nat.succ_le_of_lt i.2
    rcases gsoPrefixListQ_succ_eq_append (n := n) B i.1 hip1 with ⟨us, bstar, hEq, hUs, hB⟩
    have hb : bstar = ui := by
      subst hUs
      subst hB
      rfl
    have hb_mem : bstar ∈ gsoPrefixListQ (n := n) B (i.1 + 1) hip1 := by
      have : bstar ∈ (gsoPrefixListQ (n := n) B i.1 (Nat.le_of_lt i.2)) ++ [bstar] := by simp
      -- rewrite via the succ-append equation
      simpa [hEq, hUs] using this
    have hip1_le_j : i.1 + 1 ≤ j.1 := Nat.succ_le_of_lt hij
    have hb_in_j :
        bstar ∈ gsoPrefixListQ (n := n) B j.1 (Nat.le_of_lt j.2) := by
      exact gsoPrefixListQ_mem_of_le (n := n) (B := B) (m := i.1 + 1) (k := j.1) hip1_le_j hip1 (Nat.le_of_lt j.2) bstar hb_mem
    simpa [us0, hb] using hb_in_j

  have hdot_ui : dotQ (n := n) ui uj = 0 := hdot_uj_right ui hui_mem_us0
  have hdot_proj : dotQ (n := n) (projSumForKPrefix (n := n) (rowQ (n := n) B i) usi) uj = 0 := by
    apply dotQ_projSumForKPrefix_right_eq_zero (n := n) (bk := rowQ (n := n) B i) (uj := uj) (us := usi)
    intro a ha
    exact hdot_uj_right a (husi_sub a ha)

  -- rewrite `row_i` and finish by linearity
  rw [← hdecomp]
  simp [dotQ_add_left, uj, hdot_ui, hdot_proj]

theorem muQ_size_reduceZ_invariant_of_lt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k i j : Fin n) (q : ℤ) (hjk : (j : ℕ) < (k : ℕ))
    (hden : dotQ (n := n) (gsoAtQ (n := n) B j) (gsoAtQ (n := n) B j) ≠ 0)
    (hz : dotQ (n := n) (rowQ (n := n) B i) (gsoAtQ (n := n) B j) = 0) :
    muQ (n := n) (size_reduceZ (n := n) B k i q) k j = muQ (n := n) B k j := by
  -- `gsoAtQ` at `j` is unchanged when updating row `k` with `k>j`
  have hgso : gsoAtQ (n := n) (size_reduceZ (n := n) B k i q) j = gsoAtQ (n := n) B j := by
    simpa using (gsoAtQ_size_reduceZ_of_lt (n := n) (B := B) (k := k) (j := i) (t := j) (q := q) hjk)
  let uj : Fin n → ℚ := gsoAtQ (n := n) B j
  have hden' : dotQ (n := n) uj uj ≠ 0 := by simpa [uj] using hden
  -- reduce to `muQPrefix` invariance
  have hμ :
      muQPrefix (n := n) (rowQ (n := n) (size_reduceZ (n := n) B k i q) k) uj =
        muQPrefix (n := n) (rowQ (n := n) B k) uj := by
    simpa [uj] using
      (muQPrefix_size_reduceZ_invariant_of_dot_zero (n := n) (B := B) (k := k) (j := i) (q := q) (u := uj) hden' (by simpa [uj] using hz))
  -- turn the `muQPrefix` equality into equality of numerators
  let denom : ℚ := dotQ (n := n) uj uj
  have hμ' :
      dotQ (n := n) (rowQ (n := n) (size_reduceZ (n := n) B k i q) k) uj / denom =
        dotQ (n := n) (rowQ (n := n) B k) uj / denom := by
    simpa [muQPrefix, denom, hden'] using hμ
  have hdot :
      dotQ (n := n) (rowQ (n := n) (size_reduceZ (n := n) B k i q) k) uj =
        dotQ (n := n) (rowQ (n := n) B k) uj := by
    have hμ'' := hμ'
    -- cancel `denom` using the nonzero hypothesis
    field_simp [denom, hden'] at hμ''
    exact hμ''
  -- unfold `muQ` on both sides and use `hgso` + `hdot`
  simp [muQ, uj, hgso, hden', hdot]

theorem sizeReducedMuQ_size_reduceZ_invariant_of_lt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k i j : Fin n) (q : ℤ) (hjk : (j : ℕ) < (k : ℕ))
    (hden : dotQ (n := n) (gsoAtQ (n := n) B j) (gsoAtQ (n := n) B j) ≠ 0)
    (hz : dotQ (n := n) (rowQ (n := n) B i) (gsoAtQ (n := n) B j) = 0) :
    sizeReducedMuQ (n := n) (size_reduceZ (n := n) B k i q) k j =
      sizeReducedMuQ (n := n) B k j := by
  have hμ := muQ_size_reduceZ_invariant_of_lt (n := n) (B := B) (k := k) (i := i) (j := j) (q := q) hjk hden hz
  simp [sizeReducedMuQ, hμ]

lemma js_ofFn_id_pairwise_lt (k : Nat) : (List.ofFn fun j : Fin k => j).Pairwise (· < ·) := by
  -- `ofFn id` is strictly increasing (adjacent chain), hence `Pairwise (<)`.
  have hchain : (List.ofFn fun j : Fin k => j).IsChain (· < ·) := by
    refine (List.isChain_ofFn (f := fun j : Fin k => j) (r := (· < ·))).2 ?_
    intro i hi
    -- consecutive indices are strictly increasing
    have : (⟨i, Nat.lt_of_succ_lt hi⟩ : Fin k) < (⟨i + 1, hi⟩ : Fin k) := by
      simpa [Fin.lt_def] using (Nat.lt_succ_self i)
    simpa using this
  have hsorted : (List.ofFn fun j : Fin k => j).SortedLT := (List.sortedLT_iff_isChain).2 hchain
  exact hsorted.pairwise

lemma rowQ_foldr_size_reduceZ_other {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hk : k < n)
    (js : List (Fin k))
    (q : Fin k → Matrix (Fin n) (Fin n) ℤ → ℤ)
    (i : Fin n) (hi : i ≠ (⟨k, hk⟩ : Fin n)) :
    rowQ (n := n)
        (js.foldr
          (fun (j : Fin k) acc =>
            size_reduceZ (n := n) acc ⟨k, hk⟩ ⟨(j : Nat), Nat.lt_trans j.2 hk⟩ (q j acc))
          B)
        i =
      rowQ (n := n) B i := by
  classical
  induction js generalizing B with
  | nil =>
      simp
  | cons a tl ih =>
      -- fold the tail first
      let f : Fin k → Matrix (Fin n) (Fin n) ℤ → Matrix (Fin n) (Fin n) ℤ :=
        fun (j : Fin k) acc =>
          size_reduceZ (n := n) acc ⟨k, hk⟩ ⟨(j : Nat), Nat.lt_trans j.2 hk⟩ (q j acc)
      let Btail := tl.foldr f B
      have hrow : rowQ (n := n) (f a Btail) i = rowQ (n := n) Btail i :=
        rowQ_size_reduceZ_other (n := n) (B := Btail) (k := ⟨k, hk⟩)
          (j := ⟨(a : Nat), Nat.lt_trans a.2 hk⟩) (i := i) (q := q a Btail) hi
      calc
        rowQ (n := n) ((a :: tl).foldr f B) i = rowQ (n := n) (f a Btail) i := by
          simp [List.foldr, Btail, f]
        _ = rowQ (n := n) Btail i := hrow
        _ = rowQ (n := n) B i := by
          simpa [Btail, f] using (ih (B := B))

lemma gsoAtQ_foldr_size_reduceZ_of_lt {n k : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hk : k < n)
    (js : List (Fin k))
    (q : Fin k → Matrix (Fin n) (Fin n) ℤ → ℤ)
    (t : Fin n) (ht : (t : ℕ) < k) :
    gsoAtQ (n := n)
        (js.foldr
          (fun (j : Fin k) acc =>
            size_reduceZ (n := n) acc ⟨k, hk⟩ ⟨(j : Nat), Nat.lt_trans j.2 hk⟩ (q j acc))
          B)
        t =
      gsoAtQ (n := n) B t := by
  classical
  induction js generalizing B with
  | nil =>
      simp
  | cons a tl ih =>
      let f : Fin k → Matrix (Fin n) (Fin n) ℤ → Matrix (Fin n) (Fin n) ℤ :=
        fun (j : Fin k) acc =>
          size_reduceZ (n := n) acc ⟨k, hk⟩ ⟨(j : Nat), Nat.lt_trans j.2 hk⟩ (q j acc)
      let Btail := tl.foldr f B
      have hgso : gsoAtQ (n := n) (f a Btail) t = gsoAtQ (n := n) Btail t :=
        gsoAtQ_size_reduceZ_of_lt (n := n) (B := Btail) (k := ⟨k, hk⟩)
          (j := ⟨(a : Nat), Nat.lt_trans a.2 hk⟩) (t := t) (q := q a Btail) ht
      calc
        gsoAtQ (n := n) ((a :: tl).foldr f B) t = gsoAtQ (n := n) (f a Btail) t := by
          simp [List.foldr, Btail, f]
        _ = gsoAtQ (n := n) Btail t := hgso
        _ = gsoAtQ (n := n) B t := by
          simpa [Btail, f] using (ih (B := B))

/-!
### Size-reduction postcondition for `sizeReduceAllExactWithPrefix`

We prove that the “descending” size-reduction loop (`foldr` over `0,1,...,k-1`) makes the row `k`
size-reduced against every `j < k` (in the computable boolean sense).
-/

theorem sizeReduceAllExactWithPrefix_sizeReducedMuQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n)
    (hnz : ∀ u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk), dotQ (n := n) u u ≠ 0) :
    let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
    ∀ j : Fin k,
      sizeReducedMuQ (n := n) B1 ⟨k, hk⟩ ⟨(j : Nat), Nat.lt_trans j.2 hk⟩ = true := by
  classical
  intro B1
  -- we will unfold `sizeReduceAllExactWithPrefix` at the end to identify `B1`
  -- reuse the same `us` as the implementation
  let us : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk)
  have hus : us = gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk) := rfl
  -- define the reduction step exactly as in `sizeReduceAllExactWithUs`
  let k' : Fin n := ⟨k, hk⟩
  let emb : Fin k → Fin n := fun j => ⟨(j : Nat), Nat.lt_trans j.2 hk⟩
  let step : Fin k → Matrix (Fin n) (Fin n) ℤ → Matrix (Fin n) (Fin n) ℤ :=
    fun (j : Fin k) acc =>
      let uj : Fin n → ℚ := us.getD j.val (zeroVecQ (n := n))
      let bk : Fin n → ℚ := rowQ (n := n) acc k'
      let μ : ℚ := muQPrefix (n := n) bk uj
      let q : ℤ := roundQ μ
      size_reduceZ (n := n) acc k' (emb j) q
  let js : List (Fin k) := List.ofFn (α := Fin k) (fun j : Fin k => j)
  have hpair : js.Pairwise (· < ·) := js_ofFn_id_pairwise_lt k

  -- convenient `q`-function (so we can use generic foldr invariance lemmas)
  let qfun : Fin k → Matrix (Fin n) (Fin n) ℤ → ℤ :=
    fun j acc =>
      let uj : Fin n → ℚ := us.getD j.val (zeroVecQ (n := n))
      let bk : Fin n → ℚ := rowQ (n := n) acc k'
      roundQ (muQPrefix (n := n) bk uj)

  have hstep : step =
      (fun (j : Fin k) acc => size_reduceZ (n := n) acc k' (emb j) (qfun j acc)) := by
    rfl

  -- main: prove `∀ j ∈ js, sizeReducedMuQ (foldr step B) k' (emb j) = true`
  have hmain : ∀ j ∈ js, sizeReducedMuQ (n := n) (js.foldr step B) k' (emb j) = true := by
    -- do list induction with the `Pairwise (<)` hypothesis to know “current j” is < all previously processed ones
    revert hpair
    induction js with
    | nil =>
        intro _ j hj
        cases hj
    | cons a tl ih =>
        intro hpair j hj
        have hrel : ∀ b ∈ tl, a < b := (List.pairwise_cons.1 hpair).1
        have hpair_tl : tl.Pairwise (· < ·) := (List.pairwise_cons.1 hpair).2
        have ih_tl : ∀ b ∈ tl, sizeReducedMuQ (n := n) (tl.foldr step B) k' (emb b) = true := by
          intro b hb
          exact ih hpair_tl b hb
        -- fold the tail first (descending order)
        let Btail := tl.foldr step B
        let uj_a : Fin n → ℚ := us.getD a.val (zeroVecQ (n := n))
        let μa : ℚ := muQPrefix (n := n) (rowQ (n := n) Btail k') uj_a
        let qa : ℤ := roundQ μa
        let Bnew : Matrix (Fin n) (Fin n) ℤ := size_reduceZ (n := n) Btail k' (emb a) qa
        have hfold : (a :: tl).foldr step B = Bnew := by
          simp [List.foldr, step, Btail, uj_a, μa, qa, Bnew]
        -- case split on whether `j = a` or `j ∈ tl`
        have hj_or : j = a ∨ j ∈ tl := by
          simpa using (List.mem_cons.1 hj)
        cases hj_or with
        | inl hEq =>
            subst j
            -- show the fresh coefficient `(k,a)` is size-reduced after this step
            have ha_lt_k : (a : ℕ) < k := a.2
            have ha'_lt_k' : ((emb a : Fin n) : ℕ) < (k' : ℕ) := by
              simpa [emb, k'] using ha_lt_k
            have ha'_ne_k' : (emb a : Fin n) ≠ k' := by
              intro hEq
              have := congrArg Fin.val hEq
              exact (Nat.ne_of_lt ha_lt_k) this
            -- denom nonzero for `uj_a`
            have hus_len : us.length = k := by
              simpa [us] using gsoPrefixListQ_length (n := n) B k (Nat.le_of_lt hk)
            have ha_lt_len : a.1 < us.length := by simpa [hus_len] using a.2
            let ia : Fin us.length := ⟨a.1, ha_lt_len⟩
            have huj_mem : uj_a ∈ us := by
              -- `uj_a` is the in-range `getD` at index `a`, hence equals `get ia` and is in the list
              have hgetD : us.getD (ia : ℕ) (zeroVecQ (n := n)) = us.get ia :=
                List.getD_eq_get (l := us) (d := (zeroVecQ (n := n))) ia
              have hgetD' : us.getD a.1 (zeroVecQ (n := n)) = us.get ia := by
                simpa [ia] using hgetD
              have hm : us.get ia ∈ us := List.get_mem us ia
              have : uj_a = us.get ia := by simpa [uj_a] using hgetD'
              -- avoid `simp` changing the proposition to `True`
              rw [this]
              exact hm
            have hden : dotQ (n := n) uj_a uj_a ≠ 0 := hnz uj_a (by simpa [us] using huj_mem)
            -- GS identity for this `uj_a` (computed from the fixed prefix list)
            have huj_as_gso : uj_a = gsoAtQ (n := n) B (emb a) := by
              -- `us = gsoPrefixListQ B k`, and `a < k`
              have : uj_a = (gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk)).getD a.1 (zeroVecQ (n := n)) := rfl
              simpa [us, uj_a] using
                (gsoPrefixListQ_getD_eq_gsoAtQ_of_lt (n := n) (B := B) (k := k) (hk := Nat.le_of_lt hk)
                  (j := emb a) (hjk := a.2))
            have hnz_a : ∀ u ∈ gsoPrefixListQ (n := n) B ((emb a).1 + 1) (Nat.succ_le_of_lt (Nat.lt_trans a.2 hk)),
                dotQ (n := n) u u ≠ 0 := by
              intro u hu
              -- `(a+1)`-prefix is contained in the `k`-prefix list `us`
              have hu_in_us :
                  u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk) := by
                have := gsoPrefixListQ_mem_of_le (n := n) (B := B) (m := (emb a).1 + 1) (k := k)
                  (hmk := Nat.succ_le_of_lt a.2) (hmn := Nat.succ_le_of_lt (Nat.lt_trans a.2 hk))
                  (hkn := Nat.le_of_lt hk) u hu
                simpa [us] using this
              exact hnz u (by simpa [us] using hu_in_us)
            have hgsB : dotQ (n := n) (rowQ (n := n) B (emb a)) uj_a = dotQ (n := n) uj_a uj_a := by
              -- use the “prefix” GS identity and rewrite `gsoAtQ` to `uj_a`
              have hgs' : dotQ (n := n) (rowQ (n := n) B (emb a)) (gsoAtQ (n := n) B (emb a)) =
                  dotQ (n := n) (gsoAtQ (n := n) B (emb a)) (gsoAtQ (n := n) B (emb a)) := by
                -- `dotQ_row_prefix_eq_normSq` plus `gsoAtQ_eq_gsoVectorForKPrefix`
                have := dotQ_row_prefix_eq_normSq (n := n) (B := B) (j := (emb a).1) (hj := (emb a).2) (hnz := hnz_a)
                simpa [gsoAtQ_eq_gsoVectorForKPrefix (n := n) (B := B) (emb a)] using this
              simpa [huj_as_gso] using hgs'
            -- transfer GS identity to `Btail` (row `a` is unchanged; `gsoAtQ` at `a` is unchanged)
            have hrow_a : rowQ (n := n) Btail (emb a) = rowQ (n := n) B (emb a) := by
              -- `Btail` is a foldr of `size_reduceZ` updates at row `k`
              simpa [Btail, hstep] using
                (rowQ_foldr_size_reduceZ_other (n := n) (B := B) (k := k) hk tl qfun (emb a) ha'_ne_k')
            have hgso_a : gsoAtQ (n := n) Btail (emb a) = gsoAtQ (n := n) B (emb a) := by
              simpa [Btail, hstep, emb] using
                (gsoAtQ_foldr_size_reduceZ_of_lt (n := n) (B := B) (k := k) hk tl qfun (emb a) a.2)
            have hgs_tail : dotQ (n := n) (rowQ (n := n) Btail (emb a)) uj_a = dotQ (n := n) uj_a uj_a := by
              simpa [hrow_a] using hgsB
            -- one-step bound for `muQPrefix` at `(k,a)` after the update
            have habs : |muQPrefix (n := n) (rowQ (n := n) Bnew k') uj_a| ≤ (1 / 2 : ℚ) := by
              -- apply the generic one-step lemma
              simpa [μa, qa, Bnew] using
                (abs_muQPrefix_after_size_reduceZ_le_half (n := n) (B := Btail) (k := k') (j := emb a)
                  (uj := uj_a) hden hgs_tail)
            -- now relate `muQ` (which uses `gsoAtQ`) to `muQPrefix` with the same `uj_a`
            have hgso_new : gsoAtQ (n := n) Bnew (emb a) = uj_a := by
              have hstep_gso :
                  gsoAtQ (n := n) Bnew (emb a) = gsoAtQ (n := n) Btail (emb a) := by
                -- `emb a < k`, so updating row `k` does not change `gsoAtQ` at `emb a`
                simpa [Bnew] using
                  (gsoAtQ_size_reduceZ_of_lt (n := n) (B := Btail) (k := k') (j := emb a) (t := emb a) (q := qa) ha'_lt_k')
              calc
                gsoAtQ (n := n) Bnew (emb a) = gsoAtQ (n := n) Btail (emb a) := hstep_gso
                _ = gsoAtQ (n := n) B (emb a) := hgso_a
                _ = uj_a := by simpa using huj_as_gso.symm
            have hmuQ : |muQ (n := n) Bnew k' (emb a)| ≤ (1 / 2 : ℚ) := by
              -- unfold muQ with denom≠0 and `gsoAtQ = uj_a`
              simpa [muQ, hgso_new, muQPrefix, hden] using habs
            -- conclude the boolean checker
            have : sizeReducedMuQ (n := n) Bnew k' (emb a) = true := by
              have hmuQ' : |muQ (n := n) Bnew k' (emb a)| ≤ (2⁻¹ : ℚ) := by
                simpa using hmuQ
              simpa [sizeReducedMuQ, hmuQ']
            simpa [hfold, Bnew] using this
        | inr hj_tl =>
            -- preserve size-reduction for indices in the tail
            have hj_lt_k : (j : ℕ) < k := j.2
            have hjk' : ((emb j : Fin n) : ℕ) < (k' : ℕ) := by simpa [emb, k'] using hj_lt_k
            -- invariance preconditions for `(k,j)` when updating with `a`
            have haj : a < j := hrel j hj_tl
            have hzB : dotQ (n := n) (rowQ (n := n) B (emb a)) (gsoAtQ (n := n) B (emb j)) = 0 := by
              -- `a < j` implies orthogonality
              have hnz_j : ∀ u ∈ gsoPrefixListQ (n := n) B ((emb j).1 + 1) (Nat.succ_le_of_lt (Nat.lt_trans j.2 hk)),
                  dotQ (n := n) u u ≠ 0 := by
                intro u hu
                have hu_in_us :
                    u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk) := by
                  have := gsoPrefixListQ_mem_of_le (n := n) (B := B) (m := (emb j).1 + 1) (k := k)
                    (hmk := Nat.succ_le_of_lt j.2) (hmn := Nat.succ_le_of_lt (Nat.lt_trans j.2 hk))
                    (hkn := Nat.le_of_lt hk) u hu
                  simpa [us] using this
                exact hnz u (by simpa [us] using hu_in_us)
              have haj' : ((emb a : Fin n) : ℕ) < ((emb j : Fin n) : ℕ) := by
                -- compare underlying values
                simpa [emb] using (show (a : ℕ) < (j : ℕ) from haj)
              simpa using dotQ_row_lt_gsoAtQ_eq_zero (n := n) (B := B) (i := emb a) (j := emb j) haj' hnz_j
            have hrow_a : rowQ (n := n) Btail (emb a) = rowQ (n := n) B (emb a) := by
              have ha'_ne_k' : (emb a : Fin n) ≠ k' := by
                intro hEq
                have := congrArg Fin.val hEq
                exact (Nat.ne_of_lt a.2) this
              simpa [Btail, hstep] using
                (rowQ_foldr_size_reduceZ_other (n := n) (B := B) (k := k) hk tl qfun (emb a) ha'_ne_k')
            have hgso_j : gsoAtQ (n := n) Btail (emb j) = gsoAtQ (n := n) B (emb j) := by
              simpa [Btail, hstep, emb] using
                (gsoAtQ_foldr_size_reduceZ_of_lt (n := n) (B := B) (k := k) hk tl qfun (emb j) j.2)
            have hz : dotQ (n := n) (rowQ (n := n) Btail (emb a)) (gsoAtQ (n := n) Btail (emb j)) = 0 := by
              simpa [hrow_a, hgso_j] using hzB
            -- denom nonzero for `gsoAtQ ... j`
            have hden : dotQ (n := n) (gsoAtQ (n := n) Btail (emb j)) (gsoAtQ (n := n) Btail (emb j)) ≠ 0 := by
              -- `gsoAtQ` at `<k` is invariant and its norm is nonzero by `hnz` on `us`
              have hus_len : us.length = k := by
                simpa [us] using gsoPrefixListQ_length (n := n) B k (Nat.le_of_lt hk)
              have hj_lt_len : j.1 < us.length := by simpa [hus_len] using j.2
              let ij : Fin us.length := ⟨j.1, hj_lt_len⟩
              have hgetD : us.getD j.1 (zeroVecQ (n := n)) = us.get ij := by
                have htmp : us.getD (ij : ℕ) (zeroVecQ (n := n)) = us.get ij :=
                  List.getD_eq_get (l := us) (d := (zeroVecQ (n := n))) ij
                simpa [ij] using htmp
              have hj_mem : us.getD j.1 (zeroVecQ (n := n)) ∈ us := by
                have hm : us.get ij ∈ us := List.get_mem us ij
                rw [hgetD]
                exact hm
              have hgso_us : us.getD j.1 (zeroVecQ (n := n)) = gsoAtQ (n := n) B (emb j) := by
                simpa [us] using
                  (gsoPrefixListQ_getD_eq_gsoAtQ_of_lt (n := n) (B := B) (k := k) (hk := Nat.le_of_lt hk)
                    (j := emb j) (hjk := j.2))
              have hj_in : gsoAtQ (n := n) B (emb j) ∈ us := by
                -- rewrite the element using `hgso_us`
                have : gsoAtQ (n := n) B (emb j) = us.getD j.1 (zeroVecQ (n := n)) := by
                  simpa using hgso_us.symm
                rw [this]
                exact hj_mem
              have hdenB :
                  dotQ (n := n) (gsoAtQ (n := n) B (emb j)) (gsoAtQ (n := n) B (emb j)) ≠ 0 :=
                hnz (gsoAtQ (n := n) B (emb j)) (by simpa [us] using hj_in)
              simpa [hgso_j] using hdenB
            -- apply size-reduction invariance
            have hinv :
                sizeReducedMuQ (n := n) Bnew k' (emb j) =
                  sizeReducedMuQ (n := n) Btail k' (emb j) := by
              simpa [Bnew] using
                (sizeReducedMuQ_size_reduceZ_invariant_of_lt (n := n) (B := Btail) (k := k') (i := emb a) (j := emb j)
                  (q := qa) hjk' hden hz)
            have := ih_tl j hj_tl
            -- conclude using the IH and invariance equality
            simpa [hfold, hinv, Bnew, Btail] using this

  -- convert `∀ j ∈ js` into `∀ j : Fin k` (since `js = ofFn id`)
  have hall : ∀ j : Fin k, sizeReducedMuQ (n := n) (js.foldr step B) k' (emb j) = true := by
    have hforall : ∀ x ∈ js, sizeReducedMuQ (n := n) (js.foldr step B) k' (emb x) = true := by
      intro x hx
      exact hmain x hx
    simpa [js] using (List.forall_mem_ofFn_iff (f := fun j : Fin k => j) (P := fun x => sizeReducedMuQ (n := n) (js.foldr step B) k' (emb x) = true)).1 hforall

  -- finally identify `B1` with the folded result
  have hB1 : B1 = js.foldr step B := by
    -- unfold the `let B1 := ...` binder and the definitions
    dsimp [B1, sizeReduceAllExactWithPrefix, us, sizeReduceAllExactWithUs, js, step, k', emb]
  intro j
  simpa [hB1, k', emb] using hall j

/-!
### Lifting size-reduction through the main loop (size-reduction half)

We introduce a simple “size-reduced below `k`” invariant on a basis `B`.
-/

def SizeReducedBelow {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) : Prop :=
  ∀ i j : Fin n, (i : ℕ) < k → (j : ℕ) < (i : ℕ) → sizeReducedMuQ (n := n) B i j = true

lemma SizeReducedBelow_mono {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) {k k' : Nat}
    (hkk' : k ≤ k') (h : SizeReducedBelow (n := n) B k') : SizeReducedBelow (n := n) B k := by
  intro i j hi hj
  exact h i j (Nat.lt_of_lt_of_le hi hkk') hj

theorem SizeReducedBelow_after_sizeReduceAllExactWithPrefix
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n)
    (hnz : ∀ u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk), dotQ (n := n) u u ≠ 0)
    (hbelow : SizeReducedBelow (n := n) B k) :
    let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
    SizeReducedBelow (n := n) B1 (k + 1) := by
  classical
  intro B1
  intro i j hi hj
  by_cases hik : (i : ℕ) < k
  · -- rows `< k` are unchanged by size reduction on row `k`
    -- `B1` differs from `B` only in row `k`, and `gsoAtQ` for `j<i<k` depends only on rows `< k`.
    -- We reduce `muQ` equality to row + gsoAtQ equality.
    have hi_ne : i ≠ (⟨k, hk⟩ : Fin n) := by
      intro hEq
      have := congrArg Fin.val hEq
      exact (Nat.ne_of_lt hik) this
    -- show `rowQ B1 i = rowQ B i`
    have hrow : rowQ (n := n) B1 i = rowQ (n := n) B i := by
      -- `sizeReduceAllExactWithPrefix` is a foldr of `size_reduceZ` updates at row `k`
      -- so other rows are unchanged
      -- (use the generic lemma with the `qfun` from the implementation)
      let us : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk)
      let k' : Fin n := ⟨k, hk⟩
      let emb : Fin k → Fin n := fun j => ⟨(j : Nat), Nat.lt_trans j.2 hk⟩
      let qfun : Fin k → Matrix (Fin n) (Fin n) ℤ → ℤ :=
        fun j acc =>
          let uj : Fin n → ℚ := us.getD j.val (zeroVecQ (n := n))
          let bk : Fin n → ℚ := rowQ (n := n) acc k'
          roundQ (muQPrefix (n := n) bk uj)
      let js : List (Fin k) := List.ofFn (α := Fin k) (fun j : Fin k => j)
      have hB1 : B1 =
          js.foldr
            (fun (j : Fin k) acc => size_reduceZ (n := n) acc k' (emb j) (qfun j acc))
            B := by
        -- unfold defs; `simp` is enough here
        simp [sizeReduceAllExactWithPrefix, sizeReduceAllExactWithUs, js, qfun, emb, k', us, B1]
      have : rowQ (n := n)
            (js.foldr (fun (j : Fin k) acc => size_reduceZ (n := n) acc k' (emb j) (qfun j acc)) B) i
          = rowQ (n := n) B i :=
        rowQ_foldr_size_reduceZ_other (n := n) (B := B) (k := k) hk js qfun i (by simpa [k'] using hi_ne)
      simpa [hB1] using this
    -- show `gsoAtQ B1 j = gsoAtQ B j` since `j < i < k`
    have hjk : (j : ℕ) < k := Nat.lt_trans hj hik
    have hgso : gsoAtQ (n := n) B1 j = gsoAtQ (n := n) B j := by
      let us : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk)
      let k' : Fin n := ⟨k, hk⟩
      let emb : Fin k → Fin n := fun j => ⟨(j : Nat), Nat.lt_trans j.2 hk⟩
      let qfun : Fin k → Matrix (Fin n) (Fin n) ℤ → ℤ :=
        fun j acc =>
          let uj : Fin n → ℚ := us.getD j.val (zeroVecQ (n := n))
          let bk : Fin n → ℚ := rowQ (n := n) acc k'
          roundQ (muQPrefix (n := n) bk uj)
      let js : List (Fin k) := List.ofFn (α := Fin k) (fun j : Fin k => j)
      have hB1 : B1 =
          js.foldr
            (fun (j : Fin k) acc => size_reduceZ (n := n) acc k' (emb j) (qfun j acc))
            B := by
        simp [sizeReduceAllExactWithPrefix, sizeReduceAllExactWithUs, js, qfun, emb, k', us, B1]
      have : gsoAtQ (n := n)
            (js.foldr (fun (j : Fin k) acc => size_reduceZ (n := n) acc k' (emb j) (qfun j acc)) B) j
          = gsoAtQ (n := n) B j :=
        gsoAtQ_foldr_size_reduceZ_of_lt (n := n) (B := B) (k := k) hk js qfun j (by simpa using hjk)
      simpa [hB1] using this
    -- unfold `sizeReducedMuQ` and rewrite `muQ`
    have : muQ (n := n) B1 i j = muQ (n := n) B i j := by
      simp [muQ, hrow, hgso]
    -- conclude from the invariant on `B`
    have hb : sizeReducedMuQ (n := n) B i j = true := hbelow i j hik hj
    simpa [sizeReducedMuQ, this] using hb
  · -- `i = k` (since `i < k+1` but not `< k`)
    have hi_eq : (i : ℕ) = k := Nat.eq_of_lt_succ_of_not_lt hi hik
    have hi_val : i.1 = k := hi_eq
    -- reduce to the per-`k` postcondition we proved
    have hrowk : i = (⟨k, hk⟩ : Fin n) := by
      apply Fin.ext
      simpa [hi_val]
    subst hrowk
    have hj_fin : (j : ℕ) < k := by simpa [hi_val] using hj
    -- package `j` as `Fin k`
    let j' : Fin k := ⟨j.1, by simpa using hj_fin⟩
    have h := sizeReduceAllExactWithPrefix_sizeReducedMuQ (n := n) (B := B) (k := k) hk hnz
    have := h j'
    simpa [B1, j', Fin.eta] using this

lemma SizeReducedBelow_one {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : SizeReducedBelow (n := n) B 1 := by
  intro i j hi hj
  -- `i < 1` forces `i.val = 0`, then `j < i` is impossible
  have hi0 : (i : ℕ) = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hi)
  have : False := by
    have hj0 : (j : ℕ) < 0 := by simpa [hi0] using hj
    exact Nat.not_lt_zero _ hj0
  exact this.elim

lemma rowQ_swap_vectors_other {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j i : Fin n)
    (hik : i ≠ k) (hij : i ≠ j) :
    rowQ (n := n) (swap_vectors (n := n) B k j) i = rowQ (n := n) B i := by
  ext t
  simp [rowQ, swap_vectors, Equiv.swap_apply_of_ne_of_ne hik hij]

theorem gsoPrefixListQ_swap_vectors_of_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k j : Fin n) (hjk : (j : ℕ) < (k : ℕ)) (m : Nat) (hmj : m ≤ (j : Nat)) (hmn : m ≤ n) :
    gsoPrefixListQ (n := n) (swap_vectors (n := n) B k j) m hmn =
      gsoPrefixListQ (n := n) B m hmn := by
  -- swap only touches rows `k` and `j`, and `m ≤ j < k` means rows `< m` are unaffected
  induction m with
  | zero =>
      simp [gsoPrefixListQ]
  | succ m ih =>
      have hmn' : m ≤ n := Nat.le_trans (Nat.le_succ m) hmn
      have hmj' : m ≤ (j : Nat) := Nat.le_trans (Nat.le_succ m) hmj
      have hm_lt_j : m < (j : Nat) := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hmj
      have hm_lt_n : m < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hmn
      let i' : Fin n := ⟨m, hm_lt_n⟩
      have hik : i' ≠ k := by
        intro hEq
        have := congrArg Fin.val hEq
        exact (Nat.ne_of_lt (Nat.lt_trans hm_lt_j hjk)) this
      have hij : i' ≠ j := by
        intro hEq
        have := congrArg Fin.val hEq
        exact (Nat.ne_of_lt hm_lt_j) this
      have hrow :
          rowQ (n := n) (swap_vectors (n := n) B k j) i' = rowQ (n := n) B i' :=
        rowQ_swap_vectors_other (n := n) (B := B) (k := k) (j := j) (i := i') hik hij
      simp [gsoPrefixListQ, ih (hmn := hmn') (hmj := hmj'), i', hrow]

theorem gsoAtQ_swap_vectors_of_lt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k j t : Fin n) (hjk : (j : ℕ) < (k : ℕ)) (ht : (t : ℕ) < (j : ℕ)) :
    gsoAtQ (n := n) (swap_vectors (n := n) B k j) t = gsoAtQ (n := n) B t := by
  have htp1_le_j : t.1 + 1 ≤ (j : Nat) := Nat.succ_le_of_lt ht
  have htp1_le_n : t.1 + 1 ≤ n := Nat.succ_le_of_lt t.2
  simp [gsoAtQ]
  have := gsoPrefixListQ_swap_vectors_of_le (n := n) (B := B) (k := k) (j := j) hjk
    (m := t.1 + 1) (hmj := htp1_le_j) (hmn := htp1_le_n)
  simpa using congrArg (fun us => us.getD t.1 (zeroVecQ (n := n))) this

theorem SizeReducedBelow_swap_vectors_of_le {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ)
    (k j : Fin n) (hjk : (j : ℕ) < (k : ℕ)) (m : Nat) (hmj : m ≤ (j : Nat))
    (h : SizeReducedBelow (n := n) B m) :
    SizeReducedBelow (n := n) (swap_vectors (n := n) B k j) m := by
  intro i x hi hx
  have hi_lt_j : (i : ℕ) < (j : ℕ) := Nat.lt_of_lt_of_le hi hmj
  have hx_lt_j : (x : ℕ) < (j : ℕ) := Nat.lt_of_lt_of_le (Nat.lt_trans hx hi) hmj
  have hrow_i :
      rowQ (n := n) (swap_vectors (n := n) B k j) i = rowQ (n := n) B i := by
    -- `i < j < k`
    have hik : i ≠ k := by
      intro hEq
      have := congrArg Fin.val hEq
      exact (Nat.ne_of_lt (Nat.lt_trans hi_lt_j hjk)) this
    have hij : i ≠ j := by
      intro hEq
      have := congrArg Fin.val hEq
      exact (Nat.ne_of_lt hi_lt_j) this
    exact rowQ_swap_vectors_other (n := n) (B := B) (k := k) (j := j) (i := i) hik hij
  have hgso_x :
      gsoAtQ (n := n) (swap_vectors (n := n) B k j) x = gsoAtQ (n := n) B x := by
    exact gsoAtQ_swap_vectors_of_lt (n := n) (B := B) (k := k) (j := j) (t := x) hjk hx_lt_j
  have hmu : muQ (n := n) (swap_vectors (n := n) B k j) i x = muQ (n := n) B i x := by
    simp [muQ, hrow_i, hgso_x]
  have hb : sizeReducedMuQ (n := n) B i x = true := h i x hi hx
  simpa [sizeReducedMuQ, hmu] using hb

theorem lllRunExactGo_preserves_SizeReducedBelow
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k steps fuel : Nat)
    (hnz_all :
      ∀ (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n),
        ∀ u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk), dotQ (n := n) u u ≠ 0)
    (hbelow : SizeReducedBelow (n := n) B k) :
    SizeReducedBelow (n := n) (lllRunExactGo (n := n) B δ k steps fuel).basis
      (lllRunExactGo (n := n) B δ k steps fuel).final_k := by
  induction fuel generalizing B k steps with
  | zero =>
      simpa [lllRunExactGo] using hbelow
  | succ fuel ih =>
      by_cases hk : k < n
      · by_cases h0 : k = 0
        · subst h0
          -- move to k=1; size-reduction below 1 is trivial
          simpa [lllRunExactGo, hk] using
            (ih (B := B) (k := 1) (steps := steps + 1) (SizeReducedBelow_one (n := n) B))
        · -- k>0 step: size-reduce row k, then either advance or swap+recurse
          have hk0 : 0 < k := Nat.pos_of_ne_zero h0
          let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
          have hbelow1 : SizeReducedBelow (n := n) B1 (k + 1) := by
            -- apply our lemma (requires hnz on the k-prefix list)
            have hnz : ∀ u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk), dotQ (n := n) u u ≠ 0 :=
              hnz_all B k hk
            simpa [B1] using
              (SizeReducedBelow_after_sizeReduceAllExactWithPrefix (n := n) (B := B) (k := k) hk hnz hbelow)
          let km1 : Nat := k - 1
          have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
          let k' : Fin n := ⟨k, hk⟩
          let km1' : Fin n := ⟨km1, hkm1⟩
          by_cases hL : lovaszQ (n := n) B1 k' km1' δ = true
          · -- advance: recurse at k+1 with invariant up to k+1
            simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL] using
              (ih (B := B1) (k := k + 1) (steps := steps + 1) hbelow1)
          · -- swap: recurse at km1 with invariant up to km1
            let B2 := swap_vectors (n := n) B1 k' km1'
            have hkm1_lt_k : (km1' : ℕ) < (k' : ℕ) := by
              -- km1 = k-1 < k
              have : km1 < k := by simpa [km1] using Nat.pred_lt h0
              simpa [k', km1'] using this
            have hbelow_km1 : SizeReducedBelow (n := n) B1 km1 := by
              have hkm1_le : km1 ≤ k + 1 := by
                exact Nat.le_trans (by simpa [km1] using Nat.pred_le k) (Nat.le_succ k)
              exact SizeReducedBelow_mono (n := n) (B := B1) (k := km1) (k' := k + 1) hkm1_le hbelow1
            have hbelow2 : SizeReducedBelow (n := n) B2 km1 := by
              -- swapping rows k and km1 does not affect indices < km1
              exact SizeReducedBelow_swap_vectors_of_le (n := n) (B := B1) (k := k') (j := km1')
                hkm1_lt_k (m := km1) (hmj := Nat.le_refl km1) hbelow_km1
            simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL, B2] using
              (ih (B := B2) (k := km1) (steps := steps + 1) hbelow2)
      · -- already finished (k ≥ n): basis=B, final_k=k
        simpa [lllRunExactGo, hk] using hbelow

/-!
### Size reduction: make the nondegeneracy assumption local to the run

The earlier size-reduction lift assumed a very strong `hnz_all` hypothesis quantified over *all* bases.
For downstream use it is nicer to assume nondegeneracy only **along the actual run**.
-/

def HNZAt {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n) : Prop :=
  ∀ u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk), dotQ (n := n) u u ≠ 0

def HNZAlongRun {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k steps fuel : Nat) : Prop :=
  match fuel with
  | 0 => True
  | fuel' + 1 =>
      if hk : k < n then
        if h0 : k = 0 then
          HNZAlongRun (n := n) B δ 1 (steps + 1) fuel'
        else
          HNZAt (n := n) B k hk ∧
            let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
            let km1 : Nat := k - 1
            have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
            let k' : Fin n := ⟨k, hk⟩
            let km1' : Fin n := ⟨km1, hkm1⟩
            if lovaszQ (n := n) B1 k' km1' δ = true then
              HNZAlongRun (n := n) B1 δ (k + 1) (steps + 1) fuel'
            else
              let B2 := swap_vectors (n := n) B1 k' km1'
              HNZAlongRun (n := n) B2 δ km1 (steps + 1) fuel'
      else
        True

theorem HNZAlongRun_of_hnz_all
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k steps fuel : Nat)
    (hnz_all :
      ∀ (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n),
        ∀ u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk), dotQ (n := n) u u ≠ 0) :
    HNZAlongRun (n := n) B δ k steps fuel := by
  induction fuel generalizing B k steps with
  | zero =>
      simp [HNZAlongRun]
  | succ fuel ih =>
      by_cases hk : k < n
      · by_cases h0 : k = 0
        · subst h0
          simpa [HNZAlongRun, hk] using ih (B := B) (k := 1) (steps := steps + 1)
        · -- k>0: record `HNZAt` for this step, then follow the chosen recursive branch
          let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
          let km1 : Nat := k - 1
          have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
          let k' : Fin n := ⟨k, hk⟩
          let km1' : Fin n := ⟨km1, hkm1⟩
          by_cases hL : lovaszQ (n := n) B1 k' km1' δ = true
          · have hnext : HNZAlongRun (n := n) B1 δ (k + 1) (steps + 1) fuel :=
              ih (B := B1) (k := k + 1) (steps := steps + 1)
            have : HNZAlongRun (n := n) B δ k steps (fuel + 1) := by
              simpa [HNZAlongRun, hk, h0, hL, HNZAt, B1, km1, hkm1, k', km1'] using
                And.intro (hnz_all B k hk) hnext
            exact this
          · let B2 := swap_vectors (n := n) B1 k' km1'
            have hnext : HNZAlongRun (n := n) B2 δ km1 (steps + 1) fuel :=
              ih (B := B2) (k := km1) (steps := steps + 1)
            have : HNZAlongRun (n := n) B δ k steps (fuel + 1) := by
              simpa [HNZAlongRun, hk, h0, hL, HNZAt, B1, km1, hkm1, k', km1', B2] using
                And.intro (hnz_all B k hk) hnext
            exact this
      · simp [HNZAlongRun, hk]

theorem lllRunExactGo_preserves_SizeReducedBelow_of_hnzRun
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k steps fuel : Nat)
    (hnz_run : HNZAlongRun (n := n) B δ k steps fuel)
    (hbelow : SizeReducedBelow (n := n) B k) :
    SizeReducedBelow (n := n) (lllRunExactGo (n := n) B δ k steps fuel).basis
      (lllRunExactGo (n := n) B δ k steps fuel).final_k := by
  induction fuel generalizing B k steps with
  | zero =>
      simpa [lllRunExactGo] using hbelow
  | succ fuel ih =>
      by_cases hk : k < n
      · by_cases h0 : k = 0
        · subst h0
          have hnz' : HNZAlongRun (n := n) B δ 1 (steps + 1) fuel := by
            simpa [HNZAlongRun, hk] using hnz_run
          simpa [lllRunExactGo, hk] using
            (ih (B := B) (k := 1) (steps := steps + 1) hnz' (SizeReducedBelow_one (n := n) B))
        · have hk0 : 0 < k := Nat.pos_of_ne_zero h0
          have hnz_run' :
              HNZAt (n := n) B k hk ∧
                (let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
                 let km1 : Nat := k - 1
                 have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
                 let k' : Fin n := ⟨k, hk⟩
                 let km1' : Fin n := ⟨km1, hkm1⟩
                 if lovaszQ (n := n) B1 k' km1' δ = true then
                   HNZAlongRun (n := n) B1 δ (k + 1) (steps + 1) fuel
                 else
                   let B2 := swap_vectors (n := n) B1 k' km1'
                   HNZAlongRun (n := n) B2 δ km1 (steps + 1) fuel) := by
            simpa [HNZAlongRun, hk, h0] using hnz_run
          have hnz : HNZAt (n := n) B k hk := hnz_run'.1
          let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
          have hbelow1 : SizeReducedBelow (n := n) B1 (k + 1) := by
            simpa [B1] using
              (SizeReducedBelow_after_sizeReduceAllExactWithPrefix (n := n) (B := B) (k := k) hk hnz hbelow)
          let km1 : Nat := k - 1
          have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
          let k' : Fin n := ⟨k, hk⟩
          let km1' : Fin n := ⟨km1, hkm1⟩
          by_cases hL : lovaszQ (n := n) B1 k' km1' δ = true
          · have hnz' : HNZAlongRun (n := n) B1 δ (k + 1) (steps + 1) fuel := by
              simpa [B1, km1, hkm1, k', km1', hL] using hnz_run'.2
            simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL] using
              (ih (B := B1) (k := k + 1) (steps := steps + 1) hnz' hbelow1)
          · let B2 := swap_vectors (n := n) B1 k' km1'
            have hkm1_lt_k : (km1' : ℕ) < (k' : ℕ) := by
              have : km1 < k := by simpa [km1] using Nat.pred_lt h0
              simpa [k', km1'] using this
            have hbelow_km1 : SizeReducedBelow (n := n) B1 km1 := by
              have hkm1_le : km1 ≤ k + 1 := by
                exact Nat.le_trans (by simpa [km1] using Nat.pred_le k) (Nat.le_succ k)
              exact SizeReducedBelow_mono (n := n) (B := B1) (k := km1) (k' := k + 1) hkm1_le hbelow1
            have hbelow2 : SizeReducedBelow (n := n) B2 km1 := by
              exact SizeReducedBelow_swap_vectors_of_le (n := n) (B := B1) (k := k') (j := km1')
                hkm1_lt_k (m := km1) (hmj := Nat.le_refl km1) hbelow_km1
            have hnz' : HNZAlongRun (n := n) B2 δ km1 (steps + 1) fuel := by
              simpa [B1, km1, hkm1, k', km1', hL, B2] using hnz_run'.2
            simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL, B2] using
              (ih (B := B2) (k := km1) (steps := steps + 1) hnz' hbelow2)
      · simpa [lllRunExactGo, hk] using hbelow

theorem SizeReducedBelow_isSizeReducedQ_of_ge {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat)
    (hkn : n ≤ k) (h : SizeReducedBelow (n := n) B k) :
    isSizeReducedQ (n := n) B = true := by
  -- use the semantic lemma `isSizeReducedQ_of_forall`
  refine isSizeReducedQ_of_forall (n := n) (B := B) ?_
  intro i j hij
  have hi : (i : ℕ) < k := Nat.lt_of_lt_of_le i.2 hkn
  exact h i j hi hij

theorem lllRunExactGo_finished_final_k_ge_n
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k steps fuel : Nat) :
    (lllRunExactGo (n := n) B δ k steps fuel).reason = .finished →
      n ≤ (lllRunExactGo (n := n) B δ k steps fuel).final_k := by
  induction fuel generalizing B k steps with
  | zero =>
      intro h
      simp [lllRunExactGo] at h
  | succ fuel ih =>
      intro h
      by_cases hk : k < n
      · -- unfold one step, then recurse into the branch that must have finished
        by_cases h0 : k = 0
        · subst h0
          -- finish can only come from the recursive call at k=1
          have h' : (lllRunExactGo (n := n) B δ 1 (steps + 1) fuel).reason = .finished := by
            simpa [lllRunExactGo, hk] using h
          simpa [lllRunExactGo, hk] using ih (B := B) (k := 1) (steps := steps + 1) h'
        · -- k>0: split on Lovász branch and apply IH to the recursive call
          -- Reconstruct the same `B1`, `km1`, etc. as in the definition.
          -- Reconstruct the same `B1`, `km1`, etc. as in the definition.
          have hk0 : 0 < k := Nat.pos_of_ne_zero h0
          let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
          let km1 : Nat := k - 1
          have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
          let k' : Fin n := ⟨k, hk⟩
          let km1' : Fin n := ⟨km1, hkm1⟩
          by_cases hL : lovaszQ (n := n) B1 k' km1' δ = true
          · -- recurse at k+1
            have h' : (lllRunExactGo (n := n) B1 δ (k + 1) (steps + 1) fuel).reason = .finished := by
              simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL] using h
            simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL] using
              ih (B := B1) (k := k + 1) (steps := steps + 1) h'
          · -- recurse at km1
            let B2 := swap_vectors (n := n) B1 k' km1'
            have h' : (lllRunExactGo (n := n) B2 δ km1 (steps + 1) fuel).reason = .finished := by
              simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL, B2] using h
            simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL, B2] using
              ih (B := B2) (k := km1) (steps := steps + 1) h'
      · -- already finished: final_k = k and hk is false so k ≥ n
        have hkn : n ≤ k := Nat.le_of_not_gt hk
        simpa [lllRunExactGo, hk, hkn] using hkn

theorem lllRunExactGo_finished_isSizeReducedQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k steps fuel : Nat)
    (hnz_all :
      ∀ (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n),
        ∀ u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk), dotQ (n := n) u u ≠ 0)
    (hbelow : SizeReducedBelow (n := n) B k) :
    (lllRunExactGo (n := n) B δ k steps fuel).reason = .finished →
      isSizeReducedQ (n := n) (lllRunExactGo (n := n) B δ k steps fuel).basis = true := by
  intro hfin
  set r := lllRunExactGo (n := n) B δ k steps fuel
  have hbelow_r : SizeReducedBelow (n := n) r.basis r.final_k := by
    simpa [r] using lllRunExactGo_preserves_SizeReducedBelow (n := n) (B := B) (δ := δ) (k := k) (steps := steps)
      (fuel := fuel) hnz_all hbelow
  have hkn : n ≤ r.final_k := by
    simpa [r] using lllRunExactGo_finished_final_k_ge_n (n := n) (B := B) (δ := δ) (k := k) (steps := steps) (fuel := fuel) hfin
  have : isSizeReducedQ (n := n) r.basis = true := SizeReducedBelow_isSizeReducedQ_of_ge (n := n) (B := r.basis) (k := r.final_k) hkn hbelow_r
  simpa [r] using this

theorem lllRunExact_finished_isSizeReducedQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (limit : Nat)
    (hnz_all :
      ∀ (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n),
        ∀ u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk), dotQ (n := n) u u ≠ 0) :
    (lllRunExact (n := n) B δ limit).reason = .finished →
      isSizeReducedQ (n := n) (lllRunExact (n := n) B δ limit).basis = true := by
  -- `lllRunExact` starts at `k=1`, where `SizeReducedBelow` is trivial
  simpa [lllRunExact] using
    (lllRunExactGo_finished_isSizeReducedQ (n := n) (B := B) (δ := δ) (k := 1) (steps := 0) (fuel := limit)
      hnz_all (SizeReducedBelow_one (n := n) B))

theorem lllRunExactGo_finished_isSizeReducedQ_of_hnzRun
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k steps fuel : Nat)
    (hnz_run : HNZAlongRun (n := n) B δ k steps fuel)
    (hbelow : SizeReducedBelow (n := n) B k) :
    (lllRunExactGo (n := n) B δ k steps fuel).reason = .finished →
      isSizeReducedQ (n := n) (lllRunExactGo (n := n) B δ k steps fuel).basis = true := by
  intro hfin
  set r := lllRunExactGo (n := n) B δ k steps fuel
  have hbelow_r : SizeReducedBelow (n := n) r.basis r.final_k := by
    simpa [r] using
      lllRunExactGo_preserves_SizeReducedBelow_of_hnzRun (n := n) (B := B) (δ := δ) (k := k) (steps := steps) (fuel := fuel)
        hnz_run hbelow
  have hkn : n ≤ r.final_k := by
    simpa [r] using lllRunExactGo_finished_final_k_ge_n (n := n) (B := B) (δ := δ) (k := k) (steps := steps) (fuel := fuel) hfin
  have : isSizeReducedQ (n := n) r.basis = true :=
    SizeReducedBelow_isSizeReducedQ_of_ge (n := n) (B := r.basis) (k := r.final_k) hkn hbelow_r
  simpa [r] using this

theorem lllRunExact_finished_isSizeReducedQ_of_hnzRun
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (limit : Nat)
    (hnz_run : HNZAlongRun (n := n) B δ 1 0 limit) :
    (lllRunExact (n := n) B δ limit).reason = .finished →
      isSizeReducedQ (n := n) (lllRunExact (n := n) B δ limit).basis = true := by
  simpa [lllRunExact] using
    (lllRunExactGo_finished_isSizeReducedQ_of_hnzRun (n := n) (B := B) (δ := δ) (k := 1) (steps := 0) (fuel := limit)
      hnz_run (SizeReducedBelow_one (n := n) B))

/-!
### Lifting Lovász through the main loop

Unlike the size-reduction proof, the Lovász-side lift does **not** need nondegeneracy: both `muQ`
and `gsoNormSqQ` have a defined `denom = 0` fallback.
-/

def LovaszBelow {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (K : Nat) : Prop :=
  ∀ k : Fin n,
    (k : ℕ) < K →
      (hk0 : (0 : ℕ) < (k : ℕ)) →
        let km1Nat : ℕ := (k : ℕ) - 1
        have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) k.2
        let km1 : Fin n := ⟨km1Nat, hkm1⟩
        lovaszQ (n := n) B k km1 δ = true

lemma LovaszBelow_mono {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) {K K' : Nat}
    (hKK' : K ≤ K') (h : LovaszBelow (n := n) B δ K') : LovaszBelow (n := n) B δ K := by
  intro k hk hk0
  exact h k (Nat.lt_of_lt_of_le hk hKK') hk0

lemma LovaszBelow_one {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) : LovaszBelow (n := n) B δ 1 := by
  intro k hk hk0
  -- impossible: `k < 1` forces `k = 0`, contradicting `0 < k`
  have hk0' : (k : ℕ) = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
  have : False := by
    have : (0 : ℕ) < 0 := by simpa [hk0'] using hk0
    exact (Nat.lt_irrefl 0 this)
  exact this.elim

theorem lovaszQ_after_sizeReduceAllExactWithPrefix_of_lt
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k : Nat) (hk : k < n)
    (B1 : Matrix (Fin n) (Fin n) ℤ)
    (hB1 : B1 = sizeReduceAllExactWithPrefix (n := n) B k hk)
    (i : Fin n) (hi : (i : ℕ) < k) (hi0 : (0 : ℕ) < (i : ℕ)) :
    let im1Nat : ℕ := (i : ℕ) - 1
    have him1 : im1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hi0)) i.2
    let im1 : Fin n := ⟨im1Nat, him1⟩
    lovaszQ (n := n) B1 i im1 δ = lovaszQ (n := n) B i im1 δ := by
  classical
  intro im1Nat him1 im1
  -- unfold B1 as the foldr over `size_reduceZ` updates at row `k`
  let us : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk)
  let k' : Fin n := ⟨k, hk⟩
  let emb : Fin k → Fin n := fun j => ⟨(j : Nat), Nat.lt_trans j.2 hk⟩
  let qfun : Fin k → Matrix (Fin n) (Fin n) ℤ → ℤ :=
    fun j acc =>
      let uj : Fin n → ℚ := us.getD j.val (zeroVecQ (n := n))
      let bk : Fin n → ℚ := rowQ (n := n) acc k'
      roundQ (muQPrefix (n := n) bk uj)
  let js : List (Fin k) := List.ofFn (α := Fin k) (fun j : Fin k => j)
  have hfold :
      B1 =
        js.foldr
          (fun (j : Fin k) acc => size_reduceZ (n := n) acc k' (emb j) (qfun j acc))
          B := by
    -- `hB1` identifies `B1` with the implementation; unfold it
    simp [hB1, sizeReduceAllExactWithPrefix, sizeReduceAllExactWithUs, js, qfun, emb, k', us]
  have hi_ne : i ≠ k' := by
    intro hEq
    have := congrArg Fin.val hEq
    exact (Nat.ne_of_lt hi) this
  have him1_lt_k : (im1 : ℕ) < k := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hi0)) hi
  have him1_ne : im1 ≠ k' := by
    intro hEq
    have := congrArg Fin.val hEq
    exact (Nat.ne_of_lt him1_lt_k) this
  have hrow_i :
      rowQ (n := n) B1 i = rowQ (n := n) B i := by
    have :
        rowQ (n := n)
            (js.foldr (fun (j : Fin k) acc => size_reduceZ (n := n) acc k' (emb j) (qfun j acc)) B) i
          = rowQ (n := n) B i :=
      rowQ_foldr_size_reduceZ_other (n := n) (B := B) (k := k) hk js qfun i (by simpa [k'] using hi_ne)
    simpa [hfold] using this
  have hrow_im1 :
      rowQ (n := n) B1 im1 = rowQ (n := n) B im1 := by
    have :
        rowQ (n := n)
            (js.foldr (fun (j : Fin k) acc => size_reduceZ (n := n) acc k' (emb j) (qfun j acc)) B) im1
          = rowQ (n := n) B im1 :=
      rowQ_foldr_size_reduceZ_other (n := n) (B := B) (k := k) hk js qfun im1 (by simpa [k'] using him1_ne)
    simpa [hfold] using this
  have hgso_i :
      gsoAtQ (n := n) B1 i = gsoAtQ (n := n) B i := by
    have :
        gsoAtQ (n := n)
            (js.foldr (fun (j : Fin k) acc => size_reduceZ (n := n) acc k' (emb j) (qfun j acc)) B) i
          = gsoAtQ (n := n) B i :=
      gsoAtQ_foldr_size_reduceZ_of_lt (n := n) (B := B) (k := k) hk js qfun i (by simpa using hi)
    simpa [hfold] using this
  have hgso_im1 :
      gsoAtQ (n := n) B1 im1 = gsoAtQ (n := n) B im1 := by
    have :
        gsoAtQ (n := n)
            (js.foldr (fun (j : Fin k) acc => size_reduceZ (n := n) acc k' (emb j) (qfun j acc)) B) im1
          = gsoAtQ (n := n) B im1 :=
      gsoAtQ_foldr_size_reduceZ_of_lt (n := n) (B := B) (k := k) hk js qfun im1 (by simpa using him1_lt_k)
    simpa [hfold] using this
  -- unfold `lovaszQ` and rewrite `muQ` + norms using row/gso equalities
  simp [lovaszQ, gsoNormSqQ, muQ, hrow_i, hrow_im1, hgso_i, hgso_im1]

theorem LovaszBelow_after_sizeReduceAllExactWithPrefix
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k : Nat) (hk : k < n)
    (hbelow : LovaszBelow (n := n) B δ k) :
    let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
    LovaszBelow (n := n) B1 δ k := by
  classical
  intro B1
  intro i hi hi0
  have hEq :
      lovaszQ (n := n) B1 i
            (let im1Nat : ℕ := (i : ℕ) - 1
             have him1 : im1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hi0)) i.2
             (⟨im1Nat, him1⟩ : Fin n)) δ
        =
        lovaszQ (n := n) B i
            (let im1Nat : ℕ := (i : ℕ) - 1
             have him1 : im1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hi0)) i.2
             (⟨im1Nat, him1⟩ : Fin n)) δ := by
    simpa [B1] using
      (lovaszQ_after_sizeReduceAllExactWithPrefix_of_lt (n := n) (B := B) (δ := δ) (k := k) hk
        (B1 := B1) rfl i hi hi0)
  -- use the hypothesis on `B`
  have hb : lovaszQ (n := n) B i
        (let im1Nat : ℕ := (i : ℕ) - 1
         have him1 : im1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hi0)) i.2
         (⟨im1Nat, him1⟩ : Fin n)) δ = true := hbelow i hi hi0
  simpa [hEq] using hb

theorem lllRunExactGo_preserves_LovaszBelow
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k steps fuel : Nat)
    (hbelow : LovaszBelow (n := n) B δ k) :
    LovaszBelow (n := n) (lllRunExactGo (n := n) B δ k steps fuel).basis δ
      (lllRunExactGo (n := n) B δ k steps fuel).final_k := by
  induction fuel generalizing B k steps with
  | zero =>
      simpa [lllRunExactGo] using hbelow
  | succ fuel ih =>
      by_cases hk : k < n
      · by_cases h0 : k = 0
        · subst h0
          simpa [lllRunExactGo, hk] using
            (ih (B := B) (k := 1) (steps := steps + 1) (LovaszBelow_one (n := n) B δ))
        · let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
          let km1 : Nat := k - 1
          have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
          let k' : Fin n := ⟨k, hk⟩
          let km1' : Fin n := ⟨km1, hkm1⟩
          have hbelow1 : LovaszBelow (n := n) B1 δ k := by
            simpa [B1] using LovaszBelow_after_sizeReduceAllExactWithPrefix (n := n) (B := B) (δ := δ) (k := k) hk hbelow
          by_cases hL : lovaszQ (n := n) B1 k' km1' δ = true
          · -- extend the invariant to `k+1` using the checked pair at `k`
            have hbelow_succ : LovaszBelow (n := n) B1 δ (k + 1) := by
              intro i hi hi0
              by_cases hik : (i : ℕ) < k
              · exact hbelow1 i hik hi0
              · have hi_eq : (i : ℕ) = k := Nat.eq_of_lt_succ_of_not_lt hi hik
                -- the `i=k` case is exactly the branch check
                have hi_fin : i = k' := by
                  apply Fin.ext
                  simpa [k'] using hi_eq
                subst hi_fin
                -- unfold the `km1` construction and use `hL`
                simpa [k', km1'] using hL
            simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL] using
              (ih (B := B1) (k := k + 1) (steps := steps + 1) hbelow_succ)
          · -- swap: drop to `km1`; indices `< km1` are unaffected by swapping `k` and `km1`
            let B2 := swap_vectors (n := n) B1 k' km1'
            have hkm1_lt_k : (km1' : ℕ) < (k' : ℕ) := by
              have : km1 < k := by simpa [km1] using Nat.pred_lt h0
              simpa [k', km1'] using this
            have hbelow_km1 : LovaszBelow (n := n) B1 δ km1 := by
              have hkm1_le : km1 ≤ k := by simpa [km1] using Nat.pred_le k
              exact LovaszBelow_mono (n := n) (B := B1) (δ := δ) (K := km1) (K' := k) hkm1_le hbelow1
            have hbelow2 : LovaszBelow (n := n) B2 δ km1 := by
              -- for `i < km1`, `gsoAtQ` and `muQ` are prefix-only, so swapping later rows is irrelevant
              intro i hi hi0
              -- unfold the local predecessor construction in the goal
              dsimp
              have hi_lt_km1 : (i : ℕ) < (km1' : ℕ) := by simpa [km1'] using hi
              have hi_lt_k : (i : ℕ) < (k' : ℕ) := Nat.lt_trans hi_lt_km1 hkm1_lt_k
              -- rewrite `lovaszQ` on `B2` back to `B1`
              have him1_lt_km1 : ((i : ℕ) - 1) < (km1' : ℕ) :=
                Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hi0)) hi_lt_km1
              let im1 : Fin n := ⟨(i : ℕ) - 1, Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hi0)) i.2⟩
              have hgi : gsoAtQ (n := n) B2 i = gsoAtQ (n := n) B1 i := by
                -- `i < km1`
                exact gsoAtQ_swap_vectors_of_lt (n := n) (B := B1) (k := k') (j := km1') (t := i) hkm1_lt_k hi_lt_km1
              have hgm1 : gsoAtQ (n := n) B2 im1 = gsoAtQ (n := n) B1 im1 := by
                have him1_lt_km1' : (im1 : ℕ) < (km1' : ℕ) := by simpa [im1, km1'] using him1_lt_km1
                exact gsoAtQ_swap_vectors_of_lt (n := n) (B := B1) (k := k') (j := km1') (t := im1) hkm1_lt_k him1_lt_km1'
              have hrow_i : rowQ (n := n) B2 i = rowQ (n := n) B1 i := by
                -- `i < km1` so `i ≠ k,k-1`
                have hik : i ≠ k' := by
                  intro hEq; exact (Nat.ne_of_lt hi_lt_k) (congrArg Fin.val hEq)
                have hij : i ≠ km1' := by
                  intro hEq; exact (Nat.ne_of_lt hi_lt_km1) (congrArg Fin.val hEq)
                exact rowQ_swap_vectors_other (n := n) (B := B1) (k := k') (j := km1') (i := i) hik hij
              have hrow_im1 : rowQ (n := n) B2 im1 = rowQ (n := n) B1 im1 := by
                have hik : im1 ≠ k' := by
                  intro hEq; exact (Nat.ne_of_lt (Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hi0)) hi_lt_k)) (congrArg Fin.val hEq)
                have hij : im1 ≠ km1' := by
                  intro hEq; exact (Nat.ne_of_lt (Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hi0)) hi_lt_km1)) (congrArg Fin.val hEq)
                exact rowQ_swap_vectors_other (n := n) (B := B1) (k := k') (j := km1') (i := im1) hik hij
              have : lovaszQ (n := n) B2 i im1 δ = lovaszQ (n := n) B1 i im1 δ := by
                simp [lovaszQ, gsoNormSqQ, muQ, hgi, hgm1, hrow_i, hrow_im1]
              have hb : lovaszQ (n := n) B1 i im1 δ = true := by
                simpa [LovaszBelow, im1] using hbelow_km1 i hi hi0
              have hb2 : lovaszQ (n := n) B2 i im1 δ = true := by
                simpa [this] using hb
              simpa [im1] using hb2
            simpa [lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL, B2] using
              (ih (B := B2) (k := km1) (steps := steps + 1) hbelow2)
      · -- finished / fuel-exhausted: no progress, preserve invariant
        simpa [lllRunExactGo, hk] using hbelow

theorem lllRunExact_finished_isLovaszReducedQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (limit : Nat) :
    (lllRunExact (n := n) B δ limit).reason = .finished →
      isLovaszReducedQ (n := n) (lllRunExact (n := n) B δ limit).basis δ = true := by
  intro hfin
  -- get the invariant at final_k and use `final_k ≥ n`
  set r := lllRunExact (n := n) B δ limit
  have hbelow_r : LovaszBelow (n := n) r.basis δ r.final_k := by
    simpa [r, lllRunExact] using
      (lllRunExactGo_preserves_LovaszBelow (n := n) (B := B) (δ := δ) (k := 1) (steps := 0) (fuel := limit)
        (LovaszBelow_one (n := n) B δ))
  have hkn : n ≤ r.final_k := by
    simpa [r, lllRunExact] using
      (lllRunExactGo_finished_final_k_ge_n (n := n) (B := B) (δ := δ) (k := 1) (steps := 0) (fuel := limit) hfin)
  -- convert the bounded invariant into the universal adjacency predicate used by `isLovaszReducedQ_of_forall`
  have hlov :
      ∀ k : Fin n,
        (hk0 : (0 : ℕ) < (k : ℕ)) →
          let km1Nat : ℕ := (k : ℕ) - 1
          have hkm1 : km1Nat < n := Nat.lt_trans (Nat.pred_lt (Nat.ne_of_gt hk0)) k.2
          let km1 : Fin n := ⟨km1Nat, hkm1⟩
          lovaszQ (n := n) r.basis k km1 δ = true := by
    intro k hk0
    have hkK : (k : ℕ) < r.final_k := Nat.lt_of_lt_of_le k.2 hkn
    simpa using hbelow_r k hkK hk0
  have : isLovaszReducedQ (n := n) r.basis δ = true :=
    isLovaszReducedQ_of_forall (n := n) (B := r.basis) (δ := δ) hlov
  simpa [r] using this

theorem lllRunExact_finished_isLLLReducedQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (limit : Nat)
    (hnz_all :
      ∀ (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n),
        ∀ u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk), dotQ (n := n) u u ≠ 0) :
    (lllRunExact (n := n) B δ limit).reason = .finished →
      isLLLReducedQ (n := n) (lllRunExact (n := n) B δ limit).basis δ = true := by
  intro hfin
  set r := lllRunExact (n := n) B δ limit
  have hs : isSizeReducedQ (n := n) r.basis = true := by
    simpa [r] using lllRunExact_finished_isSizeReducedQ (n := n) (B := B) (δ := δ) (limit := limit) hnz_all hfin
  have hl : isLovaszReducedQ (n := n) r.basis δ = true := by
    simpa [r] using lllRunExact_finished_isLovaszReducedQ (n := n) (B := B) (δ := δ) (limit := limit) hfin
  simpa [isLLLReducedQ, r, hs, hl]

/-!
### Relating the instrumented runner to the plain loop (`lllReduceLoopExact`)

This lets us transfer postconditions proven for `lllRunExact` to `lllReduceExact`.
-/

theorem lllReduceLoopExact_eq_lllRunExactGo_basis
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k steps fuel : Nat) :
    lllReduceLoopExact (n := n) B δ k fuel =
      (lllRunExactGo (n := n) B δ k steps fuel).basis := by
  induction fuel generalizing B k steps with
  | zero =>
      simp [lllReduceLoopExact, lllRunExactGo]
  | succ fuel ih =>
      by_cases hk : k < n
      · by_cases h0 : k = 0
        · subst h0
          simpa [lllReduceLoopExact, lllRunExactGo, hk] using
            ih (B := B) (k := 1) (steps := steps + 1)
        · let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
          let km1 : Nat := k - 1
          have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
          let k' : Fin n := ⟨k, hk⟩
          let km1' : Fin n := ⟨km1, hkm1⟩
          by_cases hL : lovaszQ (n := n) B1 k' km1' δ = true
          · simpa [lllReduceLoopExact, lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL] using
              ih (B := B1) (k := k + 1) (steps := steps + 1)
          · let B2 := swap_vectors (n := n) B1 k' km1'
            simpa [lllReduceLoopExact, lllRunExactGo, hk, h0, B1, km1, hkm1, k', km1', hL, B2] using
              ih (B := B2) (k := km1) (steps := steps + 1)
      · -- finished branch: `lllReduceLoopExact` returns `B`
        simp [lllReduceLoopExact, lllRunExactGo, hk]

theorem lllReduceExact_eq_lllRunExact_basis
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (limit : Nat) :
    lllReduceExact (n := n) B δ limit = (lllRunExact (n := n) B δ limit).basis := by
  -- both start at `k=1`, and `steps` does not affect `.basis`
  simpa [lllReduceExact, lllRunExact] using
    (lllReduceLoopExact_eq_lllRunExactGo_basis (n := n) (B := B) (δ := δ) (k := 1) (steps := 0) (fuel := limit))

theorem lllReduceExact_isLLLReducedQ_of_finished
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (limit : Nat)
    (hnz_all :
      ∀ (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n),
        ∀ u ∈ gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk), dotQ (n := n) u u ≠ 0) :
    (lllRunExact (n := n) B δ limit).reason = .finished →
      isLLLReducedQ (n := n) (lllReduceExact (n := n) B δ limit) δ = true := by
  intro hfin
  have hpost : isLLLReducedQ (n := n) (lllRunExact (n := n) B δ limit).basis δ = true :=
    lllRunExact_finished_isLLLReducedQ (n := n) (B := B) (δ := δ) (limit := limit) hnz_all hfin
  simpa [lllReduceExact_eq_lllRunExact_basis (n := n) (B := B) (δ := δ) (limit := limit)] using hpost

/-!
## Deriving nondegeneracy from row linear independence (best-effort)

The size-reduction proof needs that every Gram–Schmidt prefix vector has nonzero `dotQ u u`.
Rather than assuming this ad hoc, we can derive it from **row linear independence over `ℚ`**.

Note: this is a *mathematical* hypothesis (the input is a basis), not a “runtime check”.
-/

def RowLIQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  LinearIndependent ℚ (fun i : Fin n => rowQ (n := n) B i)

def rowSetLtQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) : Set (Fin n → ℚ) :=
  (fun i : Fin n => rowQ (n := n) B i) '' { i : Fin n | (i : ℕ) < k }

lemma rowSetLtQ_mono {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) {k k' : Nat} (hkk' : k ≤ k') :
    rowSetLtQ (n := n) B k ⊆ rowSetLtQ (n := n) B k' := by
  intro v hv
  rcases hv with ⟨i, hi, rfl⟩
  refine ⟨i, ?_, rfl⟩
  exact Nat.lt_of_lt_of_le hi hkk'

lemma gsoVectorForKPrefixFrom_sub_mem_span {n : ℕ} (bk v0 : Fin n → ℚ) (us : List (Fin n → ℚ)) :
    gsoVectorForKPrefixFrom (n := n) bk v0 us - v0 ∈ Submodule.span ℚ { u : Fin n → ℚ | u ∈ us } := by
  classical
  induction us generalizing v0 with
  | nil =>
      simp [gsoVectorForKPrefixFrom]
  | cons u us ih =>
      -- `v1 = v0 - μ•u`
      let v1 : Fin n → ℚ := gsUpdate (n := n) bk v0 u
      have htail :
          gsoVectorForKPrefixFrom (n := n) bk v1 us - v1 ∈ Submodule.span ℚ { w : Fin n → ℚ | w ∈ us } :=
        ih (v0 := v1)
      have htail' :
          gsoVectorForKPrefixFrom (n := n) bk v1 us - v1 ∈ Submodule.span ℚ { w : Fin n → ℚ | w ∈ (u :: us) } := by
        -- monotone span
        refine Submodule.span_mono ?_ htail
        intro w hw
        -- `w ∈ us` implies `w ∈ u :: us`
        exact List.mem_cons_of_mem _ hw
      have hv10 :
          v1 - v0 ∈ Submodule.span ℚ { w : Fin n → ℚ | w ∈ (u :: us) } := by
        -- `v1 - v0 = - μ • u`
        have hu : u ∈ { w : Fin n → ℚ | w ∈ (u :: us) } := by simp
        have : (- (muQPrefix (n := n) bk u)) • u ∈ Submodule.span ℚ { w : Fin n → ℚ | w ∈ (u :: us) } :=
          Submodule.smul_mem _ _ (Submodule.subset_span hu)
        simpa [v1, gsUpdate, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using this
      -- combine: (final - v0) = (final - v1) + (v1 - v0)
      have :
          gsoVectorForKPrefixFrom (n := n) bk v0 (u :: us) - v0 =
            (gsoVectorForKPrefixFrom (n := n) bk v1 us - v1) + (v1 - v0) := by
        simp [gsoVectorForKPrefixFrom, v1, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      -- close under addition
      refine this ▸ (Submodule.add_mem _ htail' hv10)

lemma gsoVectorForKPrefix_eq_zero_imp_mem_span {n : ℕ} (bk : Fin n → ℚ) (us : List (Fin n → ℚ))
    (h0 : gsoVectorForKPrefix (n := n) bk us = 0) :
    bk ∈ Submodule.span ℚ { u : Fin n → ℚ | u ∈ us } := by
  classical
  -- `gsoVectorForKPrefix bk us - bk ∈ span(us)`; if `gso = 0` then `-bk ∈ span(us)`
  have hmem :
      gsoVectorForKPrefixFrom (n := n) bk bk us - bk ∈ Submodule.span ℚ { u : Fin n → ℚ | u ∈ us } :=
    gsoVectorForKPrefixFrom_sub_mem_span (n := n) bk bk us
  have hEq : gsoVectorForKPrefixFrom (n := n) bk bk us = gsoVectorForKPrefix (n := n) bk us := by
    -- definitional: both are `foldl (gsUpdate bk) bk us`
    rfl
  have hneg : (-bk) ∈ Submodule.span ℚ { u : Fin n → ℚ | u ∈ us } := by
    simpa [hEq, h0] using hmem
  simpa using (Submodule.neg_mem _ hneg)

lemma gsoVectorForKPrefixFrom_mem_span_of_mem_span {n : ℕ} (bk v0 : Fin n → ℚ) (us : List (Fin n → ℚ))
    (S : Set (Fin n → ℚ))
    (hv0 : v0 ∈ Submodule.span ℚ S)
    (hus : ∀ u ∈ us, u ∈ Submodule.span ℚ S) :
    gsoVectorForKPrefixFrom (n := n) bk v0 us ∈ Submodule.span ℚ S := by
  classical
  -- `foldl` preserves membership in a submodule
  induction us generalizing v0 with
  | nil =>
      simpa [gsoVectorForKPrefixFrom] using hv0
  | cons u us ih =>
      have hu : u ∈ Submodule.span ℚ S := hus u (by simp)
      have htail : ∀ w ∈ us, w ∈ Submodule.span ℚ S := by
        intro w hw
        exact hus w (by simp [hw])
      -- one update stays in the span
      have hv1 : gsUpdate (n := n) bk v0 u ∈ Submodule.span ℚ S := by
        have hμu : (muQPrefix (n := n) bk u) • u ∈ Submodule.span ℚ S :=
          Submodule.smul_mem _ _ hu
        simpa [gsUpdate, sub_eq_add_neg] using (Submodule.sub_mem _ hv0 hμu)
      -- then fold on the tail
      simpa [gsoVectorForKPrefixFrom, gsoVectorForKPrefixFrom_cons] using
        (ih (v0 := gsUpdate (n := n) bk v0 u) (hv0 := hv1) (hus := htail))

theorem gsoPrefixListQ_mem_span_rowSetLtQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k ≤ n) :
    ∀ u ∈ gsoPrefixListQ (n := n) B k hk, u ∈ Submodule.span ℚ (rowSetLtQ (n := n) B k) := by
  classical
  induction k with
  | zero =>
      intro u hu
      simpa [gsoPrefixListQ] using hu
  | succ k ih =>
      intro u hu
      -- unfold the `succ` decomposition
      rcases gsoPrefixListQ_succ_eq_append (n := n) B k hk with ⟨us, bstar, hEq, hUs, hB⟩
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hus_eq : us = gsoPrefixListQ (n := n) B k hk' := hUs
      have hbstar_eq :
          bstar = gsoVectorForKPrefix (n := n) (rowQ (n := n) B ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩) us := hB
      have hus : ∀ w ∈ us, w ∈ Submodule.span ℚ (rowSetLtQ (n := n) B k) := by
        intro w hw
        -- rewrite `us` to the recursive prefix list and apply IH
        have : w ∈ gsoPrefixListQ (n := n) B k hk' := by simpa [hus_eq] using hw
        exact ih (hk := hk') w this
      have hus_succ : ∀ w ∈ us, w ∈ Submodule.span ℚ (rowSetLtQ (n := n) B (k + 1)) := by
        intro w hw
        have : w ∈ Submodule.span ℚ (rowSetLtQ (n := n) B k) := hus w hw
        exact Submodule.span_mono (rowSetLtQ_mono (n := n) (B := B) (k := k) (k' := k + 1) (Nat.le_succ k)) this
      -- membership split: in `us` or equals `bstar`
      have hu' : u ∈ us ∨ u = bstar := by
        -- `gsoPrefixListQ ... (k+1) = us ++ [bstar]`
        have : u ∈ us ++ [bstar] := by simpa [hEq] using hu
        simpa using (List.mem_append.1 this)
      cases hu' with
      | inl hu_us =>
          exact hus_succ u hu_us
      | inr hu_eq =>
          -- replace `u` by `bstar` but keep `bstar` in scope
          subst u
          -- show the new `bstar` lies in the span of rows `< k+1`
          have hklt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
          let i' : Fin n := ⟨k, hklt⟩
          have hbki : rowQ (n := n) B i' ∈ Submodule.span ℚ (rowSetLtQ (n := n) B (k + 1)) := by
            refine Submodule.subset_span ?_
            refine ⟨i', ?_, rfl⟩
            simpa [i'] using (Nat.lt_succ_self k)
          have hbstar :
              gsoVectorForKPrefixFrom (n := n) (rowQ (n := n) B i') (rowQ (n := n) B i') us ∈
                Submodule.span ℚ (rowSetLtQ (n := n) B (k + 1)) :=
            gsoVectorForKPrefixFrom_mem_span_of_mem_span (n := n) (bk := rowQ (n := n) B i') (v0 := rowQ (n := n) B i')
              (us := us) (S := rowSetLtQ (n := n) B (k + 1)) hbki hus_succ
          -- relate the `bstar` witness to our chosen `i'`
          have hbstar' :
              bstar =
                gsoVectorForKPrefix (n := n) (rowQ (n := n) B i') us := by
            -- `hbstar_eq` uses the same `i'` by definition
            simpa [i'] using hbstar_eq
          -- now finish
          simpa [hbstar', gsoVectorForKPrefix, gsoVectorForKPrefixFrom] using hbstar

lemma dotQ_self_eq_zero_iff {n : ℕ} (v : Fin n → ℚ) : dotQ (n := n) v v = 0 ↔ v = 0 := by
  classical
  constructor
  · intro h
    funext i
    have hterms :
        ∀ j : Fin n, v j * v j = 0 := by
      -- all summands are nonnegative (as squares), so sum=0 forces each=0
      have :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (mul_self_nonneg (v j)))).1 (by simpa [dotQ] using h)
      intro j
      exact this j (by simp)
    have : v i * v i = 0 := hterms i
    simpa using (mul_self_eq_zero.1 this)
  · intro h
    simpa [h, dotQ]

lemma dotQ_self_ne_zero_of_ne_zero {n : ℕ} (v : Fin n → ℚ) (hv : v ≠ 0) : dotQ (n := n) v v ≠ 0 := by
  intro h
  have : v = 0 := (dotQ_self_eq_zero_iff (n := n) v).1 h
  exact hv this

theorem HNZAt_of_RowLIQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n)
    (hli : RowLIQ (n := n) B) :
    HNZAt (n := n) B k hk := by
  classical
  -- prove by induction that each GS prefix vector is nonzero
  let v : Fin n → (Fin n → ℚ) := fun i => rowQ (n := n) B i
  have hv : LinearIndependent ℚ v := hli
  intro u hu
  -- show `u ≠ 0` by induction on `k` via the concrete construction
  have hk0 : k ≤ n := Nat.le_of_lt hk
  -- `u` lies in the prefix list, so it is some `getD` element; use a structural induction on `k`.
  -- We'll use the stronger statement: all elements in `gsoPrefixListQ B k` are nonzero.
  have hnonzero :
      ∀ (k : Nat) (hk : k ≤ n),
        (∀ w ∈ gsoPrefixListQ (n := n) B k hk, w ≠ 0) := by
    intro k hk
    induction k with
    | zero =>
        intro w hw
        simpa [gsoPrefixListQ] using hw
    | succ k ih =>
        intro w hw
        rcases gsoPrefixListQ_succ_eq_append (n := n) B k hk with ⟨us, bstar, hEq, hUs, hB⟩
        have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
        have hus_eq : us = gsoPrefixListQ (n := n) B k hk' := hUs
        have hbstar_eq :
            bstar = gsoVectorForKPrefix (n := n) (rowQ (n := n) B ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩) us := hB
        have hmem : w ∈ us ∨ w = bstar := by
          have : w ∈ us ++ [bstar] := by simpa [hEq] using hw
          simpa using (List.mem_append.1 this)
        cases hmem with
        | inl hw_us =>
            have : w ∈ gsoPrefixListQ (n := n) B k hk' := by simpa [hus_eq] using hw_us
            exact ih (hk := hk') w this
        | inr hw_eq =>
            subst w
            -- show `bstar ≠ 0` using linear independence: if it were zero, the new row is in the span of previous rows
            have hklt : k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk
            let i' : Fin n := ⟨k, hklt⟩
            have hspan_us :
                Submodule.span ℚ { a : Fin n → ℚ | a ∈ us } ≤
                  Submodule.span ℚ (rowSetLtQ (n := n) B k) := by
              -- each `a ∈ us` is in the span of rows `< k`
              refine Submodule.span_le.2 ?_
              intro a ha
              -- `a ∈ us` implies `a ∈ gsoPrefixListQ B k`
              have ha' : a ∈ gsoPrefixListQ (n := n) B k hk' := by
                simpa [hus_eq] using ha
              exact gsoPrefixListQ_mem_span_rowSetLtQ (n := n) (B := B) (k := k) hk' a ha'
            have hnot :
                v i' ∉ Submodule.span ℚ (v '' { i : Fin n | (i : ℕ) < k }) := by
              -- `i'` is not in `{i | i<k}`
              have : i' ∉ ({ i : Fin n | (i : ℕ) < k } : Set (Fin n)) := by
                simp [i']
              simpa [v, rowSetLtQ] using (hv.notMem_span_image (s := { i : Fin n | (i : ℕ) < k }) this)
            intro hb0
            have hbmem : v i' ∈ Submodule.span ℚ { a : Fin n → ℚ | a ∈ us } := by
              -- `bstar = gsoVectorForKPrefix (rowQ B i') us`
              have hb : gsoVectorForKPrefix (n := n) (v i') us = 0 := by
                -- rewrite `bstar` to the canonical `gsoVectorForKPrefix ... us`
                have hbstar' : bstar = gsoVectorForKPrefix (n := n) (rowQ (n := n) B i') us := by
                  simpa [i'] using hbstar_eq
                simpa [hbstar', v, i'] using hb0
              exact gsoVectorForKPrefix_eq_zero_imp_mem_span (n := n) (bk := v i') (us := us) hb
            have : v i' ∈ Submodule.span ℚ (v '' { i : Fin n | (i : ℕ) < k }) :=
              (hspan_us hbmem)
            exact hnot this
  have hu0 : u ≠ 0 := hnonzero k hk0 u hu
  exact dotQ_self_ne_zero_of_ne_zero (n := n) u hu0

/-!
### Row linear independence invariance under LLL row operations

These are the “group action” facts we need to replace `hnz_*` by a clean basis hypothesis:
elementary row operations and row swaps preserve linear independence of the row family over `ℚ`.
-/

theorem RowLIQ_swap_vectors {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n)
    (hli : RowLIQ (n := n) B) :
    RowLIQ (n := n) (swap_vectors (n := n) B k j) := by
  classical
  -- `swap_vectors` is precomposition by an equivalence on indices.
  -- `LinearIndependent` is stable under composition with an injective map.
  simpa [RowLIQ, swap_vectors, Function.comp] using
    (LinearIndependent.comp (R := ℚ) (v := fun i : Fin n => rowQ (n := n) B i) hli
      (fun i : Fin n => Equiv.swap k j i) (Equiv.swap k j).injective)

theorem RowLIQ_size_reduceZ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) (q : ℤ)
    (hkj : k ≠ j) (hli : RowLIQ (n := n) B) :
    RowLIQ (n := n) (size_reduceZ (n := n) B k j q) := by
  classical
  -- Switch to the ℚ matrix view and use determinant invariance under “add multiple of another row”.
  let BQ : Matrix (Fin n) (Fin n) ℚ := B.map (fun z : ℤ => (z : ℚ))
  let BQ' : Matrix (Fin n) (Fin n) ℚ :=
    BQ.updateRow k (BQ k + (-(q : ℚ)) • BQ j)

  have hliQ : LinearIndependent ℚ BQ.row := by
    simpa [RowLIQ, BQ, rowQ, Matrix.row] using hli

  have hdet : BQ.det ≠ 0 := by
    -- over a field: linear independent rows ↔ matrix is a unit ↔ det is a unit ↔ det ≠ 0
    have hUnit : IsUnit BQ := (Matrix.linearIndependent_rows_iff_isUnit (A := BQ)).1 (by
      simpa [Matrix.row] using hliQ)
    have hDetUnit : IsUnit BQ.det := (Matrix.isUnit_iff_isUnit_det (A := BQ)).1 hUnit
    exact hDetUnit.ne_zero

  have hdet' : BQ'.det ≠ 0 := by
    have hdet_eq : BQ'.det = BQ.det := by
      simpa [BQ'] using
        (Matrix.det_updateRow_add_smul_self (A := BQ) (i := k) (j := j) (c := (-(q : ℚ))) hkj)
    simpa [hdet_eq] using hdet

  have hliQ' : LinearIndependent ℚ BQ'.row := by
    -- use the det ≠ 0 criterion for row linear independence
    have : LinearIndependent ℚ (fun i : Fin n => BQ' i) :=
      Matrix.linearIndependent_rows_of_det_ne_zero (R := ℚ) (A := BQ') hdet'
    simpa [Matrix.row] using this

  have hBQ' :
      BQ' = (size_reduceZ (n := n) B k j q).map (fun z : ℤ => (z : ℚ)) := by
    ext i t
    by_cases hik : i = k
    · subst hik
      simp [BQ', BQ, size_reduceZ, Matrix.updateRow_self, rowQ, Pi.add_apply, Pi.smul_apply,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    · simp [BQ', BQ, size_reduceZ, Matrix.updateRow_ne, hik]

  simpa [RowLIQ, BQ', hBQ', rowQ, Matrix.row] using hliQ'

theorem RowLIQ_sizeReduceAllExactWithUs {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n)
    (us : List (Fin n → ℚ)) (hli : RowLIQ (n := n) B) :
    RowLIQ (n := n) (sizeReduceAllExactWithUs (n := n) B k hk us) := by
  classical
  -- `sizeReduceAllExactWithUs` is a foldr of `size_reduceZ` operations on a fixed row `k'`.
  unfold sizeReduceAllExactWithUs
  -- now do induction on `js`
  let k' : Fin n := ⟨k, hk⟩
  let js : List (Fin k) := List.ofFn (α := Fin k) (fun j : Fin k => j)
  -- rewrite the goal in terms of `js.foldr`
  -- (Lean unfolds the `let`s above; keep them stable by rewriting with the locals we introduced)
  change RowLIQ (n := n)
      ((js).foldr
        (fun (j : Fin k) acc =>
          let j' : Fin n := ⟨(j : Nat), Nat.lt_trans j.2 hk⟩
          let uj : Fin n → ℚ := us.getD j.val (zeroVecQ (n := n))
          let bk : Fin n → ℚ := rowQ (n := n) acc k'
          let μ : ℚ := muQPrefix (n := n) bk uj
          let q : ℤ := roundQ μ
          size_reduceZ acc k' j' q)
        B)
  -- list recursion on `js`
  revert B
  induction js with
  | nil =>
      intro B hliB
      simpa using hliB
  | cons j js ih =>
      intro B hliB
      -- first fold tail, then apply one `size_reduceZ`
      have hli_tail :
          RowLIQ (n := n)
            (js.foldr
              (fun (j : Fin k) acc =>
                let j' : Fin n := ⟨(j : Nat), Nat.lt_trans j.2 hk⟩
                let uj : Fin n → ℚ := us.getD j.val (zeroVecQ (n := n))
                let bk : Fin n → ℚ := rowQ (n := n) acc k'
                let μ : ℚ := muQPrefix (n := n) bk uj
                let q : ℤ := roundQ μ
                size_reduceZ acc k' j' q)
              B) := ih B hliB
      -- show `k' ≠ j'`
      have hkj' : k' ≠ (⟨(j : Nat), Nat.lt_trans j.2 hk⟩ : Fin n) := by
        intro hEq
        have hval : k = (j : Nat) := congrArg Fin.val hEq
        have hkneq : k ≠ (j : Nat) := Nat.ne_of_gt j.2
        exact hkneq hval
      -- finish by applying `RowLIQ_size_reduceZ`
      -- (the `let`s are harmless; we just `simp` them away)
      simpa using
        (RowLIQ_size_reduceZ (n := n)
          (B := js.foldr
            (fun (j : Fin k) acc =>
              let j' : Fin n := ⟨(j : Nat), Nat.lt_trans j.2 hk⟩
              let uj : Fin n → ℚ := us.getD j.val (zeroVecQ (n := n))
              let bk : Fin n → ℚ := rowQ (n := n) acc k'
              let μ : ℚ := muQPrefix (n := n) bk uj
              let q : ℤ := roundQ μ
              size_reduceZ acc k' j' q)
            B)
          (k := k')
          (j := ⟨(j : Nat), Nat.lt_trans j.2 hk⟩)
          (q := roundQ (muQPrefix (n := n)
            (rowQ (n := n)
              (js.foldr
                (fun (j : Fin k) acc =>
                  let j' : Fin n := ⟨(j : Nat), Nat.lt_trans j.2 hk⟩
                  let uj : Fin n → ℚ := us.getD j.val (zeroVecQ (n := n))
                  let bk : Fin n → ℚ := rowQ (n := n) acc k'
                  let μ : ℚ := muQPrefix (n := n) bk uj
                  let q : ℤ := roundQ μ
                  size_reduceZ acc k' j' q)
                B)
              k')
            (us.getD j.val (zeroVecQ (n := n)))))
          hkj' hli_tail)

theorem RowLIQ_sizeReduceAllExactWithPrefix {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : Nat) (hk : k < n)
    (hli : RowLIQ (n := n) B) :
    RowLIQ (n := n) (sizeReduceAllExactWithPrefix (n := n) B k hk) := by
  classical
  unfold sizeReduceAllExactWithPrefix
  exact RowLIQ_sizeReduceAllExactWithUs (n := n) (B := B) (k := k) (hk := hk)
    (us := gsoPrefixListQ (n := n) B k (Nat.le_of_lt hk)) hli

theorem HNZAlongRun_of_RowLIQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k steps fuel : Nat)
    (hli : RowLIQ (n := n) B) :
    HNZAlongRun (n := n) B δ k steps fuel := by
  classical
  induction fuel generalizing B k steps with
  | zero =>
      simp [HNZAlongRun]
  | succ fuel ih =>
      by_cases hk : k < n
      · by_cases h0 : k = 0
        · simp [HNZAlongRun, hk, h0, ih (B := B) (k := 1) (steps := steps + 1) hli]
        · have hnz_here : HNZAt (n := n) B k hk :=
            HNZAt_of_RowLIQ (n := n) (B := B) (k := k) hk hli
          let B1 := sizeReduceAllExactWithPrefix (n := n) B k hk
          have hli1 : RowLIQ (n := n) B1 :=
            RowLIQ_sizeReduceAllExactWithPrefix (n := n) (B := B) (k := k) (hk := hk) hli
          let km1 : ℕ := k - 1
          have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
          let k' : Fin n := ⟨k, hk⟩
          let km1' : Fin n := ⟨km1, hkm1⟩
          by_cases hlov : lovaszQ (n := n) B1 k' km1' δ
          · -- no swap
            simp [HNZAlongRun, hk, h0, hnz_here, B1, km1, hkm1, k', km1', hlov,
              ih (B := B1) (k := k + 1) (steps := steps + 1) hli1]
          · -- swap
            let B2 := swap_vectors (n := n) B1 k' km1'
            have hli2 : RowLIQ (n := n) B2 := RowLIQ_swap_vectors (n := n) (B := B1) (k := k') (j := km1') hli1
            simp [HNZAlongRun, hk, h0, hnz_here, B1, km1, hkm1, k', km1', hlov, B2,
              ih (B := B2) (k := km1) (steps := steps + 1) hli2]
      · simp [HNZAlongRun, hk]

theorem lllRunExact_finished_isLLLReducedQ_of_RowLIQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (limit : Nat)
    (hli : RowLIQ (n := n) B) :
    (lllRunExact (n := n) B δ limit).reason = .finished →
      isLLLReducedQ (n := n) (lllRunExact (n := n) B δ limit).basis δ = true := by
  intro hfin
  set r := lllRunExact (n := n) B δ limit
  have hnz_run : HNZAlongRun (n := n) B δ 1 0 limit :=
    HNZAlongRun_of_RowLIQ (n := n) (B := B) (δ := δ) (k := 1) (steps := 0) (fuel := limit) hli
  have hs : isSizeReducedQ (n := n) r.basis = true := by
    simpa [r] using
      lllRunExact_finished_isSizeReducedQ_of_hnzRun (n := n) (B := B) (δ := δ) (limit := limit) hnz_run hfin
  have hl : isLovaszReducedQ (n := n) r.basis δ = true := by
    simpa [r] using lllRunExact_finished_isLovaszReducedQ (n := n) (B := B) (δ := δ) (limit := limit) hfin
  simpa [isLLLReducedQ, r, hs, hl]

theorem dotQ_row_gsoAtQ_eq_normSq {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n)
    (hnz : ∀ u ∈ gsoPrefixListQ (n := n) B (j.1 + 1) (Nat.succ_le_of_lt j.2), dotQ (n := n) u u ≠ 0) :
    dotQ (n := n) (rowQ (n := n) B j) (gsoAtQ (n := n) B j) =
      dotQ (n := n) (gsoAtQ (n := n) B j) (gsoAtQ (n := n) B j) := by
  -- rewrite `gsoAtQ` to the explicit GS vector and apply `dotQ_row_prefix_eq_normSq`
  simp [gsoAtQ_eq_gsoVectorForKPrefix (n := n) (B := B) j] at *
  simpa using
    (dotQ_row_prefix_eq_normSq (n := n) (B := B) (j := j.1) (hj := j.2) (hnz := hnz))

/-!
### One-step size reduction (semantic `muQ` bound)

One `sizeReduceExact` update makes the coefficient `(k,j)` size-reduced, assuming the Gram–Schmidt
construction at index `j` is nondegenerate (so the GS identity holds and `denom ≠ 0`).

This is the reusable “local postcondition” that will feed the full `k`-loop postcondition.
-/

theorem sizeReduceExact_sizeReducedMuQ
    {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n)
    (hjk : (j : ℕ) < (k : ℕ))
    (hnz : ∀ u ∈ gsoPrefixListQ (n := n) B (j.1 + 1) (Nat.succ_le_of_lt j.2), dotQ (n := n) u u ≠ 0) :
    sizeReducedMuQ (n := n) (sizeReduceExact (n := n) B k j) k j = true := by
  classical
  -- Identify `gsoAtQ B j` with the “explicit” GS vector built from the `j`-prefix list.
  let us0 : List (Fin n → ℚ) := gsoPrefixListQ (n := n) B j.1 (Nat.le_of_lt j.2)
  let ujGS : Fin n → ℚ := gsoVectorForKPrefix (n := n) (rowQ (n := n) B j) us0
  have hprefix :
      gsoPrefixListQ (n := n) B (j.1 + 1) (Nat.succ_le_of_lt j.2) = us0 ++ [ujGS] := by
    rcases gsoPrefixListQ_succ_eq_append (n := n) B j.1 (Nat.succ_le_of_lt j.2) with ⟨us, bstar, hEq, hUs, hB⟩
    -- rewrite the existential witnesses to our chosen names
    subst hUs
    subst hB
    simpa [us0, ujGS] using hEq
  have huj : gsoAtQ (n := n) B j = ujGS := by
    -- `gsoAtQ` is `getD j` from the `(j+1)`-prefix list
    have hus0_len : us0.length = j.1 := by
      simpa [us0] using gsoPrefixListQ_length (n := n) B j.1 (Nat.le_of_lt j.2)
    -- in `us0 ++ [ujGS]`, index `j` is in the right part
    have hlen_le : us0.length ≤ j.1 := by simp [hus0_len]
    -- `getD_append_right` reduces `getD j` to the singleton tail
    have : (us0 ++ [ujGS]).getD j.1 (zeroVecQ (n := n)) = ujGS := by
      -- `getD_append_right` reduces to the singleton tail, then `j - length us0 = 0`
      simpa [hus0_len] using
        (List.getD_append_right (l := us0) (l' := [ujGS]) (d := (zeroVecQ (n := n))) (n := j.1) hlen_le)
    -- now unfold `gsoAtQ` and rewrite the prefix list via `hprefix`
    calc
      gsoAtQ (n := n) B j =
          (gsoPrefixListQ (n := n) B (j.1 + 1) (Nat.succ_le_of_lt j.2)).getD j.1 (zeroVecQ (n := n)) := by
            simp [gsoAtQ]
      _ = (us0 ++ [ujGS]).getD j.1 (zeroVecQ (n := n)) := by
            simp [hprefix]
      _ = ujGS := this
  have huj_mem : ujGS ∈ gsoPrefixListQ (n := n) B (j.1 + 1) (Nat.succ_le_of_lt j.2) := by
    -- `ujGS` is the last element of the `(j+1)`-prefix list
    have : ujGS ∈ us0 ++ [ujGS] := by simp
    simpa [hprefix] using this
  have hden : dotQ (n := n) ujGS ujGS ≠ 0 := hnz ujGS huj_mem
  have hgs : dotQ (n := n) (rowQ (n := n) B j) ujGS = dotQ (n := n) ujGS ujGS := by
    -- this is exactly `dotQ_row_prefix_eq_normSq`
    simpa [us0, ujGS] using
      (dotQ_row_prefix_eq_normSq (n := n) (B := B) (j := j.1) (hj := j.2) (hnz := hnz))
  -- use `uj := gsoAtQ B j` for the update, but rewrite to `ujGS`
  let uj : Fin n → ℚ := gsoAtQ (n := n) B j
  have huj' : uj = ujGS := by simpa [uj] using huj
  have hden' : dotQ (n := n) uj uj ≠ 0 := by simpa [huj'] using hden
  have hgs' : dotQ (n := n) (rowQ (n := n) B j) uj = dotQ (n := n) uj uj := by
    simpa [huj'] using hgs
  let μ : ℚ := muQPrefix (n := n) (rowQ (n := n) B k) uj
  let q : ℤ := roundQ μ
  let B' : Matrix (Fin n) (Fin n) ℤ := size_reduceZ (n := n) B k j q
  have hμ_small : |muQPrefix (n := n) (rowQ (n := n) B' k) uj| ≤ (1 / 2 : ℚ) := by
    simpa [μ, q, B'] using
      (abs_muQPrefix_after_size_reduceZ_le_half (n := n) (B := B) (k := k) (j := j) (uj := uj) hden' hgs')
  have hgso_stable : gsoAtQ (n := n) B' j = uj := by
    simpa [B', uj] using
      (gsoAtQ_size_reduceZ_of_lt (n := n) (B := B) (k := k) (j := j) (t := j) (q := q) hjk)
  have hmuQ' : muQ (n := n) B' k j = muQPrefix (n := n) (rowQ (n := n) B' k) uj := by
    simp [muQ, hgso_stable, muQPrefix, hden']
  have habs : |muQ (n := n) B' k j| ≤ (1 / 2 : ℚ) := by
    simpa [hmuQ'] using hμ_small
  have hmuQ0 : muQ (n := n) B k j = μ := by
    -- unfold `muQ` and rewrite `gsoAtQ B j` to `ujGS`
    simp [muQ, muQPrefix, uj, μ, huj', hden]
  have hB' : sizeReduceExact (n := n) B k j = B' := by
    simp [sizeReduceExact, hmuQ0, μ, q, B']
  -- final boolean check
  have : |muQ (n := n) (sizeReduceExact (n := n) B k j) k j| ≤ (1 / 2 : ℚ) := by
    simpa [hB'] using habs
  simpa [sizeReducedMuQ, this]

end GeometryOfNumbers.Computable

