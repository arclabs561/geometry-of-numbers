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

end GeometryOfNumbers.Computable

