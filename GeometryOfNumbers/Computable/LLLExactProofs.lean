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

end GeometryOfNumbers.Computable

