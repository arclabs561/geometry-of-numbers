import Mathlib.Data.Rat.Floor
import Mathlib.Tactic
import GeometryOfNumbers.Computable.LLLCore

namespace GeometryOfNumbers.Computable

/-!
## Exact (computable) LLL over ℤ using ℚ Gram–Schmidt

This module provides an **executable** (computable) LLL loop:

- the basis is an integer matrix `Matrix (Fin n) (Fin n) ℤ` (rows are basis vectors)
- Gram–Schmidt coefficients are computed exactly in `ℚ`
- nearest-integer rounding uses `⌊μ + 1/2⌋ : ℤ` on rationals (computable)

This is the “hard way” in the sense that we avoid floating / noncomputable reals and make it usable
from `lean_exe` entrypoints.

Correctness caveat (honesty): if the input rows are not linearly independent (so some GS vector has
zero squared norm), the algorithm uses a conservative `μ = 0` fallback for that degenerate branch.
-/

def dotQ {n : ℕ} (v w : Fin n → ℚ) : ℚ :=
  ∑ i, v i * w i

def zeroVecQ {n : ℕ} : Fin n → ℚ := fun _ => 0

def rowQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Fin n → ℚ :=
  fun j => (B i j : ℚ)

def roundQ (x : ℚ) : ℤ :=
  ⌊x + (1 / 2 : ℚ)⌋

def gsoListQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : List (Fin n → ℚ) :=
  let idxs : List (Fin n) := List.ofFn (fun i : Fin n => i)
  let accRev : List (Fin n → ℚ) :=
    idxs.foldl
      (fun accRev i =>
        let bi := rowQ B i
        let bstar :=
          accRev.foldl
            (fun v u =>
              let denom := dotQ u u
              let μ : ℚ := if denom = 0 then 0 else dotQ bi u / denom
              v - μ • u)
            bi
        bstar :: accRev)
      []
  accRev.reverse

def gsoAtQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) : Fin n → ℚ :=
  (gsoListQ (n := n) B).getD j.val (zeroVecQ (n := n))

def muQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i j : Fin n) : ℚ :=
  let bi := rowQ B i
  let uj := gsoAtQ (n := n) B j
  let denom := dotQ uj uj
  if denom = 0 then 0 else dotQ bi uj / denom

def gsoNormSqQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℚ :=
  let ui := gsoAtQ (n := n) B i
  dotQ ui ui

def lovaszQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k km1 : Fin n) (δ : ℚ) : Bool :=
  let lhs : ℚ := gsoNormSqQ (n := n) B k
  let rhs : ℚ := (δ - (muQ (n := n) B k km1) ^ 2) * gsoNormSqQ (n := n) B km1
  decide (lhs ≥ rhs)

def sizeReduceExact {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  let μ := muQ (n := n) B k j
  let q : ℤ := roundQ μ
  size_reduceZ B k j q

def sizeReduceAllExact {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k < n) :
    Matrix (Fin n) (Fin n) ℤ :=
  let js : List (Fin k) := List.ofFn (fun j : Fin k => j)
  js.foldl
    (fun acc (j : Fin k) =>
      have hj : (j : ℕ) < n := Nat.lt_trans j.2 hk
      sizeReduceExact (n := n) acc ⟨k, hk⟩ ⟨(j : ℕ), hj⟩)
    B

def lllReduceLoopExact {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (k : ℕ) (limit : ℕ) :
    Matrix (Fin n) (Fin n) ℤ :=
  match limit with
  | 0 => B
  | limit' + 1 =>
      if hk : k < n then
        if h0 : k = 0 then
          lllReduceLoopExact (n := n) B δ 1 limit'
        else
          let B1 := sizeReduceAllExact (n := n) B k hk
          let km1 : ℕ := k - 1
          have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
          let k' : Fin n := ⟨k, hk⟩
          let km1' : Fin n := ⟨km1, hkm1⟩
          if lovaszQ (n := n) B1 k' km1' δ then
            lllReduceLoopExact (n := n) B1 δ (k + 1) limit'
          else
            let B2 := swap_vectors (n := n) B1 k' km1'
            lllReduceLoopExact (n := n) B2 δ km1 limit'
      else
        B

def lllReduceExact {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (limit : ℕ := 200000) :
    Matrix (Fin n) (Fin n) ℤ :=
  lllReduceLoopExact (n := n) B δ 1 limit

theorem rowSpan_sizeReduceExact {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k j : Fin n) (hkj : k ≠ j) :
    rowSpan (sizeReduceExact (n := n) B k j) = rowSpan B := by
  let μ := muQ (n := n) B k j
  let q : ℤ := roundQ μ
  simpa [sizeReduceExact, μ, q] using rowSpan_size_reduceZ (B := B) (k := k) (j := j) hkj q

theorem rowSpan_sizeReduceAllExact {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (hk : k < n) :
    rowSpan (sizeReduceAllExact (n := n) B k hk) = rowSpan B := by
  classical
  -- unfold and induct over the explicit list of indices `0..k-1`
  unfold sizeReduceAllExact
  set js : List (Fin k) := List.ofFn (fun j : Fin k => j)
  revert B
  induction js with
  | nil =>
      intro B
      simp
  | cons a tl ih =>
      intro B
      have ha_lt : (a : ℕ) < k := a.2
      have hj : (a : ℕ) < n := Nat.lt_trans ha_lt hk
      have hkj : (⟨k, hk⟩ : Fin n) ≠ ⟨(a : ℕ), hj⟩ := by
        intro h
        exact (Nat.ne_of_gt ha_lt) (congrArg Fin.val h)
      have hstep :
          rowSpan (sizeReduceExact (n := n) B ⟨k, hk⟩ ⟨(a : ℕ), hj⟩) = rowSpan B :=
        rowSpan_sizeReduceExact (n := n) (B := B) (k := ⟨k, hk⟩) (j := ⟨(a : ℕ), hj⟩) hkj
      have htail :=
        ih (B := sizeReduceExact (n := n) B ⟨k, hk⟩ ⟨(a : ℕ), hj⟩)
      simpa [js, List.foldl, hstep] using htail

theorem rowSpan_lllReduceExact {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (δ : ℚ) (limit : ℕ) :
    rowSpan (lllReduceExact (n := n) B δ limit) = rowSpan B := by
  -- Follows because the exact loop uses only `size_reduceZ` and `swap_vectors`.
  -- (We keep this proof minimal; the existing `LLL.lean` has the more detailed induction pattern.)
  classical
  -- prove the loop variant; then specialize
  have hloop :
      ∀ (B : Matrix (Fin n) (Fin n) ℤ) (k : ℕ) (limit : ℕ),
        rowSpan (lllReduceLoopExact (n := n) B δ k limit) = rowSpan B := by
    intro B k limit
    induction limit generalizing B k with
    | zero =>
        simp [lllReduceLoopExact]
    | succ limit ih =>
        by_cases hk : k < n
        · by_cases h0 : k = 0
          · cases h0
            have := ih (B := B) (k := 1)
            have hk0 : (0 : ℕ) < n := hk
            simpa [lllReduceLoopExact, hk0] using this
          · let B1 := sizeReduceAllExact (n := n) B k hk
            have hB1 : rowSpan B1 = rowSpan B := by
              simpa [B1] using rowSpan_sizeReduceAllExact (n := n) (B := B) (k := k) hk
            let km1 : ℕ := k - 1
            have hkm1 : km1 < n := Nat.lt_trans (Nat.pred_lt h0) hk
            let k' : Fin n := ⟨k, hk⟩
            let km1' : Fin n := ⟨km1, hkm1⟩
            by_cases hL : lovaszQ (n := n) B1 k' km1' δ = true
            · have := ih (B := B1) (k := k + 1)
              simpa [lllReduceLoopExact, hk, h0, B1, km1, hkm1, k', km1', hL, hB1] using this
            · let B2 := swap_vectors (n := n) B1 k' km1'
              have hB2 : rowSpan B2 = rowSpan B1 := by
                simpa [B2] using rowSpan_swap_vectors (n := n) (B := B1) k' km1'
              have ih2 := ih (B := B2) (k := km1)
              calc
                rowSpan (lllReduceLoopExact (n := n) B δ k (limit + 1)) =
                    rowSpan (lllReduceLoopExact (n := n) B2 δ km1 limit) := by
                      simp [lllReduceLoopExact, hk, h0, B1, km1, k', km1', hL, B2]
                _ = rowSpan B2 := by
                      simpa using ih2
                _ = rowSpan B1 := by
                      simp [hB2]
                _ = rowSpan B := by
                      simp [hB1]
        · simp [lllReduceLoopExact, hk]
  simpa [lllReduceExact] using hloop B 1 limit

end GeometryOfNumbers.Computable
