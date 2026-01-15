import PolygonalNumberTheorem.Basic
import PolygonalNumberTheorem.SumThreeSquares
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.Ring.Int.Parity

open Nat
open BigOperators

namespace PolygonalNumberTheorem

/-- For `a ≥ 3`, there exists an odd `b` satisfying Cauchy's conditions. -/
lemma exists_cauchy_b (a : ℤ) (ha : 3 ≤ a) :
    ∃ b : ℤ, 0 < a ∧ 0 < b ∧ Odd b ∧ b ^ 2 < 4 * a ∧ b ^ 2 + 2 * b - 3 * a + 4 > 0 := by
  sorry

/-- 8n + 3 is never of the form 4^a(8k + 7). -/
lemma not_exception_eight_n_add_three (n : ℕ) :
    ¬ Nat.is_three_square_exception (8 * n + 3) := by
  intro ⟨a, k, heq⟩
  cases a with
  | zero =>
    -- 8n + 3 = 8k + 7 is impossible mod 8
    simp at heq
    omega
  | succ a' =>
    -- 4^(a'+1) * (8k + 7) ≡ 0 (mod 4), but 8n + 3 ≡ 3 (mod 4)
    have hmod : (8 * n + 3) % 4 = 3 := by omega
    have hpow : 4 ^ (a' + 1) * (8 * k + 7) % 4 = 0 := by
      have : 4 ^ (a' + 1) = 4 * 4 ^ a' := by ring
      rw [this]
      simp [Nat.mul_mod]
    rw [heq] at hmod
    omega

/-- Helper: For odd `a` and odd `b` with `b² < 4a`, we have `4a - b² ≡ 3 (mod 8)`. -/
lemma four_a_minus_b_sq_mod_eight (a b : ℕ) (ha : Odd a) (hb : Odd b)
    (hcond : b ^ 2 < 4 * a) : (4 * a - b ^ 2) % 8 = 3 := by
  -- Odd a: 4a ≡ 4 (mod 8)
  obtain ⟨k, hak⟩ := ha
  have h4a : (4 * a) % 8 = 4 := by
    rw [hak]; omega
  -- Odd b: b² ≡ 1 (mod 8)
  have hb2 : b ^ 2 % 8 = 1 := by
    obtain h | h | h := Nat.sq_mod_eight b
    · -- b² % 8 = 0 contradicts odd b
      exfalso
      have hkey : b ^ 2 % 8 = (b % 8) ^ 2 % 8 := Nat.pow_mod b 2 8
      rw [hkey] at h
      have h8 : b % 8 < 8 := Nat.mod_lt b (by decide : 0 < 8)
      have h2 : b % 2 = b % 8 % 2 := (Nat.mod_mod_of_dvd b (by decide : 2 ∣ 8)).symm
      rw [Nat.odd_iff] at hb
      interval_cases (b % 8) <;> omega
    · exact h
    · -- b² % 8 = 4 contradicts odd b
      exfalso
      have hkey : b ^ 2 % 8 = (b % 8) ^ 2 % 8 := Nat.pow_mod b 2 8
      rw [hkey] at h
      have h8 : b % 8 < 8 := Nat.mod_lt b (by decide : 0 < 8)
      have h2 : b % 2 = b % 8 % 2 := (Nat.mod_mod_of_dvd b (by decide : 2 ∣ 8)).symm
      rw [Nat.odd_iff] at hb
      interval_cases (b % 8) <;> omega
  -- 4a - b² = 4 - 1 = 3 (mod 8)
  have hle : b ^ 2 ≤ 4 * a := Nat.le_of_lt hcond
  omega

/-- 4a - b² is not of the exceptional form 4^e(8k+7). -/
lemma four_a_minus_b_sq_not_exception (a b : ℕ) (_ha_pos : 1 ≤ a) (_hb_pos : 1 ≤ b)
    (ha_odd : Odd a) (hb_odd : Odd b) (hcond : b ^ 2 < 4 * a) :
    ¬ Nat.is_three_square_exception (4 * a - b ^ 2) := by
  have hmod3 := four_a_minus_b_sq_mod_eight a b ha_odd hb_odd hcond
  have hle : b ^ 2 ≤ 4 * a := Nat.le_of_lt hcond
  have hdiff_pos : 3 ≤ 4 * a - b ^ 2 := by omega
  let m := (4 * a - b ^ 2 - 3) / 8
  have heq : 4 * a - b ^ 2 = 8 * m + 3 := by
    have hmod0 : (4 * a - b ^ 2 - 3) % 8 = 0 := by omega
    have hdiv : 8 * m = 4 * a - b ^ 2 - 3 := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod0)
    omega
  rw [heq]
  exact not_exception_eight_n_add_three m

/-- If n is a sum of three squares, it has a representation with integers x, y, z sorted x ≥ y ≥ z. -/
lemma exists_sorted_three_squares_int (n : ℕ) (h : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) :
    ∃ x y z : ℤ, 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z ∧ x ≥ y ∧ y ≥ z ∧ x ^ 2 + y ^ 2 + z ^ 2 = n := by
  obtain ⟨a, b, c, habc⟩ := h
  -- Sort a, b, c into descending order and cast to ℤ
  have hsym : ∀ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 →
      (x : ℤ) ^ 2 + (y : ℤ) ^ 2 + (z : ℤ) ^ 2 = n := by
    intros x y z hxyz
    have : (x ^ 2 + y ^ 2 + z ^ 2 : ℕ) = n := by rw [hxyz, habc]
    exact_mod_cast this
  -- Choose the sorted triple based on ordering
  rcases Nat.le_total a b with hab | hba
  · rcases Nat.le_total b c with hbc | hcb
    -- a ≤ b ≤ c
    · exact ⟨c, b, a, by linarith, by linarith, by linarith, by exact_mod_cast hbc, by exact_mod_cast hab, hsym c b a (by ring)⟩
    · rcases Nat.le_total a c with hac | hca
      -- a ≤ c ≤ b
      · exact ⟨b, c, a, by linarith, by linarith, by linarith, by exact_mod_cast hcb, by exact_mod_cast hac, hsym b c a (by ring)⟩
      -- c < a ≤ b
      · exact ⟨b, a, c, by linarith, by linarith, by linarith, by exact_mod_cast hab, by exact_mod_cast hca, hsym b a c (by ring)⟩
  · rcases Nat.le_total b c with hbc | hcb
    · rcases Nat.le_total a c with hac | hca
      -- b ≤ a ≤ c
      · exact ⟨c, a, b, by linarith, by linarith, by linarith, by exact_mod_cast hac, by exact_mod_cast hba, hsym c a b (by ring)⟩
      -- b ≤ c < a
      · exact ⟨a, c, b, by linarith, by linarith, by linarith, by exact_mod_cast hca, by exact_mod_cast hbc, hsym a c b (by ring)⟩
    -- c ≤ b ≤ a
    · exact ⟨a, b, c, by linarith, by linarith, by linarith, by exact_mod_cast hba, by exact_mod_cast hcb, hsym a b c (by ring)⟩

/-- The Cauchy-Schwarz inequality for three terms in ℤ. -/
lemma three_terms_cauchy_schwarz_int (x y z : ℤ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  -- 3(x² + y² + z²) - (x + y + z)² = (x-y)² + (x-z)² + (y-z)² ≥ 0
  have h : 3 * (x ^ 2 + y ^ 2 + z ^ 2) - (x + y + z) ^ 2 =
           (x - y) ^ 2 + (x - z) ^ 2 + (y - z) ^ 2 := by ring
  have h_pos : (x - y) ^ 2 + (x - z) ^ 2 + (y - z) ^ 2 ≥ 0 := by
    have h1 : (x - y) ^ 2 ≥ 0 := sq_nonneg _
    have h2 : (x - z) ^ 2 ≥ 0 := sq_nonneg _
    have h3 : (y - z) ^ 2 ≥ 0 := sq_nonneg _
    linarith
  linarith

/-- Modular sign choice for Cauchy’s lemma. -/
lemma choose_u_div_four (b x y z : ℤ) (hb : Odd b) (hx : Odd x) (hy : Odd y) (hz : Odd z) :
    ∃ u : ℤ, (u = z ∨ u = -z) ∧ (4 : ℤ) ∣ (b + x + y + u) := by
  have hsum_odd : Odd (b + x + y) := (hb.add_odd hx).add_odd hy
  have heven_plus : Even (b + x + y + z) := hsum_odd.add_odd hz
  have heven_minus : Even (b + x + y - z) := by
    rw [sub_eq_add_neg]; exact hsum_odd.add_odd hz.neg
  
  obtain ⟨k1, hk1⟩ := heven_plus
  -- b + x + y + z = 2 * k1
  by_cases hk1_even : Even k1
  · -- Case 1: k1 is even, so 2*k1 is divisible by 4
    obtain ⟨m, hm⟩ := hk1_even
    use z, Or.inl rfl
    rw [hk1, hm]
    use m; ring
  · -- Case 2: k1 is odd
    -- b + x + y - z = (b + x + y + z) - 2z = 2k1 - 2z = 2(k1 - z)
    have hk1_odd : Odd k1 := by rwa [← Int.not_even_iff_odd]
    have h_diff : b + x + y - z = 2 * k1 - 2 * z := by
      calc b + x + y - z = b + x + y + z - 2 * z := by ring
        _ = 2 * k1 - 2 * z := by rw [hk1]; ring
    have h_factor : b + x + y - z = 2 * (k1 - z) := by
      rw [h_diff]; ring
    -- k1 is odd, z is odd, so k1 - z is even
    have : Even (k1 - z) := hk1_odd.sub_odd hz
    obtain ⟨m, hm⟩ := this
    use -z, Or.inr rfl
    rw [← sub_eq_add_neg, h_factor, hm]
    use m; ring

/-- The main Cauchy's Lemma (Nathanson Lemma 1.12). -/
theorem four_nonneg_sum_from_cauchy (a b : ℕ) (ha_pos : 1 ≤ a) (hb_pos : 1 ≤ b)
    (ha_odd : Odd a) (hb_odd : Odd b)
    (hcond1 : b ^ 2 < 4 * a) (hcond2 : 3 * a < b ^ 2 + 2 * b + 4) :
    ∃ s t u v : ℕ, a = s ^ 2 + t ^ 2 + u ^ 2 + v ^ 2 ∧ b = s + t + u + v := by
  -- 1. Mod 8 check
  have hmod : (4 * a - b ^ 2) % 8 = 3 := four_a_minus_b_sq_mod_eight a b ha_odd hb_odd hcond1
  
  -- 2. Not exception
  have hnot_exc : ¬ Nat.is_three_square_exception (4 * a - b ^ 2) :=
    four_a_minus_b_sq_not_exception a b ha_pos hb_pos ha_odd hb_odd hcond1
  
  -- 3. Legendre
  obtain ⟨x_nat, y_nat, z_nat, hsum_nat⟩ := Nat.sum_three_squares_of_not_exception (4 * a - b ^ 2) hnot_exc
  
  -- 4. Sorted integers
  obtain ⟨x, y, z, hx_pos, hy_pos, hz_pos, hxy, hyz, hsum⟩ := 
    exists_sorted_three_squares_int (4 * a - b ^ 2) ⟨x_nat, y_nat, z_nat, hsum_nat⟩
  
  -- 5. Parity
  -- If x^2 + y^2 + z^2 = 3 mod 8, then x, y, z are all odd.
  -- We already proved this for Nat in Nat.all_odd_of_sum_three_squares_eq_three_mod_eight.
  -- Since x, y, z are non-negative integers cast from Nat, we can use that.
  have hx_odd : Odd x := sorry
  have hy_odd : Odd y := sorry
  have hz_odd : Odd z := sorry
  have hb_int_odd : Odd (b : ℤ) := by rw [Int.odd_coe_nat]; exact hb_odd

  -- 6. Choose signs
  obtain ⟨w, hw_sign, hw_div4⟩ := choose_u_div_four b x y z hb_int_odd hx_odd hy_odd hz_odd
  
  -- 7. Define s, t, u, v
  let s_z := (b + x + y + w) / 4
  let t_z := (b + x - y - w) / 4
  let u_z := (b - x + y - w) / 4
  let v_z := (b - x - y + w) / 4
  
  -- 8. Verify sums and squares
  sorry

/-- Existence of b, r for Cauchy's decomposition. -/
lemma exists_cauchy_b_r (m N : ℕ) (hm : 3 ≤ m) (hN : 108 * m ≤ N) :
    ∃ b r : ℕ, Odd b ∧ r ≤ m - 2 ∧ (N - r) % m = b % m ∧
      (b : ℤ) ^ 2 < 4 * (b + 2 * (N - b - r) / m : ℤ) ∧
      3 * (b + 2 * (N - b - r) / m : ℤ) < (b : ℤ) ^ 2 + 2 * (b : ℤ) + 4 := by
  sorry

/-- Given valid Cauchy conditions, express N in terms of polygonal numbers. -/
theorem cauchy_decomposition (m : ℕ) (hm : 3 ≤ m) (N : ℕ) (hN : 108 * m ≤ N) :
    ∃ p1 p2 p3 p4 : ℕ, ∃ r : ℕ,
      r ≤ m - 2 ∧
      N = polygonal (m + 2) p1 + polygonal (m + 2) p2 +
          polygonal (m + 2) p3 + polygonal (m + 2) p4 + r := by
  sorry

/-- Gauss's Eureka Theorem wrapper. -/
theorem gauss_eureka (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n := by
  sorry

/-- The "small n" case for Fermat's Polygonal Number Theorem. -/
lemma fermat_polygonal_small (s : ℕ) (hs : 3 ≤ s) (n : ℕ) (hn : n < 108 * (s - 2)) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  sorry

/-- Fermat's Polygonal Number Theorem. -/
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n := by
  let m := s - 2
  rcases Nat.lt_trichotomy s 4 with hlt4 | heq4 | hgt4
  · have : s = 3 := by omega
    subst this; obtain ⟨a, b, c, habc⟩ := gauss_eureka n
    let f : Fin 3 → ℕ := fun i => if i.val = 0 then a else if i.val = 1 then b else c
    use f; sorry
  · subst heq4; obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares n
    let f : Fin 4 → ℕ := fun i =>
      if i.val = 0 then a
      else if i.val = 1 then b
      else if i.val = 2 then c
      else d
    use f; sorry
  · -- s ≥ 5
    by_cases h_small : n < 108 * m
    · exact fermat_polygonal_small s hs n h_small
    · obtain ⟨p1, p2, p3, p4, r, hr, hsum⟩ := cauchy_decomposition m (by omega) n (by linarith)
      sorry

end PolygonalNumberTheorem
