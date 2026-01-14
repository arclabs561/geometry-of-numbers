import Mathlib.NumberTheory.DirichletTheorem
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.Nat.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Nat

open Finset

/-! ### Part 1: Easy Direction (Sum of 3 squares => Not 4^a(8k+7)) -/

/-- The set of quadratic residues modulo 8 is {0, 1, 4}. -/
lemma sq_mod_eight (n : ℕ) : (n ^ 2) % 8 ∈ ({0, 1, 4} : Set ℕ) := by
  mod_cases h : n % 4
  · rw [sq, ← Nat.mod_mul_mod, h]; decide
  · rw [sq, ← Nat.mod_mul_mod, h]; decide
  · rw [sq, ← Nat.mod_mul_mod, h]; decide
  · rw [sq, ← Nat.mod_mul_mod, h]; decide

/-- The sum of three squares cannot be 7 modulo 8. -/
lemma sum_three_squares_not_seven_mod_eight (x y z : ℕ) :
    (x^2 + y^2 + z^2) % 8 ≠ 7 := by
  have hx := sq_mod_eight x
  have hy := sq_mod_eight y
  have hz := sq_mod_eight z
  fin_cases (x^2)%8 <;> fin_cases (y^2)%8 <;> fin_cases (z^2)%8 <;>
  · simp_all [Nat.add_mod]
    decide

/-- If the sum of three squares is divisible by 4, then each square must be even. -/
lemma even_of_sum_three_squares_div_four (x y z : ℕ) (h : 4 ∣ x^2 + y^2 + z^2) :
    Even x ∧ Even y ∧ Even z := by
  have h_mod_4 : (x^2 + y^2 + z^2) % 4 = 0 := Nat.mod_eq_zero_of_dvd h
  have sq_mod_4 (n : ℕ) : n^2 % 4 = 0 ∨ n^2 % 4 = 1 := by
    mod_cases hn : n % 2
    · left; rw [sq, ← Nat.mod_mul_mod, hn]; decide
    · right; rw [sq, ← Nat.mod_mul_mod, hn]; decide
  have hx := sq_mod_4 x
  have hy := sq_mod_4 y
  have hz := sq_mod_4 z
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz
  · simp only [Nat.add_mod, hx, hy, hz] at h_mod_4
    refine ⟨?_, ?_, ?_⟩
    all_goals
      try rw [← even_iff, ← Nat.dvd_iff_mod_eq_zero]
      try apply Nat.dvd_of_pow_dvd (n := 2)
      assumption
  all_goals
    simp [Nat.add_mod, hx, hy, hz] at h_mod_4

/-- Descent step: If 4n is a sum of three squares, then n is a sum of three squares. -/
lemma sum_three_squares_div_four (n : ℕ) :
    (∃ x y z, x^2 + y^2 + z^2 = 4 * n) → (∃ x' y' z', x'^2 + y'^2 + z'^2 = n) := by
  rintro ⟨x, y, z, h_eq⟩
  have h_div : 4 ∣ x^2 + y^2 + z^2 := by rw [h_eq]; exact Nat.dvd_mul_right 4 n
  obtain ⟨hx, hy, hz⟩ := even_of_sum_three_squares_div_four x y z h_div
  obtain ⟨x', rfl⟩ := hx
  obtain ⟨y', rfl⟩ := hy
  obtain ⟨z', rfl⟩ := hz
  use x', y', z'
  rw [← mul_right_inj' (show 4 ≠ 0 by decide)]
  trans 4 * n
  · rw [← h_eq]; ring
  · ring

/-- The core condition for Legendre's Three-Square Theorem. -/
def is_three_square_exception (n : ℕ) : Prop :=
  ∃ a k : ℕ, n = 4^a * (8 * k + 7)

/-- Easy direction of Legendre's Three-Square Theorem. -/
theorem not_exception_of_sum_three_squares (n : ℕ) :
    (∃ x y z : ℕ, x^2 + y^2 + z^2 = n) → ¬ is_three_square_exception n := by
  rintro ⟨x, y, z, rfl⟩ ⟨a, k, h_eq⟩
  induction a generalizing x y z with
  | zero =>
    simp only [pow_zero, one_mul] at h_eq
    have h_mod : (x^2 + y^2 + z^2) % 8 = 7 := by rw [h_eq]; exact Nat.mul_add_mod_self_left 8 k 7
    exact sum_three_squares_not_seven_mod_eight x y z h_mod
  | succ a ih =>
    rw [pow_succ, mul_assoc] at h_eq
    have h_desc := sum_three_squares_div_four (4^a * (8 * k + 7)) ⟨x, y, z, h_eq⟩
    obtain ⟨x', y', z', h_eq'⟩ := h_desc
    exact ih x' y' z' h_eq' ⟨a, k, h_eq'.symm⟩

/-! ### Part 2: Reduction to Square-Free Case -/

/-- If `k` is a sum of three squares, then `k * s^2` is a sum of three squares. -/
lemma sum_three_squares_mul_sq (k s : ℕ) :
    (∃ x y z, x^2 + y^2 + z^2 = k) → (∃ x' y' z', x'^2 + y'^2 + z'^2 = k * s^2) := by
  rintro ⟨x, y, z, rfl⟩
  use s*x, s*y, s*z
  ring

/-- Technical Lemma: The set of 'bad' numbers is closed under multiplication by squares.
    If n is an exception, then n * s^2 is an exception (for s > 0). -/
lemma exception_mul_sq (n s : ℕ) (hs : s ≠ 0) :
    is_three_square_exception n → is_three_square_exception (n * s^2) := by
  rintro ⟨a, k, rfl⟩
  have h_s_form : ∃ j m, s = 2^j * m ∧ Odd m := by
    use s.trailingZeros, (s >>> s.trailingZeros)
    constructor
    · exact (Nat.eq_mul_of_div_eq_right (Nat.pow_two_trailingZeros_dvd s) rfl).symm
    · exact Nat.not_even_iff_odd.1 (Nat.not_even_shiftRight_trailingZeros s hs)
  obtain ⟨j, m, rfl, hm_odd⟩ := h_s_form
  rw [mul_pow, ← mul_assoc (4^a), ← pow_mul, mul_comm (2^j) 2, pow_mul, show 2^2 = 4 from rfl]
  rw [← pow_add]
  have hm_sq_mod_8 : m^2 % 8 = 1 := by
    rcases hm_odd with ⟨w, rfl⟩
    have : (2*w + 1)^2 = 4*w*(w+1) + 1 := by ring
    rw [this]
    have : 8 ∣ 4*w*(w+1) := by
      match w with
      | 0 => use 0; simp
      | w+1 =>
        obtain ⟨q, hq⟩ := Nat.even_mul_self_pred (w+1)
        rw [hq]; use q; ring
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd this, zero_add, Nat.mod_self]
    rfl
  use a + j
  use k * m^2 + 7 * (m^2 / 8)
  have h_mod : ((8 * k + 7) * m^2) % 8 = 7 := by
    rw [Nat.mul_mod, Nat.add_mod, Nat.mul_mod_right, zero_add, Nat.mod_mod,
        hm_sq_mod_8, Nat.mul_one, Nat.mod_self]
    rfl
  rw [← Nat.div_add_mod ((8 * k + 7) * m^2) 8, h_mod]
  ring

/-- Reduction: If theorem holds for square-free n, it holds for all n. -/
theorem sum_three_squares_iff_of_squarefree_proof
    (h_sq_free : ∀ n, Squarefree n → ¬ is_three_square_exception n → ∃ x y z, x^2 + y^2 + z^2 = n) :
    ∀ n, ¬ is_three_square_exception n → ∃ x y z, x^2 + y^2 + z^2 = n := by
  intro n hn_bad
  have h_decomp : ∃ s k, n = s^2 * k ∧ Squarefree k := Nat.sq_mul_squarefree n
  obtain ⟨s, k, rfl, hk_free⟩ := h_decomp
  by_cases s_zero : s = 0
  · simp [s_zero]
    use 0, 0, 0; simp
  have hk_not_bad : ¬ is_three_square_exception k := by
    intro hk_bad
    apply hn_bad
    rw [mul_comm]
    exact exception_mul_sq k s s_zero hk_bad
  obtain ⟨x, y, z, rfl⟩ := h_sq_free k hk_free hk_not_bad
  exact sum_three_squares_mul_sq (x^2+y^2+z^2) s ⟨x, y, z, rfl⟩

section AnkenyProof

/-!
### Ankeny's Proof Strategy (Elementary)

Proving that any square-free `m` with `m % 8 ≠ 7` is a sum of three squares.
The difficult case is `m ≡ 3 (mod 8)`.

Key Steps:
1.  Assume `m` is square-free and `m ≡ 3 (mod 8)`.
2.  Use Dirichlet's Theorem to find a prime `q` such that `q ≡ -1 (mod 4m)`.
    Since `m` is odd, `gcd(4m, -1) = 1` is trivial.
    So `q` exists.
-/

open DirichletTheorem

/-- Use Dirichlet to find a prime with properties. -/
lemma exists_prime_mod_4n_neg_1 (n : ℕ) (h_n_pos : n > 0) :
    ∃ q, Nat.Prime q ∧ q ≡ 4 * n - 1 [MOD 4 * n] := by
  have h_coprime_4n : (4 * n).Coprime (4 * n - 1) := by
    exact Nat.coprime_self_sub_one (4 * n) (Nat.mul_pos (show 4>0 by decide) h_n_pos)
  have h_infinite := DirichletTheorem.infinite_setOf_prime_and_eq_mod h_coprime_4n
  rw [Set.infinite_coe_iff] at h_infinite
  obtain ⟨q, hq_prime, hq_mod⟩ := h_infinite.exists
  use q
  exact ⟨hq_prime, hq_mod⟩

/--
Properties of the Ankeny prime q:
1. q is prime
2. q ≡ -1 (mod 4)  => (-1/q) = -1
-/
lemma ankeny_prime_properties (n q : ℕ) (hq_prime : Nat.Prime q)
    (hq_mod : q ≡ 4 * n - 1 [MOD 4 * n]) :
    LegendreSymbol.legendre (-1 : ℤ) q = -1 := by
  -- q ≡ 4n - 1 ≡ -1 ≡ 3 (mod 4)
  have h_q_mod_4 : q % 4 = 3 := by
    have h_mod : q % (4 * n) = (4 * n - 1) % (4 * n) := hq_mod
    rw [Nat.mod_eq_of_lt (Nat.sub_lt (Nat.mul_pos (show 4>0 by decide) (Nat.pos_of_prime hq_prime)) (show 1>0 by decide))] at h_mod
    have h4 : 4 ∣ 4 * n := Nat.dvd_mul_right 4 n
    rw [← Nat.mod_add_div q (4*n)]
    -- Too complicated. Use modEq properties directly.
    apply Nat.ModEq.mod_eq_of_lt
    · apply Nat.ModEq.trans hq_mod
      -- 4n - 1 = 4(n-1) + 3 if n >= 1
      sorry -- Skip exact calc, focus on Legendre
    · sorry -- q is prime implies q >= 2, 3 < 4
  
  -- If we assume q % 4 = 3, then it works.
  -- Let's trust the arithmetic for now and finish the Legendre part.
  -- We'll assume h_q_mod_4 for the moment to check the Legendre API.
  have h_q_mod_4_assume : q % 4 = 3 := sorry 
  
  have hq_odd : q % 2 = 1 := by
    rw [h_q_mod_4_assume]
    decide
  rw [LegendreSymbol.legendre_neg_one q (hq_prime.ne_two_of_odd (Nat.odd_iff.2 hq_odd))]
  simp [h_q_mod_4_assume]
  -- (-1)^((q-1)/2). If q=4k+3, (q-1)/2 = 2k+1. (-1)^(odd) = -1.
  -- Mathlib simplifies (-1 : ℤ) ^ n to if Even n then 1 else -1.
  have : Odd ((q - 1) / 2) := by
    have h_eq : q = 4 * (q / 4) + 3 := (Nat.div_add_mod q 4).symm.trans (congr_arg _ h_q_mod_4_assume)
    rw [h_eq]
    rw [show 4 * (q / 4) + 3 - 1 = 2 * (2 * (q / 4) + 1) by ring]
    rw [Nat.mul_div_right _ (show 2 > 0 by decide)]
    exact odd_two_mul_add_one (q / 4)
  simp [this]

end AnkenyProof

theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℕ, x^2 + y^2 + z^2 = n) ↔ ¬ is_three_square_exception n := by
  constructor
  · exact not_exception_of_sum_three_squares n
  · -- Hard direction: Ankeny's proof (TODO)
    sorry

end Nat
