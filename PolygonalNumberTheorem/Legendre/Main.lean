import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic
import Mathlib.NumberTheory.SumFourSquares
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Prime.Basic
import PolygonalNumberTheorem.Legendre.Exceptions

namespace Nat

/-! ## Legendre's Three-Square Theorem (work in progress) -/

lemma sq_mod_eight (n : ℕ) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  have hkey : n ^ 2 % 8 = (n % 8) ^ 2 % 8 := Nat.pow_mod n 2 8
  rw [hkey]
  have h : n % 8 < 8 := Nat.mod_lt n (by decide : 0 < 8)
  interval_cases (n % 8) <;> decide

lemma sum_three_squares_not_seven_mod_eight (x y z : ℕ) : (x ^ 2 + y ^ 2 + z ^ 2) % 8 ≠ 7 := by
  obtain h1 | h1 | h1 := sq_mod_eight x
  all_goals obtain h2 | h2 | h2 := sq_mod_eight y
  all_goals obtain h3 | h3 | h3 := sq_mod_eight z
  all_goals omega

lemma odd_of_sq_mod_eight_eq_one (n : ℕ) (h : n ^ 2 % 8 = 1) : Odd n := by
  rw [Nat.odd_iff]
  have hkey : n ^ 2 % 8 = (n % 8) ^ 2 % 8 := Nat.pow_mod n 2 8
  rw [hkey] at h
  have h8 : n % 8 < 8 := Nat.mod_lt n (by decide : 0 < 8)
  have h2 : n % 2 = n % 8 % 2 := (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).symm
  interval_cases (n % 8) <;> simp_all

lemma all_odd_of_sum_three_squares_eq_three_mod_eight (x y z : ℕ)
    (h : (x ^ 2 + y ^ 2 + z ^ 2) % 8 = 3) : Odd x ∧ Odd y ∧ Odd z := by
  obtain h1 | h1 | h1 := sq_mod_eight x
  all_goals obtain h2 | h2 | h2 := sq_mod_eight y
  all_goals obtain h3 | h3 | h3 := sq_mod_eight z
  all_goals try omega
  exact ⟨odd_of_sq_mod_eight_eq_one x h1, odd_of_sq_mod_eight_eq_one y h2, odd_of_sq_mod_eight_eq_one z h3⟩

lemma sq_mod_four (n : ℕ) : n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  have hkey : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := Nat.pow_mod n 2 4
  rw [hkey]
  have h : n % 4 < 4 := Nat.mod_lt n (by decide : 0 < 4)
  interval_cases (n % 4) <;> decide

lemma even_of_sq_mod_four_eq_zero (n : ℕ) (h : n ^ 2 % 4 = 0) : 2 ∣ n := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have hkey : n ^ 2 % 4 = (n % 4) ^ 2 % 4 := Nat.pow_mod n 2 4
  rw [hkey] at h
  have h4 : n % 4 < 4 := Nat.mod_lt n (by decide : 0 < 4)
  have h2 : n % 2 = n % 4 % 2 := (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 4)).symm
  interval_cases (n % 4) <;> simp_all

lemma sum_three_squares_zero_mod_four_implies_all_even (x y z : ℕ)
    (h : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0) :
    2 ∣ x ∧ 2 ∣ y ∧ 2 ∣ z := by
  obtain h1 | h1 := sq_mod_four x
  all_goals obtain h2 | h2 := sq_mod_four y
  all_goals obtain h3 | h3 := sq_mod_four z
  all_goals try omega
  exact ⟨even_of_sq_mod_four_eq_zero x h1, even_of_sq_mod_four_eq_zero y h2, even_of_sq_mod_four_eq_zero z h3⟩

lemma sum_three_squares_div_four (m x y z : ℕ) (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 * m) :
    ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = m := by
  have hmod : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0 := by rw [h]; simp
  obtain ⟨hx, hy, hz⟩ := sum_three_squares_zero_mod_four_implies_all_even x y z hmod
  obtain ⟨x', hx'⟩ := hx
  obtain ⟨y', hy'⟩ := hy
  obtain ⟨z', hz'⟩ := hz
  use x', y', z'
  have : (2 * x') ^ 2 + (2 * y') ^ 2 + (2 * z') ^ 2 = 4 * m := by rw [← hx', ← hy', ← hz']; exact h
  linarith [sq_nonneg x', sq_nonneg y', sq_nonneg z']

theorem not_exception_of_sum_three_squares (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) → ¬ is_three_square_exception n := by
  intro h
  rintro ⟨a, k, rfl⟩
  induction a with
  | zero =>
    rcases h with ⟨x, y, z, hsum⟩
    have h8 : (8 * k + 7) % 8 = 7 := by simp [Nat.add_mod]
    have : (x ^ 2 + y ^ 2 + z ^ 2) % 8 = 7 := by simp [hsum, h8]
    exact sum_three_squares_not_seven_mod_eight x y z this
  | succ a ih =>
    rcases h with ⟨x, y, z, hsum⟩
    have h4 : x ^ 2 + y ^ 2 + z ^ 2 = 4 * (4 ^ a * (8 * k + 7)) := by
      simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hsum
    rcases sum_three_squares_div_four (m := 4 ^ a * (8 * k + 7)) (x := x) (y := y) (z := z) h4 with
      ⟨x', y', z', hsum'⟩
    exact ih ⟨x', y', z', hsum'⟩

lemma sum_three_squares_mul_sq (m k : ℕ) (h : ∃ x y z, x^2 + y^2 + z^2 = m) :
    ∃ x y z, x^2 + y^2 + z^2 = k^2 * m := by
  obtain ⟨x, y, z, hxyz⟩ := h
  use k * x, k * y, k * z
  calc (k * x) ^ 2 + (k * y) ^ 2 + (k * z) ^ 2
      = k ^ 2 * x ^ 2 + k ^ 2 * y ^ 2 + k ^ 2 * z ^ 2 := by ring
    _ = k ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by ring
    _ = k ^ 2 * m := by rw [hxyz]

lemma sq_mod_eight_odd (n : ℕ) (h : Odd n) : n ^ 2 % 8 = 1 := by
  rcases h with ⟨k, rfl⟩
  -- (2k+1)^2 = 4*k*(k+1) + 1, and k*(k+1) is even, so the 4*k*(k+1) term is a multiple of 8.
  have h_even : Even (k * (k + 1)) := by
    exact Nat.even_mul_succ_self k
  rcases h_even with ⟨t, ht⟩
  have ht2 : k * (k + 1) = 2 * t := by
    -- `Even` gives `k*(k+1)=t+t`, rewrite into `2*t`.
    simpa [two_mul] using ht
  -- Rewrite the square into the `8 * t + 1` shape.
  have hs : (2 * k + 1) ^ 2 = 8 * t + 1 := by
    -- Expand and use `k*(k+1) = 2*t`.
    -- (2k+1)^2 = 4k^2 + 4k + 1 = 4*k*(k+1) + 1 = 8*t + 1.
    calc
      (2 * k + 1) ^ 2 = (2 * k) ^ 2 + 2 * (2 * k) * 1 + 1 ^ 2 := by
        ring
      _ = 4 * k ^ 2 + 4 * k + 1 := by
        ring
      _ = 4 * (k ^ 2 + k) + 1 := by ring
      _ = 4 * (k * (k + 1)) + 1 := by ring
      _ = 4 * (2 * t) + 1 := by simpa [ht2]
      _ = 8 * t + 1 := by ring
  -- Now reduce mod 8.
  have : (8 * t + 1) % 8 = 1 := by simp
  simpa [hs] using this

lemma is_three_square_exception_mul_odd_sq (m : ℕ) {k : ℕ} (hk : Odd k) :
    is_three_square_exception (k^2 * m) ↔ is_three_square_exception m := by
  constructor
  · rintro ⟨a, t, hkm⟩
    -- Show `4^a ∣ m` (since `k^2` is odd and doesn't contribute any `2`s).
    have hk2_odd : Odd (k ^ 2) := (Odd.pow (n := 2) hk)
    have hcop : Nat.Coprime (4 ^ a) (k ^ 2) := by
      -- `4^a` is a power of 2; any odd number is coprime to it.
      -- Use `Odd.coprime_two_right` + powering on the left.
      have h2 : (k ^ 2).Coprime 2 := hk2_odd.coprime_two_right
      -- Turn it into `Coprime (2^(2a)) (k^2)` via commutativity + pow.
      have h2' : (2 : ℕ).Coprime (k ^ 2) := by simpa [Nat.coprime_comm] using h2
      have hp : (2 ^ (2 * a)).Coprime (k ^ 2) := h2'.pow_left (2 * a)
      -- Rewrite `2^(2a)` as `4^a`.
      simpa [pow_mul, show 2 ^ 2 = 4 by decide] using hp
    have h4a_dvd_km : 4 ^ a ∣ k ^ 2 * m := by
      -- From `k^2 * m = 4^a * (8*t+7)`.
      rw [hkm]
      exact dvd_mul_of_dvd_left (dvd_refl (4 ^ a)) _
    have h4a_dvd_m : 4 ^ a ∣ m := by
      exact hcop.dvd_of_dvd_mul_left h4a_dvd_km
    obtain ⟨m', hm'⟩ := h4a_dvd_m
    -- Reduce to showing `m' % 8 = 7`.
    have h_eq : k ^ 2 * m' = 8 * t + 7 := by
      -- Cancel the common factor `4^a`.
      -- From `k^2 * (4^a * m') = 4^a * (8*t+7)` derive `k^2*m' = 8*t+7`.
      -- Use rewriting and `Nat.mul_left_cancel` (needs positivity of `4^a`).
      have hpos : 0 < 4 ^ a := pow_pos (by decide : 0 < 4) a
      -- Rewrite `hkm` using `hm'`.
      have : k ^ 2 * (4 ^ a * m') = 4 ^ a * (8 * t + 7) := by
        simpa [hm', Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hkm
      -- Cancel the `4^a` factor.
      -- `k^2 * (4^a * m') = 4^a * (k^2 * m')`.
      -- Use associativity/commutativity normalization, then cancel.
      have : 4 ^ a * (k ^ 2 * m') = 4 ^ a * (8 * t + 7) := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
      exact Nat.mul_left_cancel hpos this
    have hk2_mod8 : (k ^ 2) % 8 = 1 := sq_mod_eight_odd k hk
    have hm'_mod8 : m' % 8 = 7 := by
      -- Take `h_eq` mod 8.
      have : (k ^ 2 * m') % 8 = (8 * t + 7) % 8 := by simpa [h_eq]
      -- Simplify both sides and use `k^2 % 8 = 1`.
      -- LHS = (k^2 % 8) * (m' % 8) % 8.
      -- RHS = 7.
      have : ((k ^ 2 % 8) * (m' % 8)) % 8 = 7 := by
        simpa [Nat.mul_mod, Nat.add_mod, Nat.mod_mod, Nat.mul_assoc] using this
      -- Replace `k^2 % 8` with `1`.
      have : (m' % 8) % 8 = 7 := by
        -- `1 * (m'%8) % 8 = 7`.
        simpa [hk2_mod8] using this
      simpa using this
    refine ⟨a, m' / 8, ?_⟩
    -- Reconstruct `m' = 8*(m'/8) + 7` from `m'%8 = 7`.
    have hm'_shape : m' = 8 * (m' / 8) + 7 := by
      have := (Nat.div_add_mod m' 8).symm
      simpa [hm'_mod8] using this
    -- Put it all together.
    -- Avoid aggressive `simp` (it can loop on nested `(/)` rewrites).
    calc
      m = 4 ^ a * m' := by simpa [hm', Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = 4 ^ a * (8 * (m' / 8) + 7) := by exact congrArg (fun z => 4 ^ a * z) hm'_shape
  · rintro ⟨a, t, hm⟩
    refine ⟨a, ?_, ?_⟩
    · -- Witness for the `(8*?+7)` part after multiplying by `k^2`.
      -- Let `x := k^2 * (8*t+7)`; show it has remainder 7 mod 8.
      let x : ℕ := k ^ 2 * (8 * t + 7)
      refine x / 8
    · -- Show `k^2*m = 4^a*(8*?/8 + 7)`.
      -- Start from `hm : m = 4^a*(8*t+7)` and multiply by `k^2`.
      have hk2_mod8 : (k ^ 2) % 8 = 1 := sq_mod_eight_odd k hk
      have hx_mod : (k ^ 2 * (8 * t + 7)) % 8 = 7 := by
        -- (k^2 mod 8) * ((8*t+7) mod 8) = 1 * 7.
        rw [Nat.mul_mod, hk2_mod8]
        simp
      let x : ℕ := k ^ 2 * (8 * t + 7)
      have hx_shape : x = 8 * (x / 8) + 7 := by
        have := (Nat.div_add_mod x 8).symm
        simpa [x, hx_mod] using this
      -- Now finish.
      -- `k^2 * m = 4^a * x` and rewrite `x` into `8*(x/8)+7`.
      calc
        k ^ 2 * m = k ^ 2 * (4 ^ a * (8 * t + 7)) := by simpa [hm]
        _ = 4 ^ a * (k ^ 2 * (8 * t + 7)) := by
          simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
        _ = 4 ^ a * (8 * (x / 8) + 7) := by
          -- Avoid rewriting inside `x / 8` (same issue as before): use congrArg.
          exact congrArg (fun z => 4 ^ a * z) (by simpa [x] using hx_shape)

lemma sum_three_squares_reduction (n : ℕ) (h : ¬ is_three_square_exception n)
    (h_sqfree : ∀ m : ℕ, Squarefree m → ¬ is_three_square_exception m → ∃ x y z, x^2 + y^2 + z^2 = m) :
    ∃ x y z, x^2 + y^2 + z^2 = n := by
  rcases eq_or_ne n 0 with rfl | hn0
  · exact ⟨0, 0, 0, by simp⟩
  -- Write n = s^2 * m with m squarefree.
  -- Note: sq_mul_squarefree returns ⟨m, s, ...⟩ where m is squarefree and s^2 * m = n.
  rcases Nat.sq_mul_squarefree n with ⟨m, s, hs, hm⟩
  rw [← hs]
  -- Show m is not exception
  have hm_not_exc : ¬ is_three_square_exception m := by
    intro hm_exc
    apply h
    rw [← hs]
    -- n = s^2 * m.
    -- If m is exception, then s^2 * m is exception.
    -- We can extract powers of 4 from s^2.
    -- Let s = 2^k * u with u odd. s^2 = 4^k * u^2.
    -- n = 4^k * (u^2 * m).
    -- u^2 * m is exception iff m is exception (since u^2 = 1 mod 8).
    have hs_ne0 : s ≠ 0 := by
      intro hs0
      apply hn0
      -- From `hs : s^2 * m = n`, `s = 0` forces `n = 0`.
      have : (0 : ℕ) = n := by
        simpa [hs0] using hs
      simpa using this.symm
    let k : ℕ := s.factorization 2
    let u : ℕ := ordCompl[2] s
    have hs_decomp : s = 2 ^ k * u := by
      -- `ordProj_mul_ordCompl_eq_self` is exactly `2^k * (s / 2^k) = s`.
      have : 2 ^ k * u = s := by
        simpa [k, u] using (Nat.ordProj_mul_ordCompl_eq_self s 2)
      exact this.symm
    have hu_odd : Odd u := by
      rw [← not_even_iff_odd, even_iff_two_dvd]
      have : ¬ 2 ∣ ordCompl[2] s := Nat.not_dvd_ordCompl Nat.prime_two hs_ne0
      simpa [u] using this
    have hs_sq : s ^ 2 = 4 ^ k * u ^ 2 := by
      have hk : (2 ^ k) ^ 2 = 4 ^ k := by
        calc
          (2 ^ k) ^ 2 = 2 ^ (k * 2) := (pow_mul 2 k 2).symm
          _ = 2 ^ (2 * k) := by simp [Nat.mul_comm]
          _ = (2 ^ 2) ^ k := (pow_mul 2 2 k)
          _ = 4 ^ k := by simp
      calc
        s ^ 2 = (2 ^ k * u) ^ 2 := by simpa [hs_decomp]
        _ = (2 ^ k) ^ 2 * u ^ 2 := by simp [mul_pow]
        _ = 4 ^ k * u ^ 2 := by simpa [hk]
    rw [hs_sq, mul_assoc]
    -- n = 4^k * (u^2 * m).
    -- If m is exception, m = 4^a * (8t + 7).
    -- Since m is squarefree, a=0. m = 8t + 7.
    obtain ⟨a, t, hm_eq⟩ := hm_exc
    have ha0 : a = 0 := by
      cases a with
      | zero => rfl
      | succ a =>
        exfalso
        have h4m : 4 ∣ m := by
          -- `m = 4^(a+1) * (8*t+7)` gives `4 ∣ m`.
          rw [hm_eq, Nat.pow_succ]
          -- Normalize associativity/commutativity so `dvd_mul_of_dvd_left` matches.
          simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
            (dvd_mul_of_dvd_left (dvd_mul_right 4 (4 ^ a)) (8 * t + 7))
        have hu : IsUnit (2 : ℕ) := by
          -- `4 ∣ m` is the same as `2 * 2 ∣ m`, which contradicts squarefreeness.
          exact hm 2 (by simpa using h4m)
        have h21 : (2 : ℕ) = 1 := (Nat.isUnit_iff).1 hu
        exact (by decide : (2 : ℕ) ≠ 1) h21
    subst ha0; simp at hm_eq
    -- m = 8t + 7.
    -- u^2 * m is exception?
    -- u^2 = 1 mod 8.
    -- u^2 * m = 1 * 7 = 7 mod 8.
    -- So u^2 * m = 8k' + 7.
    -- So n = 4^k * (8k' + 7). Exception.
    refine ⟨k, ?_⟩
    -- need to show u^2 * m is of form 8k' + 7.
    rw [hm_eq]
    have hmod : (u ^ 2 * (8 * t + 7)) % 8 = 7 := by
      rw [Nat.mul_mod, sq_mod_eight_odd u hu_odd]
      simp
    let x : ℕ := u ^ 2 * (8 * t + 7)
    refine ⟨x / 8, ?_⟩
    have hx : x = 8 * (x / 8) + 7 := by
      have hx' : x = 8 * (x / 8) + x % 8 := (Nat.div_add_mod x 8).symm
      -- Replace `x % 8` using the computed remainder.
      simpa [x, hmod] using hx'
    -- Use `hx` only on the outer occurrence of `x` (avoid rewriting inside `x / 8`).
    calc
      4 ^ k * (u ^ 2 * (8 * t + 7)) = 4 ^ k * x := by simp [x]
      _ = 4 ^ k * (8 * (x / 8) + 7) := by
        -- Avoid rewriting `x` inside `x / 8` (simp/rw can loop here).
        exact congrArg (fun z => 4 ^ k * z) hx
  -- Apply h_sqfree
  obtain ⟨x, y, z, hsum⟩ := h_sqfree m hm hm_not_exc
  -- Lift to n
  exact sum_three_squares_mul_sq m s ⟨x, y, z, hsum⟩

theorem sum_three_squares_of_not_exception (n : ℕ) (h : ¬ is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  -- TODO: full proof (Legendre three-squares theorem, hard direction).
  --
  -- We are currently pivoting to a Minkowski/geometry-of-numbers proof route in
  -- `PolygonalNumberTheorem/MinkowskiDescent.lean`.
  --
  -- Once that file is completed, this theorem should become:
  -- `exact PolygonalNumberTheorem.minkowski_three_squares n h`.
  sorry

theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ is_three_square_exception n :=
  ⟨not_exception_of_sum_three_squares n, sum_three_squares_of_not_exception n⟩

/-- For an odd prime `p`, `x^2 + y^2 = -1` is solvable in `ZMod p`. -/
lemma exists_sq_add_sq_eq_neg_one_mod_prime (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ x y : ZMod p, x ^ 2 + y ^ 2 = -1 := by
  -- Mathlib proves the stronger statement that every `x : ZMod p` is a sum of two squares.
  -- We only need the special case `x = -1`.
  simpa using (ZMod.sq_add_sq p (-1 : ZMod p))

theorem exists_sq_add_sq_add_one_mod_n (n : ℕ) (hn : Odd n) (_hn_pos : 0 < n)
    (hn_sqfree : Squarefree n) :
    ∃ u v : ℤ, u ^ 2 + v ^ 2 + 1 ≡ 0 [ZMOD n] := by
  -- This lemma is used as a “local condition” seed for the Minkowski-style descent lattice.
  --
  -- Implementation choice:
  -- We prove it for *squarefree* odd `n` by CRT over distinct prime factors.
  -- (General odd `n` would require prime-power lifting / Hensel-style arguments.)
  classical
  -- First prove the congruence in `ℕ` and then cast to `ℤ`.
  have hn' : ∃ u v : ℕ, u ^ 2 + v ^ 2 + 1 ≡ 0 [MOD n] := by
    refine (induction_on_primes
      (motive := fun n => Odd n → Squarefree n → ∃ u v : ℕ, u ^ 2 + v ^ 2 + 1 ≡ 0 [MOD n])
      ?zero ?one ?prime_mul n hn hn_sqfree)
    · intro hn0 _hs0
      -- `Odd 0` is impossible.
      exfalso
      rcases hn0 with ⟨w, hw⟩
      omega
    · intro _hn1 _hs1
      refine ⟨0, 0, ?_⟩
      simp [Nat.ModEq]
    · intro p a hp ih hpa hs_pa
      haveI : Fact p.Prime := ⟨hp⟩
      -- squarefree(p*a) gives coprimality and squarefree(a)
      have hcop : p.Coprime a := Nat.coprime_of_squarefree_mul hs_pa
      have hs_a : Squarefree a := (Nat.squarefree_mul hcop).1 hs_pa |>.2
      -- odd(p*a) gives odd(a)
      have ha_odd : Odd a := (Nat.odd_mul.mp hpa).2

      -- IH gives a solution modulo `a`.
      obtain ⟨uA, vA, hA⟩ := ih ha_odd hs_a

      -- Prime case gives a solution modulo `p` for `-1`, i.e. `p-1` in `ℕ`.
      obtain ⟨uP, vP, _huP, _hvP, hP0⟩ := Nat.sq_add_sq_modEq p (p - 1)
      have hP : uP ^ 2 + vP ^ 2 + 1 ≡ 0 [MOD p] := by
        have hP1 : uP ^ 2 + vP ^ 2 + 1 ≡ (p - 1) + 1 [MOD p] := by
          -- `add_right` then reassociate
          simpa [Nat.add_assoc] using (Nat.ModEq.add_right 1 hP0)
        have hp_pos : 0 < p := hp.pos
        have hpeq : (p - 1) + 1 = p := Nat.sub_add_cancel (Nat.succ_le_iff.2 hp_pos)
        have : p ≡ 0 [MOD p] := by simp [Nat.ModEq]
        have : (p - 1) + 1 ≡ 0 [MOD p] := by simpa [hpeq] using this
        exact hP1.trans this

      -- CRT: choose `u` matching `uP (mod p)` and `uA (mod a)`, similarly for `v`.
      let u := (Nat.chineseRemainder hcop uP uA).1
      let v := (Nat.chineseRemainder hcop vP vA).1
      have hu_mod_p : u ≡ uP [MOD p] := (Nat.chineseRemainder hcop uP uA).2.1
      have hu_mod_a : u ≡ uA [MOD a] := (Nat.chineseRemainder hcop uP uA).2.2
      have hv_mod_p : v ≡ vP [MOD p] := (Nat.chineseRemainder hcop vP vA).2.1
      have hv_mod_a : v ≡ vA [MOD a] := (Nat.chineseRemainder hcop vP vA).2.2

      have h_mod_p : u ^ 2 + v ^ 2 + 1 ≡ 0 [MOD p] := by
        have hu2 : u ^ 2 ≡ uP ^ 2 [MOD p] := hu_mod_p.pow 2
        have hv2 : v ^ 2 ≡ vP ^ 2 [MOD p] := hv_mod_p.pow 2
        have huv2 : u ^ 2 + v ^ 2 ≡ uP ^ 2 + vP ^ 2 [MOD p] := hu2.add hv2
        have : u ^ 2 + v ^ 2 + 1 ≡ uP ^ 2 + vP ^ 2 + 1 [MOD p] := by
          simpa [Nat.add_assoc] using (Nat.ModEq.add_right 1 huv2)
        exact this.trans hP

      have h_mod_a : u ^ 2 + v ^ 2 + 1 ≡ 0 [MOD a] := by
        have hu2 : u ^ 2 ≡ uA ^ 2 [MOD a] := hu_mod_a.pow 2
        have hv2 : v ^ 2 ≡ vA ^ 2 [MOD a] := hv_mod_a.pow 2
        have huv2 : u ^ 2 + v ^ 2 ≡ uA ^ 2 + vA ^ 2 [MOD a] := hu2.add hv2
        have : u ^ 2 + v ^ 2 + 1 ≡ uA ^ 2 + vA ^ 2 + 1 [MOD a] := by
          simpa [Nat.add_assoc] using (Nat.ModEq.add_right 1 huv2)
        exact this.trans hA

      have : u ^ 2 + v ^ 2 + 1 ≡ 0 [MOD p * a] := by
        exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h_mod_p, h_mod_a⟩
      exact ⟨u, v, this⟩

  -- Now cast the `ℕ` congruence to `ℤ` congruence.
  rcases hn' with ⟨u, v, huv⟩
  refine ⟨(u : ℤ), (v : ℤ), ?_⟩
  have hZ : (u ^ 2 + v ^ 2 + 1 : ℕ) ≡ 0 [ZMOD n] := (Int.natCast_modEq_iff).2 huv
  -- `simp` turns `((u:ℤ)^2 + (v:ℤ)^2 + 1)` into `((u^2+v^2+1:ℕ):ℤ)`.
  simpa using (show ((u ^ 2 + v ^ 2 + 1 : ℕ) : ℤ) ≡ (0 : ℤ) [ZMOD n] from hZ)

end Nat