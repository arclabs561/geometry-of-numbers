
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

section AnkenyReduction

variable (n q : ℕ) (x y z : ℤ)

/-- The core reduction lemma for Ankeny's theorem.
    If `y^2 + n*z^2 = 2*q*(n - x^2)` with `q ≡ 1 mod 4`, `n ≡ 3 mod 4`,
    then `n - x^2` is a sum of two squares. -/
lemma ankeny_reduction_step
    (hn_mod4 : n % 4 = 3)
    (hq_prime : Nat.Prime q)
    (hq_mod4 : q % 4 = 1)
    (h_eq : y^2 + n * z^2 = 2 * q * (n - x^2)) :
    ∃ u v : ℤ, n - x^2 = u^2 + v^2 := by
  have hK_nonneg : 0 ≤ n - x^2 := by
    have h_rhs : 0 ≤ y^2 + n * z^2 := by
      apply add_nonneg (sq_nonneg y)
      apply mul_nonneg (Int.natCast_nonneg n) (sq_nonneg z)
    rw [h_eq] at h_rhs
    have h2q : 0 < (2 * q : ℤ) := by
      have hq : 0 < q := hq_prime.pos
      norm_cast; linarith
    exact nonneg_of_mul_nonneg_right h_rhs h2q
  
  let K := (n - x^2).natAbs
  have hK_eq : (K : ℤ) = n - x^2 := Int.natAbs_of_nonneg hK_nonneg
  
  suffices (∃ u v : ℕ, K = u ^ 2 + v ^ 2) by
    obtain ⟨u, v, huv⟩ := this
    refine ⟨(u : ℤ), (v : ℤ), ?_⟩
    have : (K : ℤ) = (u : ℤ) ^ 2 + (v : ℤ) ^ 2 := by
      have : (K : ℤ) = (u ^ 2 + v ^ 2 : ℤ) := by
        exact_mod_cast huv
      simpa [pow_two, add_assoc, add_left_comm, add_comm] using this
    simpa [hK_eq] using this.symm
  
  rw [Nat.eq_sq_add_sq_iff]
  intro p hp_prime_factors hp_mod3
  
  -- We prove v_p(K) is even by infinite descent (induction on valuation).
  -- Actually, `padicValNat` is just a number. If it were odd, we would have a contradiction.
  -- But usually proving `even` is done by showing if `p^k || K`, then `k` must be even.
  -- Simpler: Show that if `p | K` and `p % 4 = 3`, then `p^2 | K`.
  -- This implies the valuation is even (if finite).
  
  -- Let's prove the "step": if `p | K` (where K satisfies the equation), then `p^2 | K` 
  -- and `K/p^2` satisfies the same equation (with `y/p, z/p`).
  
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp_prime_factors
  have hp_odd : p ≠ 2 := by
    intro h; rw [h] at hp_mod3; contradiction
  have hp_not_q : p ≠ q := by
    intro h; rw [h] at hp_mod3; rw [hq_mod4] at hp_mod3; contradiction
  
  -- We need to act on the valuation directly.
  -- Let `k = padicValNat p K`. We want to show `Even k`.
  -- We can do this by strong induction on `K`? No, K is fixed.
  -- We can do induction on `k`.
  -- Or just prove `p^(2m+1) || K` is impossible.
  -- Let's define a property `P(m)`: `y^2 + n z^2 = 2 q m` implies `padicValNat p m` is even.
  
  -- Let's assume `padicValNat p K` is odd, and derive contradiction.
  by_contra h_odd
  rw [Nat.not_even_iff_odd] at h_odd
  
  -- Let `v = padicValNat p K`. Since v is odd, `v ≥ 1`, so `p | K`.
  have hp_dvd_K : p ∣ K := Nat.dvd_of_mem_primeFactors hp_prime_factors
  
  -- Key Lemma: `p | K` implies `p | y` and `p | z`.
  have key_step : ∀ {K' y' z' : ℤ}, y'^2 + n * z'^2 = 2 * q * K' → (p : ℤ) ∣ K' → (p : ℤ) ∣ y' ∧ (p : ℤ) ∣ z' := by
    intro K' y' z' heq hdiv
    -- Reduce mod p
    have hmod : (y'^2 + n * z'^2) ≡ 0 [ZMOD p] := by
      rw [heq]
      apply Int.ModEq.mul_right
      apply Int.ModEq.mul_right
      exact Int.modEq_zero_of_dvd hdiv
    
    -- y'^2 ≡ -n z'^2 (mod p)
    have h_sq : y'^2 ≡ -n * z'^2 [ZMOD p] := by
      rw [← add_eq_zero_iff_eq_neg]
      exact hmod
      
    -- If p ∤ z', then z' has an inverse mod p.
    by_cases hz : (p : ℤ) ∣ z'
    · -- If p | z', then p | n z'^2. From sum=0, p | y'^2 => p | y'.
      have hy : (p : ℤ) ∣ y' := by
        have : (p : ℤ) ∣ y'^2 := by
          rw [Int.dvd_iff_modEq_zero, sq]
          -- y^2 = -n z^2 mod p. z = 0 mod p => y^2 = 0 mod p.
          apply (Int.ModEq.add_right (n * z'^2)).1
          rw [zero_add]
          convert hmod using 1
          rw [Int.dvd_iff_modEq_zero] at hz
          rw [sq, mul_assoc, hz, mul_zero, mul_zero, add_zero]
        exact Int.prime_iff_prime_int.1 hp_prime |>.dvd_of_dvd_pow this
      exact ⟨hy, hz⟩
      
    · -- If p ∤ z', we get contradiction.
      exfalso
      -- -n is a square mod p (y' * z'⁻¹)^2
      -- n is a square mod p (since K = n - x^2 => n ≡ x^2 mod p)
      -- So -1 is a square mod p. Contradiction to p % 4 = 3.
      
      -- 1. n is a square mod p.
      -- Recall K' might not be n - x^2.
      -- Wait, the descent must preserve the form `K' = n - x'^2`?
      -- The lemma `ankeny_reduction_step` is about a specific `K`.
      -- But the lemma statement `IsSumTwoSquares K` only cares about prime factors of `K`.
      -- We need `n` to be a square mod `p`.
      -- We know `p | K`, and `K = n - x^2` (initially).
      -- So `p | n - x^2` => `n ≡ x^2 [ZMOD p]`.
      -- THIS IS ONLY TRUE FOR THE INITIAL K.
      -- But `hp_prime_factors` is for the initial K.
      -- So `p` is fixed from the start.
      
      -- So we DO know `n` is a QR mod `p`.
      have hn_qr : IsSquare (n : ZMod p) := by
        have : (n : ZMod p) = (x : ZMod p)^2 := by
          -- p | K = n - x^2 => n - x^2 = 0 mod p => n = x^2 mod p
          have h : (n : ℤ) - x^2 ≡ 0 [ZMOD p] := Int.modEq_zero_of_dvd (Int.natCast_dvd_natCast.2 hp_dvd_K)
          norm_cast
          rw [Int.modEq_iff_dvd] at h
          symm
          rw [eq_iff_sub_eq_zero]
          norm_cast
          exact h
        use x
        symm; exact this

      -- 2. -n is a square mod p.
      have hneg_n_qr : IsSquare (-(n : ZMod p)) := by
        -- y'^2 ≡ -n z'^2 [ZMOD p]
        -- z' is invertible
        have : IsUnit (z' : ZMod p) := by
          rw [isUnit_iff_ne_zero, ne_eq, ← Int.cast_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact hz
        use (y' : ZMod p) * (this.unit)⁻¹
        simp only [isUnit_inv_val_apply, mul_pow]
        -- want (y')^2 * (z'^-1)^2 = -n
        rw [← mul_inv_cancel_right₀ this.ne_zero (-(n : ZMod p))]
        rw [← mul_assoc, ← sq]
        congr 1
        -- y'^2 = -n * z'^2
        norm_cast at h_sq
        convert h_sq
        simp
        
      -- 3. Therefore -1 is a square mod p.
      have hneg_one_qr : IsSquare (-1 : ZMod p) := by
        -- -1 = (-n) * n⁻¹?
        -- Yes, if n is invertible. Is n invertible?
        -- If p | n, then p | x (since n ≡ x^2).
        -- If p | n, then p = 3 (since n%4=3 and p%4=3 and p|n?? no)
        -- n could be composite. But `n % 4 = 3`.
        -- If p | n, then y^2 ≡ 0 mod p => p | y.
        -- We assumed p ∤ z'.
        -- If p | n, then -n ≡ 0 mod p.
        -- Then y'^2 ≡ 0 => p | y'.
        -- But z' is free.
        -- We need `n` to be a unit mod `p` OR handle p|n separately.
        
        by_cases hpn : (p : ℤ) ∣ n
        · -- If p | n:
          -- Since n ≡ 3 mod 4, and p ≡ 3 mod 4.
          -- If p | n, then n = p * k.
          -- Then y^2 + p*k*z^2 = 2qK.
          -- p | K. So p | y^2 => p | y.
          -- Then p^2 | y^2. p | p*k*z^2.
          -- p^2 | 2qK.
          -- This doesn't immediately contradict p ∤ z'.
          -- However, we are in the context of "n - x^2 is a sum of two squares".
          -- If p | n and p % 4 = 3, then v_p(n) must be even for n to be a sum of 2 sq?
          -- No, we are proving K is a sum of 2 squares.
          -- The question is: can `p` divide `n`?
          -- If `p | n`, then `n ≡ 0`.
          -- `x^2 ≡ n ≡ 0`. So `p | x`.
          -- So `p^2 | x^2`.
          -- `K = n - x^2`. `p | K`.
          -- If `v_p(n) = 1`?
          -- `n` is fixed.
          -- `p` is a prime factor of `K`.
          -- If `p | n`, `p | x`, `p | y`.
          -- `y^2 + n z^2 = 2qK`.
          -- Divide by `p`.
          -- `(y^2/p) + (n/p) z^2 = 2q(K/p)`.
          -- `0 + (n/p) z^2 ≡ 0 (mod p)`?
          -- `(n/p)` is not div by `p` if `v_p(n)=1`.
          -- Then `z^2 ≡ 0`, so `p | z`. Contradiction to `hz`.
          -- So if `v_p(n)` is odd, we get `p | z`.
          -- What if `v_p(n)` is even?
          -- We assume `n` is squarefree in Ankeny? No, just `n % 8 = 3`.
          -- But wait, if `n` has a prime factor `p \equiv 3 \pmod 4` with odd exponent,
          -- then `n` is not a sum of 3 squares? No, `n` CAN be.
          -- Example: `n=3`. `p=3`. `v_3(3)=1`. `3 = 1^2+1^2+1^2`.
          -- So `p | n` is possible.
          
          -- Let's revisit the contradiction `IsSquare (-1)`.
          -- We have `y^2 = -n z^2` in `ZMod p`.
          -- If `p | n`, then `y^2 = 0`, so `y=0`.
          -- But `hz` says `z \ne 0`.
          -- The equation `0 = 0` gives no info.
          
          -- HOWEVER, `K = n - x^2`.
          -- If `p | n`, then `p | x^2`. `p | x`.
          -- `K = p * (n/p - x^2/p)`.
          -- `2qK = 2q * p * (...)`.
          -- `y^2 + n z^2 = p^2 (...) + p * (n/p) * z^2`.
          -- `y = p y'`.
          -- `p^2 y'^2 + p * (n/p) * z^2 = 2 q p (K/p)`.
          -- Divide by `p`:
          -- `p y'^2 + (n/p) z^2 = 2 q (K/p)`.
          -- Mod `p`:
          -- `(n/p) z^2 ≡ 2 q (K/p) (mod p)`.
          -- We know `p | K`, so `p | K/p`?
          -- `padicValNat p K` is the total valuation.
          -- If `v_p(K) = 1`, then `K/p` is not div by `p`.
          -- `n/p` might be div by `p`.
          
          -- This is getting complicated.
          -- Is it possible `p | n`?
          -- If `p | n`, then `n ≡ x^2 ≡ 0`.
          -- Ankeny proof usually assumes `n` squarefree or handles `p|n`.
          -- But notice: `x^2 \equiv n \pmod p`.
          -- If `p \nmid n`, then `n` is a unit.
          -- If `p \mid n`, we need to handle it.
          -- But if `p | n` and `p = 3 mod 4`, then `p` appears in `n`.
          
          -- Let's punt on `p|n` for a moment and assume `p \nmid n`.
          sorry
        
        -- If `p \nmid n`, then `n` is a unit.
        have : IsUnit (n : ZMod p) := by
          rw [isUnit_iff_ne_zero, ne_eq, ← Int.cast_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
          exact hpn
        
        -- (-n) * n⁻¹ = -1
        convert IsSquare.mul hneg_n_qr (IsSquare.inv hn_qr)
        field_simp
        
      -- -1 is not a square mod p (since p % 4 = 3)
      have h_not_qr : ¬ IsSquare (-1 : ZMod p) := by
        have : Fact (Nat.Prime p) := ⟨hp_prime⟩
        rw [ZMod.exists_sq_eq_neg_one_iff]
        exact hp_mod3
      
      contradiction

  -- Now we have `p | y` and `p | z`.
  -- We proceed by descent.
  -- v_p(y^2) >= 2, v_p(n z^2) >= 2.
  -- So v_p(LHS) >= 2.
  -- LHS = 2 q K.
  -- So v_p(2 q K) >= 2.
  -- Since p != 2 and p != q, v_p(2 q K) = v_p(K).
  -- So v_p(K) >= 2.
  
  -- We can "cancel" p^2 from the equation.
  -- `K = p^2 * K_new`. `y = p * y_new`. `z = p * z_new`.
  -- `(p y_new)^2 + n (p z_new)^2 = 2 q (p^2 K_new)`
  -- `p^2 (y_new^2 + n z_new^2) = p^2 (2 q K_new)`
  -- `y_new^2 + n z_new^2 = 2 q K_new`
  -- And `padicValNat p K_new = padicValNat p K - 2`.
  
  -- Since we assumed `padicValNat p K` is odd, `padicValNat p K_new` is also odd.
  -- This creates an infinite descent (or induction).
  -- Since we can't do infinite descent easily in a `have` block without well-founded recursion,
  -- we should use `Nat.padicValNat` properties.
  
  -- Let `v = padicValNat p K`.
  -- We proved: if `v >= 1` (i.e. `p | K`), then `p | y` and `p | z`.
  -- This implies `p^2 | y^2 + n z^2 = 2 q K`.
  -- So `p^2 | K`.
  -- Thus `v >= 2`.
  -- And if `v >= 2`, we can divide everything by `p^2` to get a solution for `K/p^2`.
  -- By induction, if `v` is odd, we eventually reach `v=1`.
  -- But we proved `v >= 1 -> v >= 2`. Contradiction.
  
  -- To formalize this:
  -- Use `Nat.rec` on `v`.
  -- Wait, `v` is fixed.
  -- We need to define a sequence of solutions `(K_i, y_i, z_i)`?
  -- Or just prove: `∀ k, y^2 + n z^2 = 2 q K → p^(2k+1) || K → False`.
  
  -- Strategy:
  -- Prove `∀ m y z, y^2 + n z^2 = 2 q m → p ∣ m → p^2 ∣ m ∧ (∃ y' z', y = p y' ∧ z = p z' ∧ y'^2 + n z'^2 = 2 q (m/p^2))`.
  
  sorry

end AnkenyReduction
