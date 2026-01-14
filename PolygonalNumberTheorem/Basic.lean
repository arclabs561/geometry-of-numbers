import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace PolygonalNumberTheorem

/-!
## Polygonal numbers

We’ll eventually formalize Cauchy’s proof of Fermat’s polygonal number theorem:

```text
Every natural number is a sum of s s-gonal numbers.
```

This file is the “algebra spine” for polygonal numbers: definitions and a few
identities that make later ring manipulations feasible.
-/

/-- The `s`-gonal number at index `n`.

```text
P(s,n) = n + (s-2) * (n(n-1)/2)
```

We keep the definition in `ℕ`; later proofs will usually move to `ℤ` for ring algebra.
-/
def polygonal (s n : ℕ) : ℕ :=
  n + (s - 2) * n * (n - 1) / 2

/-- Triangular numbers (3-gonal). -/
def triangular (n : ℕ) : ℕ := polygonal 3 n

/-- Square numbers (4-gonal). -/
def square (n : ℕ) : ℕ := polygonal 4 n

/-- Pentagonal numbers (5-gonal). -/
def pentagonal (n : ℕ) : ℕ := polygonal 5 n

@[simp] lemma triangular_def (n : ℕ) : triangular n = n + n * (n - 1) / 2 := by
  simp [triangular, polygonal]

/-!
### Exactness of the `/ 2`

The definition uses `/ 2` in `ℕ`. A recurring need is to “clear denominators”:
show the relevant numerator is even, so multiplying by 2 cancels the division.
-/

lemma two_dvd_polygonal_numer (s n : ℕ) : 2 ∣ (s - 2) * n * (n - 1) := by
  -- `n * (n - 1)` is always even.
  have hn : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
  -- Multiply by `(s-2)`.
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using dvd_mul_of_dvd_right hn (s - 2)

lemma two_mul_polygonal (s n : ℕ) :
    2 * polygonal s n = 2 * n + (s - 2) * n * (n - 1) := by
  dsimp [polygonal]
  have h2 : 2 ∣ (s - 2) * n * (n - 1) := two_dvd_polygonal_numer s n
  rw [Nat.mul_add]
  congr 1
  exact Nat.mul_div_cancel' h2

@[simp] lemma square_def (n : ℕ) : square n = n ^ 2 := by
  apply Nat.mul_left_cancel (show 0 < 2 by decide)
  rw [square, two_mul_polygonal]
  cases n with
  | zero => simp
  | succ n =>
    simp [Nat.succ_eq_add_one, pow_two]
    ring

lemma polygonal_four_eq_sq (n : ℕ) : polygonal 4 n = n ^ 2 := square_def n

lemma odd_sq_eq_eight_triangular_add_one (n : ℕ) : (2 * n + 1) ^ 2 = 8 * triangular n + 1 := by
  sorry

/-!
### The same identity in `ℤ`

Warning: because the definition uses `(s - 2)` in `ℕ`, this identity is only true
once we assume `2 ≤ s`. (Otherwise `(s - 2)` truncates to 0 in `ℕ`.)

Under `2 ≤ s`, we can express `2 * P(s,n)` as a genuine quadratic polynomial in `n`.
-/

lemma two_mul_polygonal_int (s n : ℕ) (hs : 2 ≤ s) :
    (2 * polygonal s n : ℤ) =
      ((s : ℤ) - 2) * (n : ℤ) ^ 2 + ((4 : ℤ) - s) * (n : ℤ) := by
  -- First rewrite `n*(n-1)` into `n*n - n` *in ℕ*.
  have hNat : 2 * polygonal s n = 2 * n + (s - 2) * (n * n - n) := by
    simpa [Nat.mul_assoc, Nat.mul_sub_left_distrib, Nat.mul_one, Nat.sub_mul] using
      (two_mul_polygonal s n)

  -- Cast the ℕ identity to ℤ.
  have hInt :
      ((2 * polygonal s n : ℕ) : ℤ) =
        ((2 * n + (s - 2) * (n * n - n) : ℕ) : ℤ) := by
    exact congrArg (fun t : ℕ => (t : ℤ)) hNat

  -- Rewrite casted truncating subtractions.
  have hs' : ((s - 2 : ℕ) : ℤ) = (s : ℤ) - 2 := by
    simpa using (Nat.cast_sub hs)

  have hnle : n ≤ n * n := Nat.le_mul_self n
  have hn' : ((n * n - n : ℕ) : ℤ) = (n : ℤ) * (n : ℤ) - (n : ℤ) := by
    simpa using (Nat.cast_sub hnle)

  -- Normalize casts and finish by ring algebra.
  have h1 : (2 * polygonal s n : ℤ) =
      2 * (n : ℤ) + ((s : ℤ) - 2) * ((n : ℤ) * (n : ℤ) - (n : ℤ)) := by
    simpa [Nat.cast_add, Nat.cast_mul, hs', hn', pow_two] using hInt

  -- Rearrange into the requested quadratic polynomial.
  calc
    (2 * polygonal s n : ℤ)
        = 2 * (n : ℤ) + ((s : ℤ) - 2) * ((n : ℤ) * (n : ℤ) - (n : ℤ)) := h1
    _ = ((s : ℤ) - 2) * (n : ℤ) ^ 2 + ((4 : ℤ) - s) * (n : ℤ) := by
        ring


/-!
### Recurrence

A useful “difference” identity: consecutive polygonal numbers differ by a linear term.

The clean statement is:

```text
P(s,n+1) = P(s,n) + 1 + (s-2)*n
```

The proof works in `ℕ` by clearing the `/2` denominator using [`two_mul_polygonal`], and
then using the elementary identity `n*(n+1) = n*(n-1) + 2*n`.
-/

lemma mul_mul_pred_add_two_mul (n : ℕ) : n * (n - 1) + 2 * n = n * (n + 1) := by
  cases n with
  | zero => simp
  | succ n =>
      simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma polygonal_succ (s n : ℕ) :
    polygonal s (n + 1) = polygonal s n + 1 + (s - 2) * n := by
  -- Prove by clearing the `/2` denominator (multiply by 2) and doing arithmetic in `ℕ`.
  apply Nat.mul_left_cancel (show 0 < 2 by decide)

  -- LHS: expand `2 * polygonal s (n+1)`.
  have hL :
    2 * polygonal s (n + 1) = 2 * (n + 1) + (s - 2) * (n + 1) * n := by
    simpa [Nat.add_sub_cancel] using (two_mul_polygonal s (n + 1))

  -- RHS: expand using `two_mul_polygonal`.
  have hR :
    2 * (polygonal s n + 1 + (s - 2) * n) =
      2 * n + (s - 2) * n * (n - 1) + 2 + 2 * ((s - 2) * n) := by
    simp [Nat.mul_add, two_mul_polygonal s n, Nat.add_left_comm, Nat.add_comm]

  rw [hL, hR]

  -- The key identity: (s-2)*(n+1)*n = (s-2)*n*(n-1) + 2*(s-2)*n
  -- which follows from n*(n+1) = n*(n-1) + 2*n.
  have hnn : n * (n + 1) = n * (n - 1) + 2 * n := (mul_mul_pred_add_two_mul n).symm

  -- Now it's a polynomial identity; normalize and close.
  calc
    2 * (n + 1) + (s - 2) * (n + 1) * n
        = 2 * n + 2 + (s - 2) * (n * (n + 1)) := by ring
    _ = 2 * n + 2 + (s - 2) * (n * (n - 1) + 2 * n) := by rw [hnn]
    _ = 2 * n + (s - 2) * n * (n - 1) + 2 + 2 * ((s - 2) * n) := by ring

/-!
### Monotonicity

Polygonal numbers are strictly increasing in `n` (for any `s`).
This follows immediately from `polygonal_succ`.
-/

lemma polygonal_lt_succ (s n : ℕ) : polygonal s n < polygonal s (n + 1) := by
  rw [polygonal_succ]
  -- `polygonal s n + 1 + (s-2)*n ≥ polygonal s n + 1 > polygonal s n`
  omega

lemma polygonal_le_succ (s n : ℕ) : polygonal s n ≤ polygonal s (n + 1) :=
  Nat.le_of_lt (polygonal_lt_succ s n)

lemma polygonal_strictMono (s : ℕ) : StrictMono (polygonal s) := by
  intro m n hmn
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hmn) with rfl | hlt
      · exact polygonal_lt_succ s m
      · exact Nat.lt_trans (ih hlt) (polygonal_lt_succ s n)

lemma polygonal_mono (s : ℕ) : Monotone (polygonal s) :=
  (polygonal_strictMono s).monotone

/-!
### Base cases

Useful for bootstrapping inductive arguments.
-/

@[simp] lemma polygonal_zero (s : ℕ) : polygonal s 0 = 0 := by
  simp [polygonal]

@[simp] lemma polygonal_one (s : ℕ) : polygonal s 1 = 1 := by
  simp [polygonal]

/-- Alternative closed form for the `s`-gonal number at index `n`.
    `P(s, n) = ((s - 2) * n² - (s - 4) * n) / 2`
-/
theorem polygonal_def_alt (s n : ℕ) (hs : 2 ≤ s) :
    (2 * polygonal s n : ℤ) = ((s : ℤ) - 2) * (n : ℤ) ^ 2 + ((4 : ℤ) - s) * (n : ℤ) := by
  -- In `ℕ`, the coefficient `(s-4)` truncates at 0, so the clean closed form lives in `ℤ`.
  simpa using (two_mul_polygonal_int s n hs)

/-- The "Cauchy identity" connecting sums of polygonal numbers to sums of squares.
    This is the core algebraic insight behind Cauchy's proof.
-/
theorem cauchy_polygonal_identity (s : ℕ) (hs : 3 ≤ s) (t u v w : ℕ) :
    let m : ℤ := (s : ℤ) - 2
    (2 * (polygonal s t + polygonal s u + polygonal s v + polygonal s w) : ℤ) =
      m * ((t : ℤ) ^ 2 + (u : ℤ) ^ 2 + (v : ℤ) ^ 2 + (w : ℤ) ^ 2) +
        ((2 : ℤ) - m) * ((t : ℤ) + (u : ℤ) + (v : ℤ) + (w : ℤ)) := by
  have hs2 : 2 ≤ s := le_trans (by decide : (2 : ℕ) ≤ 3) hs
  -- Remove the `let` binder.
  dsimp
  -- Expand the LHS into a sum of the four `2*polygonal` terms (still in `ℤ`).
  have hlhs :
      (2 * (polygonal s t + polygonal s u + polygonal s v + polygonal s w) : ℤ) =
        (2 * polygonal s t : ℤ) + (2 * polygonal s u : ℤ) +
          (2 * polygonal s v : ℤ) + (2 * polygonal s w : ℤ) := by
    -- Do it in `ℕ`, then cast.
    have : 2 * (polygonal s t + polygonal s u + polygonal s v + polygonal s w) =
        (2 * polygonal s t) + (2 * polygonal s u) + (2 * polygonal s v) + (2 * polygonal s w) := by
      -- `simp` knows `2*(a+b)=2a+2b` via `Nat.mul_add`.
      simp [Nat.mul_add, Nat.add_assoc]
    exact_mod_cast this
  -- Rewrite each `2*polygonal` using the quadratic closed form, then `ring`.
  have ht := two_mul_polygonal_int s t hs2
  have hu := two_mul_polygonal_int s u hs2
  have hv := two_mul_polygonal_int s v hs2
  have hw := two_mul_polygonal_int s w hs2
  -- Now finish by commutative ring algebra.
  -- (We keep the statement in `ℤ` to avoid truncated subtraction in `ℕ`.)
  -- Note: `ring` can handle the resulting polynomial identity.
  simp [hlhs] at *
  rw [ht, hu, hv, hw]
  ring

end PolygonalNumberTheorem
