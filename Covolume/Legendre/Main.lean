import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Covolume.Legendre.Exceptions
import Covolume.Legendre.Ankeny

namespace Covolume

/-!
## Legendre “easy direction”

We prove the modular obstruction:
\[
  x^2 + y^2 + z^2 = n \;\Rightarrow\; n \neq 4^a(8k+7).
\]

Two finite-ring facts drive the proof:

- In `ZMod 4`, `1 + y^2 + z^2 ≠ 0` for all `y,z`. (Checked by `decide`.)
  This implies: if `4 ∣ x^2+y^2+z^2` then `x,y,z` are even, hence we can divide the representation by `4`.

- In `ZMod 8`, `x^2 + y^2 + z^2 ≠ 7` for all `x,y,z`. (Checked by `decide`.)
  This rules out the `8k+7` base case after descending.
-/

private lemma zmod4_sq_eq_one_of_odd (x : ℕ) (hx : Odd x) : ((x : ZMod 4) ^ 2) = 1 := by
  rcases hx with ⟨m, rfl⟩
  -- `(2m+1)^2 = 4*(m*(m+1)) + 1`, and `4 = 0` in `ZMod 4`.
  -- First normalize the coercion `(2*m+1 : ℕ) ↦ ZMod 4`.
  have hcast : ((2 * m + 1 : ℕ) : ZMod 4) = (2 * (m : ZMod 4) + 1) := by
    simp [Nat.cast_add, Nat.cast_mul]
  calc
    (((2 * m + 1 : ℕ) : ZMod 4) ^ 2)
        = ((2 * (m : ZMod 4) + 1) ^ 2) := by simpa [hcast]
    _ = (4 : ZMod 4) * (m : ZMod 4) * ((m : ZMod 4) + 1) + 1 := by ring
    _ = 1 := by
          -- `4 = 0` in `ZMod 4`.
          have h4 : (4 : ZMod 4) = 0 := by
            simpa using (ZMod.natCast_self 4)
          simpa [h4]

private lemma zmod4_one_add_sq_add_sq_ne0 : ∀ y z : ZMod 4, (1 + y ^ 2 + z ^ 2) ≠ 0 := by
  decide

private lemma zmod8_sum_three_sq_ne7 : ∀ x y z : ZMod 8, (x ^ 2 + y ^ 2 + z ^ 2) ≠ 7 := by
  decide

private lemma even_of_sum_three_squares_eq_mul_four {x y z m : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 * m) : Even x ∧ Even y ∧ Even z := by
  -- If any variable is odd, reduce mod 4 and contradict the finite check in `ZMod 4`.
  have hx : Even x := by
    rcases Nat.even_or_odd x with hx | hx
    · exact hx
    · have hx1 : ((x : ZMod 4) ^ 2) = 1 := zmod4_sq_eq_one_of_odd x hx
      have hcast := congrArg (fun n : ℕ => (n : ZMod 4)) h
      -- In `ZMod 4`, `4*m = 0`.
      have h0 : ((x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
      have : (1 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        -- replace `x^2` by `1`
        simpa [hx1, add_assoc, add_left_comm, add_comm] using h0
      exact False.elim ((zmod4_one_add_sq_add_sq_ne0 (y := (y : ZMod 4)) (z := (z : ZMod 4))) this)
  have hy : Even y := by
    rcases Nat.even_or_odd y with hy | hy
    · exact hy
    · have hy1 : ((y : ZMod 4) ^ 2) = 1 := zmod4_sq_eq_one_of_odd y hy
      have hcast := congrArg (fun n : ℕ => (n : ZMod 4)) (by
        simpa [add_assoc, add_left_comm, add_comm] using h)
      have h0 : ((y : ZMod 4) ^ 2 + (x : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
      have : (1 + (x : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2) = 0 := by
        simpa [hy1, add_assoc, add_left_comm, add_comm] using h0
      exact False.elim ((zmod4_one_add_sq_add_sq_ne0 (y := (x : ZMod 4)) (z := (z : ZMod 4))) this)
  have hz : Even z := by
    rcases Nat.even_or_odd z with hz | hz
    · exact hz
    · have hz1 : ((z : ZMod 4) ^ 2) = 1 := zmod4_sq_eq_one_of_odd z hz
      have hcast := congrArg (fun n : ℕ => (n : ZMod 4)) (by
        simpa [add_assoc, add_left_comm, add_comm] using h)
      have h0 : ((z : ZMod 4) ^ 2 + (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2) = 0 := by
        simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
      have : (1 + (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2) = 0 := by
        simpa [hz1, add_assoc, add_left_comm, add_comm] using h0
      exact False.elim ((zmod4_one_add_sq_add_sq_ne0 (y := (x : ZMod 4)) (z := (y : ZMod 4))) this)
  exact ⟨hx, hy, hz⟩

private lemma descend_four {x y z m : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 * m) :
    ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = m := by
  have hev := even_of_sum_three_squares_eq_mul_four (x := x) (y := y) (z := z) (m := m) h
  rcases hev.1 with ⟨x', rfl⟩
  rcases hev.2.1 with ⟨y', rfl⟩
  rcases hev.2.2 with ⟨z', rfl⟩
  -- Factor out the `4` on the LHS and cancel.
  have hfactor :
      (x' + x') ^ 2 + (y' + y') ^ 2 + (z' + z') ^ 2 = 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) := by
    -- expand squares and collect `4`
    simp [pow_two]
    ring
  have hmul : 4 * (x' ^ 2 + y' ^ 2 + z' ^ 2) = 4 * m := by
    calc
      4 * (x' ^ 2 + y' ^ 2 + z' ^ 2)
          = (x' + x') ^ 2 + (y' + y') ^ 2 + (z' + z') ^ 2 := by
                simpa [hfactor] using hfactor.symm
      _ = 4 * m := by simpa using h
  have hcancel : x' ^ 2 + y' ^ 2 + z' ^ 2 = m :=
    Nat.mul_left_cancel (show 0 < 4 from by decide) hmul
  exact ⟨x', y', z', hcancel⟩

private lemma descend_four_pow {a x y z t : ℕ}
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 4 ^ a * t) :
    ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = t := by
  induction a generalizing x y z with
  | zero =>
      refine ⟨x, y, z, ?_⟩
      simpa using h
  | succ a ih =>
      have h' : x ^ 2 + y ^ 2 + z ^ 2 = 4 * (4 ^ a * t) := by
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h
      rcases descend_four (x := x) (y := y) (z := z) (m := 4 ^ a * t) h' with ⟨x1, y1, z1, h1⟩
      exact ih (x := x1) (y := y1) (z := z1) h1

/-- Necessary condition: representation as a sum of three squares implies n is not an exception. -/
theorem not_exception_of_sum_three_squares (n : ℕ) (h : ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) :
    ¬ is_three_square_exception n := by
  rcases h with ⟨x, y, z, hxyz⟩
  intro hex
  rcases hex with ⟨a, k, hn⟩
  -- descend `4^a` to get a representation of `8*k+7`
  have hdesc : ∃ x' y' z' : ℕ, x' ^ 2 + y' ^ 2 + z' ^ 2 = 8 * k + 7 := by
    refine descend_four_pow (a := a) (x := x) (y := y) (z := z) (t := 8 * k + 7) ?_
    simpa [hn, hxyz, mul_assoc, mul_left_comm, mul_comm]
  rcases hdesc with ⟨x', y', z', h'⟩
  -- reduce mod 8 and contradict the finite check in `ZMod 8`
  have hcast := congrArg (fun n : ℕ => (n : ZMod 8)) h'
  have : ((x' : ZMod 8) ^ 2 + (y' : ZMod 8) ^ 2 + (z' : ZMod 8) ^ 2) = (7 : ZMod 8) := by
    -- `8*k` vanishes in `ZMod 8`.
    simpa [pow_two, mul_add, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcast
  exact (zmod8_sum_three_sq_ne7 (x := (x' : ZMod 8)) (y := (y' : ZMod 8)) (z := (z' : ZMod 8))) this

/-- Sufficient condition: n not an exception implies representation as a sum of three squares. -/
theorem sum_three_squares_of_not_exception (n : ℕ) (h : ¬ is_three_square_exception n) :
    ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  /-
  TODO (current):
  This is the “hard direction”. In this repo we route it through Ankeny’s descent pipeline:
  - reduce to the squarefree part `m` with `m % 8 = 3`,
  - choose `q` and `b`,
  - build the lattice, apply Minkowski, get `2*q*x^2 + y^2 + m*z^2 = 2*m*q`,
  - descend to `m = x^2 + u^2 + v^2`, then scale back to `n`.

  TODO:
  - Make this theorem a thin wrapper around `sum_three_squares_of_three_mod_eight` + squarefree-part glue.
  - Keep “Minkowski route” alternative in `Legendre/Minkowski.lean`, but treat Ankeny as canonical.
  -/
  sorry

end Covolume
