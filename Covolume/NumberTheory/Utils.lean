import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Number theory utilities (local to Covolume)

This module collects small “glue lemmas” that show up repeatedly in the Ankeny/Minkowski pipeline:

- converting simple modular facts (e.g. `n % 8 = 3`) into `Odd n`,
- turning `Odd n` into unit/coprime facts in `ZMod n`.

These are intentionally low-level and compositional: they are API building blocks, not theorems.
-/

namespace Covolume.NumberTheory

/-! ## Parity helpers -/

lemma odd_of_mod8_eq3 {n : ℕ} (hn : n % 8 = 3) : Odd n := by
  have : n % 2 = 1 := by omega
  exact Nat.odd_iff.2 this

/-! ## `ZMod` unit/coprime helpers -/

lemma zmod_isUnit_two_of_odd (n : ℕ) (hn : Odd n) : IsUnit (2 : ZMod n) := by
  exact (ZMod.isUnit_iff_coprime 2 n).2 (Nat.coprime_two_left.2 hn)

lemma zmod_isUnit_two_of_mod8_eq3 (n : ℕ) (hn : n % 8 = 3) : IsUnit (2 : ZMod n) :=
  zmod_isUnit_two_of_odd n (odd_of_mod8_eq3 hn)

/-- Cast bridge used repeatedly in the Ankeny pipeline:

If `q = -(2)⁻¹` in `ZMod n` (with `n` odd so `2` is a unit), then
\[
  2q \equiv -1 \pmod n
\]
as an `Int.ModEq` statement. -/
lemma two_mul_int_modEq_neg_one_of_q_eq_neg_inv_two
    (n q : ℕ) (hn : Odd n) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) :
    (2 * (q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] := by
  have h2unit : IsUnit (2 : ZMod n) := zmod_isUnit_two_of_odd n hn
  have hZ : (2 : ZMod n) * (q : ZMod n) = (-1 : ZMod n) := by
    calc
      (2 : ZMod n) * (q : ZMod n)
          = (2 : ZMod n) * (-(2 : ZMod n)⁻¹) := by simp [hq_mod]
      _ = -((2 : ZMod n) * (2 : ZMod n)⁻¹) := by simp [mul_neg]
      _ = (-1 : ZMod n) := by simp [ZMod.mul_inv_of_unit (2 : ZMod n) h2unit]
  have hZ_int : ((2 : ℤ) : ZMod n) * ((q : ℤ) : ZMod n) = (-1 : ZMod n) := by
    simpa using hZ
  have hZ_cast : ((2 : ℤ) * (q : ℤ) : ℤ) ≡ (-1 : ℤ) [ZMOD n] := by
    exact (ZMod.intCast_eq_intCast_iff ((2 : ℤ) * (q : ℤ)) (-1 : ℤ) n).1 (by
      simpa [Int.cast_mul] using hZ_int)
  simpa [mul_assoc, mul_comm, mul_left_comm] using hZ_cast

end Covolume.NumberTheory

