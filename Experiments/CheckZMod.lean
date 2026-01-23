import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.SumTwoSquares

-- Silent API probes (avoid `#check` noise during builds).
private def _probe_cast_natCast := @ZMod.cast_natCast
private def _probe_castHom := @ZMod.castHom
private def _probe_castHom_apply := @ZMod.castHom_apply
private def _probe_cast := @ZMod.cast
private def _probe_intCast_zmod_eq_zero_iff_dvd := @ZMod.intCast_zmod_eq_zero_iff_dvd
private def _probe_modEq_zero_iff_dvd := @Int.modEq_zero_iff_dvd
private def _probe_modEq_iff_dvd := @Int.modEq_iff_dvd
private def _probe_exists_sq_eq_neg_one_iff := @ZMod.exists_sq_eq_neg_one_iff

/-!
Small “bridge” experiments for what `Legendre/Ankeny.lean` needs next.

The key pain point in `ankeny_Q_mod` is moving between:
- equations in `ZMod n`, and
- congruences `Int.ModEq` / `a ≡ b [ZMOD n]`.

This file tries to keep that bridge in a tiny, isolated place.
-/

-- If `n` is odd, then `2` is a unit in `ZMod n`.
example (n : ℕ) (hn2 : n % 2 = 1) : IsUnit (2 : ZMod n) := by
  have hn_odd : Odd n := (Nat.odd_iff).2 hn2
  -- `ZMod.isUnit_iff_coprime` reduces units to gcd/coprime.
  apply (ZMod.isUnit_iff_coprime 2 n).2
  exact (Nat.coprime_two_left).2 hn_odd

-- From `q = -(2)⁻¹` in `ZMod n`, conclude `2*q ≡ -1 [ZMOD n]` as an `Int.ModEq`.
--
-- This is the exact “cast bridge” needed in `ankeny_Q_mod` to derive the mod-n part.
example (n q : ℕ) (hn2 : n % 2 = 1) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) :
    (2 * (q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] := by
  have h2unit : IsUnit (2 : ZMod n) := by
    have hn_odd : Odd n := (Nat.odd_iff).2 hn2
    exact (ZMod.isUnit_iff_coprime 2 n).2 ((Nat.coprime_two_left).2 hn_odd)
  have hZ : (2 : ZMod n) * (q : ZMod n) = (-1 : ZMod n) := by
    -- Multiply `hq_mod` by 2 and use `2 * 2⁻¹ = 1`.
    calc
      (2 : ZMod n) * (q : ZMod n)
          = (2 : ZMod n) * (-(2 : ZMod n)⁻¹) := by simp [hq_mod]
      _ = -((2 : ZMod n) * (2 : ZMod n)⁻¹) := by simp [mul_neg]
      _ = (-1 : ZMod n) := by simp [ZMod.mul_inv_of_unit (2 : ZMod n) h2unit]
  -- Rewrite the same equality using explicit `Int.cast` so we can use `ZMod.intCast_eq_intCast_iff`.
  have hZ_int : ((2 : ℤ) : ZMod n) * ((q : ℤ) : ZMod n) = (-1 : ZMod n) := by
    simpa using hZ
  have hZ_cast : ((2 : ℤ) * (q : ℤ) : ℤ) ≡ (-1 : ℤ) [ZMOD n] := by
    -- `Int.cast_mul` gives: `((2*q : ℤ) : ZMod n) = ...`
    exact (ZMod.intCast_eq_intCast_iff ((2 : ℤ) * (q : ℤ)) (-1 : ℤ) n).1 (by
      simpa [Int.cast_mul] using hZ_int)
  -- Normalize the left side to `2 * (q : ℤ)`.
  simpa [mul_assoc, mul_comm, mul_left_comm] using hZ_cast

-- Combining congruences “CRT-style” (the lemma we want at the end of `ankeny_Q_mod`).
example (a m n : ℤ) (hmn : m.natAbs.Coprime n.natAbs)
    (hm : a ≡ 0 [ZMOD m]) (hn : a ≡ 0 [ZMOD n]) :
    a ≡ 0 [ZMOD m * n] :=
  (Int.modEq_and_modEq_iff_modEq_mul (a := a) (b := 0) (m := m) (n := n) hmn).1 ⟨hm, hn⟩
