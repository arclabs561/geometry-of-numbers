import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Set.Countable
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Covolume.Legendre.Exceptions
import Covolume.Legendre.AnkenyLemmas
import Covolume.NumberTheory.Utils

namespace Covolume

open MeasureTheory MeasureTheory.Measure Set Module Matrix
open scoped NNReal ENNReal BigOperators Matrix
open scoped NumberTheorySymbols

/-! We work in `ℝ^3` as `Fin 3 → ℝ`, which matches Mathlib’s `volume` conventions. -/
abbrev E3 := (Fin 3 → ℝ)

/-!
## The “computable covolume” kernel for the Ankeny lattice

In Ankeny’s proof we want a full-rank ℤ-lattice inside `E3` with *explicitly computable covolume*.

Rather than trying to compute the covolume of the congruence-defined lattice `ankeny_lattice` directly,
we build an explicit ℤ-span lattice from a concrete ℝ-basis and compute the fundamental-domain volume via
`ZSpan.volume_fundamentalDomain` (determinant).
-/

/-- A concrete ℝ-basis whose ℤ-span has covolume `2*n*q`.

The associated matrix (with basis vectors as columns) is:

```text
⎡ n    2q   b ⎤
⎢ 0    2q   b ⎥
⎣ 0     0   1 ⎦
```

so `det = 2*n*q`. -/
noncomputable def ankeny_span_matrix (n q : ℕ) (b : ℤ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(n : ℝ), (2 * q : ℝ), (b : ℝ);
    0, (2 * q : ℝ), (b : ℝ);
    0, 0, (1 : ℝ)]

noncomputable def ankeny_span_basis (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Module.Basis (Fin 3) ℝ E3 :=
  let b0 : Module.Basis (Fin 3) ℝ E3 := Pi.basisFun ℝ (Fin 3)
  let A : Matrix (Fin 3) (Fin 3) ℝ := ankeny_span_matrix n q b
  have hdet : A.det ≠ 0 := by
    -- The matrix is upper triangular with diagonal entries `n`, `2q`, `1`.
    -- (The `b`-entries do not affect the determinant.)
    have hA : A.det = (2 * n * q : ℝ) := by
      -- Explicit 3×3 determinant expansion.
      simp [A, ankeny_span_matrix, Matrix.det_fin_three]
      ring_nf
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    -- Show `2 * (n : ℝ) * (q : ℝ) ≠ 0` by contradiction.
    intro hzero
    have hmul : (2 : ℝ) * (n : ℝ) * (q : ℝ) = 0 := by
      -- rewrite the goal `A.det = 0` into `2*n*q = 0`
      -- (and normalize the multiplication order/associativity).
      have : (2 * n * q : ℝ) = 0 := by simpa [hA] using hzero
      simpa [mul_assoc, mul_left_comm, mul_comm] using this
    have h' : (2 : ℝ) * (n : ℝ) = 0 ∨ (q : ℝ) = 0 := by
      -- reassociate to apply `mul_eq_zero`.
      have : ((2 : ℝ) * (n : ℝ)) * (q : ℝ) = 0 := by simpa [mul_assoc] using hmul
      exact mul_eq_zero.mp this
    cases h' with
    | inl h2n =>
        have : (2 : ℝ) = 0 ∨ (n : ℝ) = 0 := mul_eq_zero.mp h2n
        cases this with
        | inl h2 =>
            have : (2 : ℝ) ≠ 0 := by norm_num
            exact (this h2).elim
        | inr hn' => exact hn0 hn'
    | inr hq' =>
        exact hq0 hq'
  b0.map (Matrix.toLinearEquiv b0 A (isUnit_iff_ne_zero.mpr hdet))

lemma ankeny_span_basis_matrixOf (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Matrix.of (ankeny_span_basis n q b hn hq) = (ankeny_span_matrix n q b)ᵀ := by
  classical
  ext i j
  -- `Matrix.of` sees the basis vectors as rows (index first), hence the transpose here.
  simp [ankeny_span_basis, ankeny_span_matrix, Module.Basis.map_apply, Matrix.toLinearEquiv, Matrix.of_apply,
    Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Pi.basisFun_apply,
    Matrix.transpose_apply]

lemma ankeny_span_basis_apply (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) (i j : Fin 3) :
    ankeny_span_basis n q b hn hq i j = ankeny_span_matrix n q b j i := by
  have hM := ankeny_span_basis_matrixOf n q b hn hq
  have := congrArg (fun M => M i j) hM
  simpa [Matrix.of_apply, Matrix.transpose_apply] using this

/-- The explicit ℤ-span lattice used for the covolume computation. -/
noncomputable def ankeny_span_lattice (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    AddSubgroup E3 :=
  (Submodule.span ℤ (Set.range (ankeny_span_basis n q b hn hq))).toAddSubgroup

/-- A canonical fundamental domain for the span lattice. -/
noncomputable def ankeny_span_fundamentalDomain (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    Set E3 :=
  ZSpan.fundamentalDomain (ankeny_span_basis n q b hn hq)

lemma ankeny_span_isAddFundamentalDomain (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    IsAddFundamentalDomain (ankeny_span_lattice n q b hn hq)
      (ankeny_span_fundamentalDomain n q b hn hq) volume := by
  simpa [ankeny_span_lattice, ankeny_span_fundamentalDomain] using
    (ZSpan.isAddFundamentalDomain' (ankeny_span_basis n q b hn hq) volume)

lemma ankeny_span_volume_fundamentalDomain (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    volume (ankeny_span_fundamentalDomain n q b hn hq) = (2 * n * q : ℝ≥0∞) := by
  classical
  let B : Module.Basis (Fin 3) ℝ E3 := ankeny_span_basis n q b hn hq
  let A : Matrix (Fin 3) (Fin 3) ℝ := ankeny_span_matrix n q b
  have hvol :
      volume (ankeny_span_fundamentalDomain n q b hn hq) =
        ENNReal.ofReal |(Matrix.of B).det| := by
    simpa [ankeny_span_fundamentalDomain, B] using (ZSpan.volume_fundamentalDomain B)
  have hB : Matrix.of B = Aᵀ := by
    simpa [A, B] using (ankeny_span_basis_matrixOf n q b hn hq)
  have hdetA : A.det = (2 * n * q : ℝ) := by
    simp [A, ankeny_span_matrix, Matrix.det_fin_three]
    ring_nf
  have hdetB : (Matrix.of B).det = (2 * n * q : ℝ) := by
    calc
      (Matrix.of B).det = (Aᵀ).det := by simp [hB]
      _ = A.det := by simpa using (Matrix.det_transpose A)
      _ = (2 * n * q : ℝ) := hdetA
  have hnonneg : 0 ≤ (2 * n * q : ℝ) := by
    nlinarith
  -- Convert `ENNReal.ofReal |det|` to an `ℝ≥0∞` nat-cast.
  calc
    volume (ankeny_span_fundamentalDomain n q b hn hq)
        = ENNReal.ofReal |(Matrix.of B).det| := hvol
    _ = ENNReal.ofReal (2 * n * q : ℝ) := by simp [hdetB, abs_of_nonneg hnonneg]
    _ = (2 * n * q : ℝ≥0∞) := by simp [ENNReal.ofReal_natCast]

/-- Existence of the Ankeny prime `q`. -/
lemma exists_ankeny_prime (n : ℕ) (hn : n % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ (q : ZMod n) = - (2 : ZMod n)⁻¹ := by
  classical
  have hn_odd : Odd n := Covolume.NumberTheory.odd_of_mod8_eq3 hn
  have hn0 : n ≠ 0 := by
    intro h0
    subst h0
    simpa using hn

  -- Combine the two congruence conditions into a single residue class modulo `4*n`.
  have hcop2 : Nat.Coprime 2 n := Nat.coprime_two_left.2 hn_odd
  have hcop4 : Nat.Coprime 4 n := by
    -- `Coprime (2^2) n ↔ Coprime 2 n`
    have : Nat.Coprime (2 ^ 2) n :=
      (Nat.coprime_pow_left_iff (n := 2) (by decide : 0 < 2) 2 n).2 hcop2
    simpa using this

  let a0 : ZMod n := - (2 : ZMod n)⁻¹
  let e : ZMod (4 * n) ≃+* ZMod 4 × ZMod n := ZMod.chineseRemainder hcop4
  let a : ZMod (4 * n) := e.symm (1, a0)

  -- `a` is a unit because its CRT components are units.
  have ha0 : IsUnit a0 := by
    -- `2` is a unit in `ZMod n` when `n` is odd, hence so is `-(2)⁻¹`.
    have h2 : IsUnit (2 : ZMod n) := Covolume.NumberTheory.zmod_isUnit_two_of_odd n hn_odd
    rcases h2 with ⟨u2, hu2⟩
    have hinv : IsUnit ((2 : ZMod n)⁻¹) := by
      refine ⟨u2⁻¹, ?_⟩
      -- `↑(u2⁻¹) = (↑u2)⁻¹`
      have : ((↑(u2⁻¹) : ZMod n)) = ((u2 : (ZMod n)ˣ) : ZMod n)⁻¹ := by simp
      simpa [hu2] using this
    simpa [a0] using hinv.neg

  have ha_pair : IsUnit ((1 : ZMod 4), a0) := by
    rcases ha0 with ⟨u0, hu0⟩
    refine ⟨
      { val := ((1 : ZMod 4), (u0 : ZMod n))
        inv := ((1 : ZMod 4), (↑(u0⁻¹) : ZMod n))
        val_inv := by ext <;> simp
        inv_val := by ext <;> simp }, ?_⟩
    -- show the unit value is exactly `(1, a0)`
    simpa [hu0]

  have ha : IsUnit a := by
    -- `e.symm` is a ring hom, so it maps units to units.
    simpa [a] using (e.symm.toRingHom.isUnit_map ha_pair)

  -- Apply Dirichlet: infinitely many primes in the residue class `a (mod 4*n)`.
  have hQ0 : (4 * n) ≠ 0 := Nat.mul_ne_zero (by decide) hn0
  haveI : NeZero (4 * n) := ⟨hQ0⟩
  obtain ⟨q, _hq_gt, hq_prime, hq_eq⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * n) (a := a) ha 0

  -- Project back to `ZMod 4` and `ZMod n` to read off the two conditions.
  have hpair : e (q : ZMod (4 * n)) = ((1 : ZMod 4), a0) := by
    -- apply `e` to `hq_eq : (q : ZMod (4*n)) = a`
    have := congrArg e hq_eq
    simpa [a] using this

  have hq_mod4 : (q : ZMod 4) = 1 := by
    -- first component of the pair equality
    have := congrArg Prod.fst hpair
    simpa [e] using this
  have hq_modn : (q : ZMod n) = a0 := by
    have := congrArg Prod.snd hpair
    simpa [e] using this

  have hq_mod4_nat : q % 4 = 1 := by
    -- compare `val` in `ZMod 4`
    have : (q : ZMod 4).val = (1 : ZMod 4).val := congrArg ZMod.val hq_mod4
    -- `val (q : ZMod 4) = q % 4` and `val 1 = 1`
    simpa [ZMod.val_natCast] using this

  refine ⟨q, hq_prime, hq_mod4_nat, ?_⟩
  simpa [a0] using hq_modn

/-- Existence of `b` such that `b² ≡ -n (mod 4q)`. -/
lemma exists_ankeny_b (n q : ℕ) (hn : n % 8 = 3) (hq : Nat.Prime q) (hq1 : q % 4 = 1)
    (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) :
    ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (4 * q)] := by
  classical
  have hn_odd : Odd n := Covolume.NumberTheory.odd_of_mod8_eq3 hn
  have hn0 : n ≠ 0 := by
    intro h0; subst h0
    simpa using hn

  have hq_odd : Odd q := by
    -- `q % 4 = 1` rules out `q = 2`, hence `q` is odd.
    have hq_ne2 : q ≠ 2 := by
      intro hq2; subst hq2
      simp at hq1
    exact hq.odd_of_ne_two hq_ne2

  have hcop4q : Nat.Coprime 4 q := by
    -- `q` odd implies `Coprime 4 q`.
    exact (Nat.coprime_pow_left_iff (n := 2) (by decide : 0 < 2) 2 q).2 (Nat.coprime_two_left.2 hq_odd)

  -- Step 1: compute `J(q | n)` from the congruence `2*q ≡ -1 (mod n)`.
  have h2q_mod_n : (2 * (q : ℤ)) ≡ (-1 : ℤ) [ZMOD n] :=
    Covolume.NumberTheory.two_mul_int_modEq_neg_one_of_q_eq_neg_inv_two n q hn_odd hq_mod

  have hJ_2q : J(2 * (q : ℤ) | n) = J(-1 | n) := by
    -- Jacobi symbol depends only on the numerator mod `n`.
    refine jacobiSym.mod_left' (a₁ := (2 * (q : ℤ))) (a₂ := (-1 : ℤ)) (b := n) ?_
    simpa using h2q_mod_n.eq

  have hn4 : n % 4 = 3 := by omega

  have hJ_neg_one : J(-1 | n) = (-1 : ℤ) := by
    -- `J(-1 | n) = χ₄ n = -1` since `n % 4 = 3`.
    calc
      J(-1 | n) = ZMod.χ₄ n := jacobiSym.at_neg_one hn_odd
      _ = (-1 : ℤ) := ZMod.χ₄_nat_three_mod_four hn4

  have hJ_two : J(2 | n) = (-1 : ℤ) := by
    -- `J(2 | n) = χ₈ n = -1` since `n % 8 = 3`.
    calc
      J(2 | n) = ZMod.χ₈ n := jacobiSym.at_two hn_odd
      _ = (-1 : ℤ) := by
        -- Reduce to the explicit value at `n % 8 = 3`.
        have hred : ZMod.χ₈ n = ZMod.χ₈ (n % 8 : ℕ) := by
          simpa using (ZMod.χ₈_nat_mod_eight n)
        -- `χ₈ 3 = -1` by the definition of `χ₈ : MulChar (ZMod 8) ℤ`.
        have hval : ZMod.χ₈ (3 : ℕ) = (-1 : ℤ) := by decide
        simpa [hred, hn] using hval

  have hJ_q : J((q : ℤ) | n) = (1 : ℤ) := by
    -- From `J(2*q|n) = J(2|n)*J(q|n)` and the computed values, solve for `J(q|n)`.
    have hmul : J((2 : ℤ) * (q : ℤ) | n) = J(2 | n) * J((q : ℤ) | n) := jacobiSym.mul_left 2 q n
    have : J(2 | n) * J((q : ℤ) | n) = (-1 : ℤ) := by
      -- rewrite the LHS as `J(2*q|n)` then use the mod-`n` identification.
      have : J((2 : ℤ) * (q : ℤ) | n) = (-1 : ℤ) := by simpa [mul_assoc] using (hJ_2q.trans hJ_neg_one)
      simpa [hmul] using this
    -- `(-1) * J(q|n) = (-1)` implies `J(q|n) = 1`.
    -- We use the computed value `J(2|n) = -1`.
    have : (-1 : ℤ) * J((q : ℤ) | n) = (-1 : ℤ) := by simpa [hJ_two] using this
    -- cancel `(-1)`
    simpa using (mul_left_cancel₀ (by decide : (-1 : ℤ) ≠ 0) this)

  -- Step 2: Reciprocity transfers `J(q|n)=1` to `J(n|q)=1` since `q % 4 = 1`.
  have hJ_nq : J((n : ℤ) | q) = (1 : ℤ) := by
    have := jacobiSym.quadratic_reciprocity_one_mod_four (a := q) (b := n) hq1 hn_odd
    -- `this : J(q|n) = J(n|q)`
    simpa using (this ▸ hJ_q)

  -- Step 3: Turn `J(-n | q) = 1` into an actual square root in `ZMod q`.
  haveI : Fact q.Prime := ⟨hq⟩
  have hJ_negn : J(-(n : ℤ) | q) = 1 := by
    -- `J(-n|q) = χ₄ q * J(n|q)`; for `q % 4 = 1`, `χ₄ q = 1`.
    have hχ4 : ZMod.χ₄ q = (1 : ℤ) := ZMod.χ₄_nat_one_mod_four hq1
    calc
      J(-(n : ℤ) | q) = ZMod.χ₄ q * J((n : ℤ) | q) := jacobiSym.neg (a := (n : ℤ)) (hb := hq_odd)
      _ = 1 := by simp [hχ4, hJ_nq]

  have hsq_q : IsSquare (-(n : ZMod q)) := by
    -- `ZMod.isSquare_of_jacobiSym_eq_one` returns `IsSquare ((-(n:ℤ)) : ZMod q)`;
    -- rewrite the integer cast using `Int.cast_neg` / `Int.cast_natCast`.
    simpa [Int.cast_neg, Int.cast_natCast] using
      (ZMod.isSquare_of_jacobiSym_eq_one (p := q) (a := (-(n : ℤ))) hJ_negn)
  rcases hsq_q with ⟨r, hr⟩

  -- Step 4: Lift the square root mod `q` to a square root mod `4*q` via CRT.
  have hnZ4 : (n : ZMod 4) = (3 : ZMod 4) := by
    -- `n % 4 = 3` ↔ `n ≡ 3 [MOD 4]`.
    have : n ≡ 3 [MOD 4] := by
      -- `Nat.ModEq` is definitional equality of remainders
      dsimp [Nat.ModEq]
      simpa [hn4]
    exact (ZMod.natCast_eq_natCast_iff n 3 4).2 this
  have hmod4 : ((1 : ZMod 4) ^ 2) = (-(n : ZMod 4)) := by
    -- `-(3) = 1` in `ZMod 4`.
    -- Use the explicit `n = 3` fact to reduce to a decidable finite check.
    have : ((1 : ZMod 4) ^ 2) = (-(3 : ZMod 4)) := by decide
    simpa [hnZ4] using this

  let e : ZMod (4 * q) ≃+* ZMod 4 × ZMod q := ZMod.chineseRemainder hcop4q
  let bZ : ZMod (4 * q) := e.symm ((1 : ZMod 4), r)

  have hbZ : bZ ^ 2 = (-(n : ℤ) : ZMod (4 * q)) := by
    apply e.injective
    ext
    · -- mod 4 component
      -- `e bZ = (1, r)`, so the first component is `1^2 = -n` in `ZMod 4`.
      have : ((1 : ZMod 4) ^ 2) = (-(n : ZMod 4)) := hmod4
      simpa [bZ] using this
    · -- mod q component
      -- `hr : -(n : ZMod q) = r*r`.
      have : (r ^ 2) = (-(n : ZMod q)) := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hr.symm
      -- cast `-(n : ZMod q)` as `((-(n : ℤ)) : ZMod q)` to match `e`'s component.
      simpa [bZ, Int.cast_neg, Int.cast_natCast] using this

  -- Convert the equality in `ZMod (4*q)` into an `Int.ModEq` witness.
  rcases ZMod.intCast_surjective bZ with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  have hbZ' : ((b : ZMod (4 * q)) ^ 2) = (-(n : ℤ) : ZMod (4 * q)) := by simpa [hb] using hbZ
  -- Turn equality in `ZMod` into `Int.ModEq`.
  exact (ZMod.intCast_eq_intCast_iff (b ^ 2) (-(n : ℤ)) (4 * q)).1 (by
    simpa [Int.cast_pow, pow_two] using hbZ')

/-- The Ankeny lattice `L = { (x,y,z) : x ≡ y (mod n), y ≡ bz (mod 2q) }`. -/
def ankeny_lattice (n q : ℕ) (b : ℤ) : AddSubgroup (Fin 3 → ℝ) where
  carrier := { p | ∃ x y z : ℤ, p 0 = x ∧ p 1 = y ∧ p 2 = z ∧ x ≡ y [ZMOD n] ∧ y ≡ b * z [ZMOD (2 * q)] }
  add_mem' := by
    intro a a' ⟨x1, y1, z1, hx1, hy1, hz1, hxy1, hybz1⟩ ⟨x2, y2, z2, hx2, hy2, hz2, hxy2, hybz2⟩
    refine ⟨x1 + x2, y1 + y2, z1 + z2, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hx1, hx2]
    · simp [hy1, hy2]
    · simp [hz1, hz2]
    · exact hxy1.add hxy2
    · calc (y1 + y2 : ℤ) ≡ b * z1 + b * z2 [ZMOD (2 * q)] := hybz1.add hybz2
        _ = b * (z1 + z2) := by ring
  zero_mem' := by
    refine ⟨0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Int.ModEq.refl]
  neg_mem' := by
    intro a ⟨x, y, z, hx, hy, hz, hxy, hybz⟩
    use -x, -y, -z
    constructor; simp [hx]
    constructor; simp [hy]
    constructor; simp [hz]
    constructor; exact hxy.neg
    calc (-y : ℤ) ≡ -(b * z) [ZMOD (2 * q)] := hybz.neg
      _ = b * (-z) := by ring

/-- Arithmetic glue: the explicit covolume lattice is a sublattice of the congruence-defined Ankeny lattice. -/
lemma ankeny_span_lattice_subset_ankeny_lattice (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    (ankeny_span_lattice n q b hn hq : Set E3) ⊆ ankeny_lattice n q b := by
  classical
  intro p hp
  -- Work in the underlying ℤ-submodule `span ℤ (range basis)`.
  let B : Module.Basis (Fin 3) ℝ E3 := ankeny_span_basis n q b hn hq
  have hp' : p ∈ (Submodule.span ℤ (Set.range B) : Set E3) := by
    simpa [ankeny_span_lattice, B] using hp
  -- It suffices to show `span ℤ (range B) ≤ (ankeny_lattice ...).toIntSubmodule`.
  have hle :
      (Submodule.span ℤ (Set.range B)) ≤ (ankeny_lattice n q b).toIntSubmodule := by
    refine Submodule.span_le.2 ?_
    intro x hx
    rcases hx with ⟨i, rfl⟩
    -- Show each basis vector satisfies the defining congruences.
    fin_cases i
    · -- i = 0: vector `(n, 0, 0)`
      have hx0 : (B 0) 0 = (n : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (0 : Fin 3) 0)
      have hx1 : (B 0) 1 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (0 : Fin 3) 1)
      have hx2 : (B 0) 2 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (0 : Fin 3) 2)
      have hxy : (n : ℤ) ≡ (0 : ℤ) [ZMOD n] := by
        refine (Int.modEq_iff_dvd).2 ?_
        simp
      have hybz : (0 : ℤ) ≡ b * (0 : ℤ) [ZMOD (2 * q)] := by
        simpa using (Int.ModEq.refl (0 : ℤ))
      have : (B 0) ∈ ankeny_lattice n q b := by
        refine ⟨(n : ℤ), 0, 0, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
    · -- i = 1: vector `(2q, 2q, 0)`
      have hx0 : (B 1) 0 = (2 * q : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (1 : Fin 3) 0)
      have hx1 : (B 1) 1 = (2 * q : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (1 : Fin 3) 1)
      have hx2 : (B 1) 2 = (0 : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (1 : Fin 3) 2)
      have hxy : (2 * q : ℤ) ≡ (2 * q : ℤ) [ZMOD n] := by
        simpa using (Int.ModEq.refl (2 * q : ℤ))
      have hybz : (2 * q : ℤ) ≡ b * (0 : ℤ) [ZMOD (2 * q)] := by
        -- `2q ≡ 0 (mod 2q)`
        refine (Int.modEq_iff_dvd).2 ?_
        simp
      have : (B 1) ∈ ankeny_lattice n q b := by
        refine ⟨(2 * q : ℤ), (2 * q : ℤ), 0, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
    · -- i = 2: vector `(b, b, 1)`
      have hx0 : (B 2) 0 = (b : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (2 : Fin 3) 0)
      have hx1 : (B 2) 1 = (b : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (2 : Fin 3) 1)
      have hx2 : (B 2) 2 = (1 : ℝ) := by
        simpa [B, ankeny_span_matrix] using (ankeny_span_basis_apply n q b hn hq (2 : Fin 3) 2)
      have hxy : b ≡ b [ZMOD n] := by
        simpa using (Int.ModEq.refl b)
      have hybz : b ≡ b * (1 : ℤ) [ZMOD (2 * q)] := by
        simpa using (Int.ModEq.refl b)
      have : (B 2) ∈ ankeny_lattice n q b := by
        refine ⟨b, b, 1, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hx0]
        · simp [hx1]
        · simp [hx2]
        · exact hxy
        · simpa using hybz
      simpa [AddSubgroup.coe_toIntSubmodule] using this
  -- Conclude from `hle` and `hp'`.
  have : p ∈ (ankeny_lattice n q b).toIntSubmodule := hle hp'
  -- Convert `toIntSubmodule` membership back to set membership.
  simpa [AddSubgroup.coe_toIntSubmodule] using this

/-- A convenient full-rank ℤ-lattice for Ankeny has covolume `2nq`. -/
lemma ankeny_lattice_covolume (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    ∃ (L : AddSubgroup (Fin 3 → ℝ)) (F : Set (Fin 3 → ℝ)),
      IsAddFundamentalDomain L F volume ∧ 
      volume F = (2 * n * q : ℝ≥0∞) ∧ 
      (L : Set (Fin 3 → ℝ)).Countable ∧ 
      (L : Set (Fin 3 → ℝ)) ⊆ ankeny_lattice n q b := by
  classical
  let L : AddSubgroup E3 := ankeny_span_lattice n q b hn hq
  let F : Set E3 := ankeny_span_fundamentalDomain n q b hn hq
  refine ⟨L, F, ?_, ?_, ?_, ?_⟩
  · simpa [L, F] using ankeny_span_isAddFundamentalDomain n q b hn hq
  · simpa [F] using ankeny_span_volume_fundamentalDomain n q b hn hq
  · -- Countability of the ℤ-span lattice.
    have : Countable (↥L) := by
      -- `L` is a `Submodule.span ℤ` of a finite `Set.range`, hence countable.
      change Countable (Submodule.span ℤ (Set.range (ankeny_span_basis n q b hn hq)))
      infer_instance
    -- Convert subtype-countability into set-countability.
    have hrange : (Set.range (fun x : (↥L) => (x : E3))) = (L : Set E3) := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    simpa [hrange] using (Set.countable_range (fun x : (↥L) => (x : E3)))
  · -- Inclusion into the congruence-defined lattice is the arithmetic glue step.
    simpa [L] using ankeny_span_lattice_subset_ankeny_lattice n q b hn hq

/-- The quadratic form `Q = 2qx² + y² + nz²`. -/
def ankeny_Q (n q : ℕ) (x y z : ℤ) : ℤ := 2 * q * x^2 + y^2 + n * z^2

/-- Any point in the Ankeny lattice satisfies `Q ≡ 0 (mod 2nq)`. -/
lemma ankeny_Q_mod (n q : ℕ) (b : ℤ) (x y z : ℤ)
    (hn : n % 8 = 3)
    (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (hxy : x ≡ y [ZMOD n])
    (hybz : y ≡ b * z [ZMOD (2 * q)])
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (2 * q)]) :
    ankeny_Q n q x y z ≡ 0 [ZMOD (2 * n * q)] := by
  -- This lemma is the “algebraic glue” used after the Minkowski step:
  --
  -- - mod `n`: use `x ≡ y` and `2q ≡ -1` (from `hq_mod`)
  -- - mod `2q`: use `y ≡ b z` and `b^2 ≡ -n` (from `hb`)
  -- - combine by CRT (since `gcd(n,2q)=1` in the Ankeny setup)
  --
  -- We start by proving the mod-`2q` part, since it is self-contained.
  have hQ_mod_2q : ankeny_Q n q x y z ≡ 0 [ZMOD (2 * q : ℤ)] := by
    have hy2 : y ^ 2 ≡ (b * z) ^ 2 [ZMOD (2 * q : ℤ)] := hybz.pow 2
    have hy2' : y ^ 2 ≡ b ^ 2 * z ^ 2 [ZMOD (2 * q : ℤ)] := by
      -- `(b*z)^2 = b^2 * z^2`
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hy2
    have hb_mul : b ^ 2 * z ^ 2 ≡ (-(n : ℤ)) * z ^ 2 [ZMOD (2 * q : ℤ)] :=
      Int.ModEq.mul_right (z ^ 2) hb
    have hsum_cancel : (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 = 0 := by ring
    have hy_nz : y ^ 2 + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (2 * q : ℤ)] := by
      have h1 : y ^ 2 + (n : ℤ) * z ^ 2 ≡ b ^ 2 * z ^ 2 + (n : ℤ) * z ^ 2 [ZMOD (2 * q : ℤ)] :=
        (hy2'.add (Int.ModEq.refl _))
      have h2 : b ^ 2 * z ^ 2 + (n : ℤ) * z ^ 2 ≡ (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 [ZMOD (2 * q : ℤ)] :=
        (hb_mul.add (Int.ModEq.refl _))
      have h3 : (-(n : ℤ)) * z ^ 2 + (n : ℤ) * z ^ 2 ≡ 0 [ZMOD (2 * q : ℤ)] := by
        simpa [hsum_cancel] using (Int.ModEq.refl (0 : ℤ))
      exact h1.trans (h2.trans h3)
    -- The `2q*x^2` term is 0 modulo `2q`.
    have h2qxx : (2 * (q : ℤ)) * x ^ 2 ≡ 0 [ZMOD (2 * q : ℤ)] := by
      refine (Int.modEq_zero_iff_dvd).2 ?_
      exact dvd_mul_right (2 * (q : ℤ)) (x ^ 2)
    -- Assemble.
    have : (2 * (q : ℤ)) * x ^ 2 + (y ^ 2 + (n : ℤ) * z ^ 2) ≡ 0 [ZMOD (2 * q : ℤ)] := by
      simpa [add_assoc, add_comm, add_left_comm] using (h2qxx.add hy_nz)
    simpa [ankeny_Q, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this

  -- Step 2: the mod-`n` part. This is where `hq_mod` is used to derive `2q ≡ -1 (mod n)`.
  have hnodd : Odd n := Covolume.NumberTheory.odd_of_mod8_eq3 hn
  have h2unit : IsUnit (2 : ZMod n) := Covolume.NumberTheory.zmod_isUnit_two_of_odd n hnodd
  have hqunit : IsUnit (q : ZMod n) := by
    have h2inv : IsUnit ((2 : ZMod n)⁻¹) := by
      -- `ZMod.isUnit_inv` is the correct lemma here (since `ZMod n` is not a division monoid).
      simpa using (ZMod.isUnit_inv (m := n) (n := (2 : ℤ)) (by simpa using h2unit))
    have : IsUnit (-( (2 : ZMod n)⁻¹)) := IsUnit.neg h2inv
    simpa [hq_mod] using this
  have hnq : Nat.Coprime q n :=
    (ZMod.isUnit_iff_coprime q n).1 (by simpa using hqunit)
  have hncoprime : Nat.Coprime n (2 * q) := by
    have hn2 : Nat.Coprime n 2 := (Nat.coprime_two_right.2 hnodd)
    have hnq' : Nat.Coprime n q := (Nat.coprime_comm.1 hnq)
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (hn2.mul_right hnq')
  have hmn : (n : ℤ).natAbs.Coprime (2 * q : ℤ).natAbs := by
    simpa using hncoprime

  have h2q_add_one_dvd : (n : ℤ) ∣ (2 * (q : ℤ) + 1) := by
    -- In `ZMod n`, `2*q + 1 = 0`.
    have hZ : ((2 * (q : ℤ) + 1 : ℤ) : ZMod n) = 0 := by
      -- `q = -(2)⁻¹` ⇒ `2*q = -1` ⇒ `2*q + 1 = 0`
      have h2q : (2 : ZMod n) * (q : ZMod n) = (-1 : ZMod n) := by
        calc
          (2 : ZMod n) * (q : ZMod n)
              = (2 : ZMod n) * (-(2 : ZMod n)⁻¹) := by simpa [hq_mod]
          _ = -((2 : ZMod n) * (2 : ZMod n)⁻¹) := by ring
          _ = (-1 : ZMod n) := by
            have h : (2 : ZMod n) * (2 : ZMod n)⁻¹ = (1 : ZMod n) :=
              ZMod.mul_inv_of_unit (2 : ZMod n) h2unit
            simpa [h]
      -- Convert `2*q = -1` to `2*q + 1 = 0`.
      have : (2 : ZMod n) * (q : ZMod n) + 1 = 0 := by
        calc
          (2 : ZMod n) * (q : ZMod n) + 1 = (-1 : ZMod n) + 1 := by simpa [h2q]
          _ = 0 := by simp
      -- Rewrite into the exact `ℤ`-cast form used below.
      simpa [two_mul, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * (q : ℤ) + 1) n).1 hZ

  have hQ_mod_n : ankeny_Q n q x y z ≡ 0 [ZMOD (n : ℤ)] := by
    have hx2 : x ^ 2 ≡ y ^ 2 [ZMOD (n : ℤ)] := hxy.pow 2
    have hmul : (2 * (q : ℤ)) * (x ^ 2) ≡ (2 * (q : ℤ)) * (y ^ 2) [ZMOD (n : ℤ)] :=
      Int.ModEq.mul_left _ hx2
    have hQ' :
        ankeny_Q n q x y z ≡ (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2) [ZMOD (n : ℤ)] := by
      have hadd :
          (2 * (q : ℤ)) * (x ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2)
            ≡ (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2) [ZMOD (n : ℤ)] :=
        (hmul.add (Int.ModEq.refl _)).add (Int.ModEq.refl _)
      simpa [ankeny_Q, pow_two, mul_assoc, mul_left_comm, mul_comm, add_assoc, add_left_comm, add_comm] using hadd
    have h2q1 : (2 * (q : ℤ) + 1) ≡ 0 [ZMOD (n : ℤ)] :=
      (Int.modEq_zero_iff_dvd).2 h2q_add_one_dvd
    have hnz : (n : ℤ) * (z ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      refine (Int.modEq_zero_iff_dvd).2 ?_
      exact dvd_mul_right (n : ℤ) (z ^ 2)
    have hlin : (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) = (2 * (q : ℤ) + 1) * (y ^ 2) := by ring
    have hfirst : (2 * (q : ℤ) + 1) * (y ^ 2) ≡ 0 [ZMOD (n : ℤ)] :=
      by
        simpa using (Int.ModEq.mul_right (y ^ 2) h2q1)
    have : (2 * (q : ℤ)) * (y ^ 2) + (y ^ 2) + (n : ℤ) * (z ^ 2) ≡ 0 [ZMOD (n : ℤ)] := by
      simpa [hlin] using (hfirst.add hnz)
    exact hQ'.trans this

  -- Step 3: combine the mod-`n` and mod-`2q` statements.
  have hcrt : ankeny_Q n q x y z ≡ 0 [ZMOD (n : ℤ) * (2 * q : ℤ)] :=
    (Int.modEq_and_modEq_iff_modEq_mul hmn).1 ⟨hQ_mod_n, hQ_mod_2q⟩
  -- Normalize the modulus `(n : ℤ) * (2*q : ℤ)` to `2*n*q`.
  have hmul_nat : (n : ℤ) * (2 * q : ℤ) = (2 * n * q : ℤ) := by ring
  simpa [hmul_nat] using hcrt

/-- Minkowski application: there exists a representation `2qx² + y² + nz² = 2nq`. -/
lemma exists_ankeny_representation (n q : ℕ) (b : ℤ) (hn : n % 8 = 3) (hq : Nat.Prime q)
    (hq1 : q % 4 = 1) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (4 * q)]) :
    ∃ x y z : ℤ, 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q ∧ (x, y, z) ≠ (0, 0, 0) := by
  sorry

/-- Reduction of `2qx² + y² + nz² = 2nq` to `n = x² + u² + v²`.
    Hypothesis `Squarefree n` makes the `p | n` case easier (contradiction via `z^2 ≡ -1`). -/
lemma reduction_to_sum_three_squares (n q : ℕ) (x y z : ℤ)
    (h_ankeny : 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q)
    (hq_prime : Nat.Prime q) (hq1 : q % 4 = 1) (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) 
    (hn : n % 8 = 3) (hn_sq : Squarefree n) :
    ∃ u v : ℤ, n = x^2 + u^2 + v^2 := by
  have h_eq : y^2 + n * z^2 = 2 * q * (n - x^2) := by
    calc y^2 + n * z^2 = (2 * q * x^2 + y^2 + n * z^2) - 2 * q * x^2 := by ring
      _ = 2 * n * q - 2 * q * x^2 := by rw [h_ankeny]
      _ = 2 * q * (n - x^2) := by ring
  
  -- Show n - x^2 >= 0
  have h_diff_nonneg : 0 ≤ n - x^2 := by
    have h_rhs : 0 ≤ y^2 + n * z^2 := by
      apply add_nonneg (sq_nonneg y)
      apply mul_nonneg (Int.natCast_nonneg n) (sq_nonneg z)
    rw [h_eq] at h_rhs
    have h2q : 0 < (2 * q : ℤ) := by
      have hq_pos : 0 < q := hq_prime.pos
      norm_cast; linarith
    exact nonneg_of_mul_nonneg_right h_rhs h2q

  let K := (n - x^2).natAbs
  have hK_eq : (K : ℤ) = n - x^2 := Int.natAbs_of_nonneg h_diff_nonneg
  
  -- Use Nat.eq_sq_add_sq_iff
  suffices ∃ u v : ℕ, K = u ^ 2 + v ^ 2 by
    obtain ⟨u, v, huv⟩ := this
    use (u : ℤ), (v : ℤ)
    sorry -- Setup descent induction

  rw [Nat.eq_sq_add_sq_iff]
  intro p hp_prime_factors hp_mod3
  sorry

/-- Final theorem for `n ≡ 3 (mod 8)`. -/
theorem sum_three_squares_of_three_mod_eight (n : ℕ) (hn : n % 8 = 3) :
    ∃ x y z : ℕ, x^2 + y^2 + z^2 = n := by
  obtain ⟨s, m, hm_eq, hm_sq⟩ := exists_squarefree_part n
  have hm_mod : m % 8 = 3 := squarefree_part_mod_eight n s m hm_eq hn
  obtain ⟨q, hqp, hq1, hq_mod⟩ := exists_ankeny_prime m hm_mod
  have : ∃ b : ℤ, b ^ 2 ≡ - (m : ℤ) [ZMOD (4 * q)] := exists_ankeny_b m q hm_mod hqp hq1 hq_mod
  obtain ⟨b, hb⟩ := this
  obtain ⟨x, y, z, h_rep, h_nz⟩ := exists_ankeny_representation m q b hm_mod hqp hq1 hq_mod hb
  obtain ⟨u, v, h_final⟩ := reduction_to_sum_three_squares m q x y z h_rep hqp hq1 hq_mod hm_mod hm_sq
  use s * x.natAbs, s * u.natAbs, s * v.natAbs
  zify
  -- Keep this simp list minimal to avoid unused-simp-arg warnings.
  simp only [mul_pow, ← mul_add, sq_abs]
  have hm_eq_int : (n : ℤ) = s^2 * m := by exact_mod_cast hm_eq
  rw [← h_final, ← hm_eq_int]
  -- `ring` was previously here, but the goal is already closed after rewriting.

end Covolume
