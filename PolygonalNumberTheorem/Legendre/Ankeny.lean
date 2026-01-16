import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import PolygonalNumberTheorem.Legendre.Exceptions
import PolygonalNumberTheorem.Legendre.AnkenyLemmas

/-!
# Ankeny's 1957 Proof of Legendre's Three-Squares Theorem

This file implements Ankeny's elementary proof of Legendre's three-squares theorem
using Minkowski's theorem and Dirichlet's theorem on primes in arithmetic progressions.
The proof focuses on the case `n ≡ 3 (mod 8)`, which is the core case for the
Polygonal Number Theorem.
-/

namespace PolygonalNumberTheorem

open MeasureTheory MeasureTheory.Measure Set Module Matrix
open scoped NNReal ENNReal BigOperators Matrix
open scoped NumberTheorySymbols

/-- Existence of the Ankeny prime `q`.
    For `n ≡ 3 (mod 8)`, there exists a prime `q ≡ 1 (mod 4)` such that `q ≡ -1/2 (mod n)`. -/
lemma exists_ankeny_prime (n : ℕ) (hn : n % 8 = 3) :
    ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧ (q : ZMod n) = - (2 : ZMod n)⁻¹ := by
  have hn_odd : n % 2 = 1 := by omega
  let h4n := coprime_four_n n hn_odd
  let a4 : ZMod 4 := 1
  let an : ZMod n := - (2 : ZMod n)⁻¹
  obtain ⟨a, ha⟩ := (ZMod.chineseRemainder h4n).surjective (a4, an)
  
  have h_unit : IsUnit a := by
    have hu2 : IsUnit (2 : ZMod n) := isUnit_two_zmod n hn_odd
    have hu2inv : IsUnit ((2 : ZMod n)⁻¹) := by
      -- `ZMod` has a total `Inv`, but for units we can certify `a⁻¹` is a unit using the
      -- characteristic lemmas `inv_mul_of_unit` / `mul_inv_of_unit`.
      refine (isUnit_iff_exists_inv).2 ?_
      exact ⟨(2 : ZMod n), (ZMod.inv_mul_of_unit (2 : ZMod n) hu2)⟩
    have hun : IsUnit an := by
      dsimp [an]
      exact IsUnit.neg hu2inv
    have : IsUnit ((ZMod.chineseRemainder h4n) a) := by
      -- Transport to `ZMod 4 × ZMod n` via `ha`, then use `Prod.isUnit_iff`.
      -- `ha : chineseRemainder a = (a4, an)`
      -- so it suffices to show `IsUnit (a4, an)`.
      -- (Then `a4 = 1` and `an` is a unit because `2` is a unit mod odd `n`.)
      rw [ha, Prod.isUnit_iff]
      exact ⟨by simpa [a4], hun⟩
    -- Pull `IsUnit` back across the ring equivalence.
    exact (MulEquiv.isUnit_map (f := (ZMod.chineseRemainder h4n)) (x := a)).1 this
  
  let m := a.val
  have h_nz : 4 * n ≠ 0 := by omega
  haveI : NeZero (4 * n) := ⟨h_nz⟩
  have h_m : (m : ZMod (4 * n)) = a := by
    rw [ZMod.natCast_val, show (ZMod.cast : ZMod (4 * n) → ZMod (4 * n)) = id from ZMod.cast_id']
    rfl
  have hm_unit : IsUnit (m : ZMod (4 * n)) := h_m.symm ▸ h_unit
  
  obtain ⟨q, hqp, hq_mod⟩ := (Nat.infinite_setOf_prime_and_eq_mod hm_unit).nonempty
  use q
  constructor; · exact hqp
  
  have hq_a : (q : ZMod (4 * n)) = a := hq_mod.trans h_m
  constructor
  · -- q % 4 = 1
    have h_comp_fst :
        ∀ x : ZMod (4 * n),
          ZMod.castHom (dvd_mul_right 4 n) (ZMod 4) x = (ZMod.chineseRemainder h4n x).1 := by
      intro x
      -- `ZMod.chineseRemainder` maps via `castHom` into the product; `fst` recovers the mod-4 cast.
      simp [ZMod.chineseRemainder, ZMod.castHom_apply]
    let f : ZMod (4 * n) →+* ZMod 4 := ZMod.castHom (dvd_mul_right 4 n) (ZMod 4)
    have ha1 : (ZMod.chineseRemainder h4n a).1 = a4 := by
      -- `ha : chineseRemainder a = (a4, an)`
      simpa using congrArg Prod.fst ha
    have hfa : f a = a4 := by
      simpa [f] using (h_comp_fst a).trans ha1
    have hq4z : (q : ZMod 4) = a4 := by
      have hq4' : f (q : ZMod (4 * n)) = f a := congrArg f hq_a
      -- `f` on a natural cast is just the natural cast in `ZMod 4`.
      simpa [f, ZMod.castHom_apply, ZMod.cast_natCast (h := dvd_mul_right 4 n), hfa] using hq4'
    have : q % 4 = 1 := by
      have hval : (q : ZMod 4).val = (a4 : ZMod 4).val := congrArg ZMod.val hq4z
      -- Fix the argument order: `ZMod.val_natCast 4 q`.
      simpa [a4, ZMod.val_natCast] using hval
    exact this
  · -- q ≡ -1/2 mod n
    have h_comp_snd :
        ∀ x : ZMod (4 * n),
          ZMod.castHom (dvd_mul_left n 4) (ZMod n) x = (ZMod.chineseRemainder h4n x).2 := by
      intro x
      simp [ZMod.chineseRemainder, ZMod.castHom_apply]
    let f : ZMod (4 * n) →+* ZMod n := ZMod.castHom (dvd_mul_left n 4) (ZMod n)
    have ha2 : (ZMod.chineseRemainder h4n a).2 = an := by
      simpa using congrArg Prod.snd ha
    have hfa : f a = an := by
      simpa [f] using (h_comp_snd a).trans ha2
    have hqn : (q : ZMod n) = an := by
      have hqn' : f (q : ZMod (4 * n)) = f a := congrArg f hq_a
      simpa [f, ZMod.castHom_apply, ZMod.cast_natCast (h := dvd_mul_left n 4), hfa] using hqn'
    exact hqn

/-- Existence of `b` such that `b² ≡ -n (mod 4q)`. -/
lemma exists_ankeny_b (n q : ℕ) (hn : n % 8 = 3) (hq : Nat.Prime q) (hq1 : q % 4 = 1)
    (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹) :
    ∃ b : ℤ, b^2 ≡ - (n : ℤ) [ZMOD (4 * q)] := by
  have hn_odd : n % 2 = 1 := by omega
  have hnOdd : Odd n := Nat.odd_iff.2 hn_odd
  have hq_odd : q % 2 = 1 := by omega
  have hqOdd : Odd q := Nat.odd_iff.2 hq_odd

  -- From `hq_mod` we get `n ∣ 2q + 1` (equivalently `-2q ≡ 1 (mod n)`).
  have hu2n : IsUnit (2 : ZMod n) := isUnit_two_zmod n hn_odd
  have h2q : (2 : ZMod n) * (q : ZMod n) = (-1 : ZMod n) := by
    have hmul : (2 : ZMod n) * (2 : ZMod n)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit (2 : ZMod n) hu2n
    calc
      (2 : ZMod n) * (q : ZMod n)
          = (2 : ZMod n) * (- (2 : ZMod n)⁻¹) := by simpa [hq_mod]
      _ = - ((2 : ZMod n) * (2 : ZMod n)⁻¹) := by simp [mul_neg]
      _ = -1 := by simpa [hmul]
  have hn_dvd : n ∣ (2 * q + 1) := by
    have hz : ((2 * q + 1 : ℕ) : ZMod n) = 0 := by
      -- cast `(2*q+1)` into `ZMod n` and simplify using `h2q`.
      simpa [Nat.cast_add, Nat.cast_mul, h2q] using congrArg (fun t => t + (1 : ZMod n)) h2q
    exact (ZMod.natCast_eq_zero_iff (2 * q + 1) n).1 hz

  have hmod : (-2 * (q : ℤ)) ≡ (1 : ℤ) [ZMOD (n : ℤ)] := by
    -- `a ≡ b [ZMOD n]` means `n ∣ b - a`.
    apply (Int.modEq_iff_dvd).2
    have : (n : ℤ) ∣ (2 * q + 1 : ℤ) := Int.natCast_dvd_natCast.2 hn_dvd
    -- `1 - (-2q) = 1 + 2q = 2q + 1`
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm] using this

  -- Jacobi: `J(-2q | n) = J(1|n) = 1`.
  have hJ_neg2q : J(-2 * (q : ℤ) | n) = 1 := by
    have hrem : (-2 * (q : ℤ)) % (n : ℤ) = (1 : ℤ) % (n : ℤ) := by
      simpa [Int.ModEq] using hmod
    have hJ := jacobiSym.mod_left' (a₁ := (-2 * (q : ℤ))) (a₂ := (1 : ℤ)) (b := n) hrem
    simpa using hJ.trans (by simp)

  -- Compute `J(-2|n)=1` from `n % 8 = 3`.
  have hJ_neg2 : J(-2 | n) = 1 := by
    -- `J(-2|n) = χ₈' n`, and for odd `n ≡ 3 (mod 8)` we have `χ₈' n = 1`.
    have hχ : ZMod.χ₈' n = 1 := by
      have hn2ne0 : n % 2 ≠ 0 := by omega
      -- `χ₈' n = if n%2=0 then 0 else if n%8=1 ∨ n%8=3 then 1 else -1`
      simpa [ZMod.χ₈'_nat_eq_if_mod_eight, hn2ne0, hn] using (ZMod.χ₈'_nat_eq_if_mod_eight n)
    -- `jacobiSym.at_neg_two` requires odd modulus.
    simpa [jacobiSym.at_neg_two hnOdd, hχ] using (jacobiSym.at_neg_two (b := n) hnOdd)

  -- From `J(-2q|n)=1` and `J(-2|n)=1` deduce `J(q|n)=1`.
  have hJ_qn : J((q : ℤ) | n) = 1 := by
    have hmul := (jacobiSym.mul_left (-2 : ℤ) (q : ℤ) n).symm
    have : J(-2 | n) * J((q : ℤ) | n) = 1 := by
      -- rewrite `J((-2)*q|n)` using `hJ_neg2q`
      simpa [mul_assoc, hmul] using (hmul.trans (by
        -- `(-2 : ℤ) * (q : ℤ)` is definitionaly `-2 * q`
        simpa [mul_assoc] using hJ_neg2q))
    simpa [hJ_neg2] using this

  -- Reciprocity (since `q % 4 = 1`): `J(q|n)=J(n|q)`.
  have hJ_nq : J((n : ℤ) | q) = 1 := by
    have hqr : J((q : ℤ) | n) = J((n : ℤ) | q) := by
      simpa using (jacobiSym.quadratic_reciprocity_one_mod_four (a := q) (b := n) hq1 hnOdd)
    -- rewrite the left side of `hqr` using `hJ_qn`
    simpa [hqr] using hJ_qn

  -- Supplementary law: `J(-n|q) = χ₄ q * J(n|q) = 1`.
  have hJ_neg_nq : J(-(n : ℤ) | q) = 1 := by
    have hχ4 : ZMod.χ₄ q = 1 := by
      simpa using ZMod.χ₄_nat_one_mod_four hq1
    -- `J(-a|b) = χ₄ b * J(a|b)` for odd `b`.
    rw [jacobiSym.neg (a := (n : ℤ)) (b := q) hqOdd]
    simpa [hχ4, hJ_nq]

  -- For prime `q`, `J(-n|q)=1` implies `-n` is a square in `ZMod q`.
  haveI : Fact q.Prime := ⟨hq⟩
  have hsq : IsSquare ((-(n : ℤ)) : ZMod q) := by
    -- `ZMod.isSquare_of_jacobiSym_eq_one` produces `IsSquare (↑(-(n:ℤ)) : ZMod q)`;
    -- this `simpa` just normalizes the casts.
    simpa using
      (ZMod.isSquare_of_jacobiSym_eq_one (a := (-(n : ℤ))) (p := q) hJ_neg_nq)
  rcases hsq with ⟨r, hr⟩

  -- Lift to `ZMod (4*q)` using CRT and the mod-4 choice `1^2 = -n (mod 4)` (since `n ≡ 3 (mod 4)`).
  have h4q : Nat.Coprime 4 q := coprime_four_n q hq_odd
  obtain ⟨bz, hbz⟩ := (ZMod.chineseRemainder h4q).surjective ((1 : ZMod 4), r)

  have hn4 : n % 4 = 3 := by omega
  have hneg4 : ((-(n : ℤ)) : ZMod 4) = (1 : ZMod 4) := by
    -- Reduce to the concrete fact `-(3 : ZMod 4) = 1`.
    have hn4' : ((n : ℤ) : ZMod 4) = (3 : ZMod 4) := by
      -- `Int` cast and `Nat` cast coincide here.
      have : (n : ZMod 4) = (3 : ZMod 4) := by
        have : n ≡ 3 [MOD 4] := by simpa [Nat.ModEq, hn4]
        exact (ZMod.natCast_eq_natCast_iff n 3 4).2 this
      simpa using this
    -- `decide` works because `ZMod 4` is finite/decidable.
    have hneg3 : (-(3 : ZMod 4)) = (1 : ZMod 4) := by decide
    -- normalize `(-(n:ℤ) : ZMod 4)` into `-((n:ℤ):ZMod 4)`.
    -- First prove the negation statement for the (already cast) residue, then `simp` finishes.
    have : ( -((n : ℤ) : ZMod 4) ) = (1 : ZMod 4) := by
      calc
        -((n : ℤ) : ZMod 4) = -(3 : ZMod 4) := by simpa [hn4']
        _ = (1 : ZMod 4) := hneg3
    simpa using this

  have hbz_sq : (bz ^ 2 : ZMod (4 * q)) = (-(n : ℤ) : ZMod (4 * q)) := by
    apply (ZMod.chineseRemainder h4q).injective
    -- Compare both components in `ZMod 4 × ZMod q`.
    ext
    · -- mod 4 component
      have hbz_fst : ((ZMod.chineseRemainder h4q) bz).1 = (1 : ZMod 4) := by
        simpa using congrArg Prod.fst hbz
      have hfst_lhs :
          ((ZMod.chineseRemainder h4q) (bz ^ 2)).1 = (1 : ZMod 4) := by
        -- use that `chineseRemainder` is a ring hom on the `toFun` side
        -- and compute in the product.
        -- `(bz^2)` here is `bz^2` in `ZMod (4*q)`.
        simpa [pow_two, map_mul, hbz_fst] 
          using congrArg Prod.fst ((ZMod.chineseRemainder h4q).map_pow bz 2)
      have hfst_rhs :
          ((ZMod.chineseRemainder h4q) (-(n : ℤ) : ZMod (4 * q))).1 = (1 : ZMod 4) := by
        -- `chineseRemainder`'s first projection is reduction mod 4.
        simpa [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.fst_zmod_cast, hneg4]
      exact hfst_lhs.trans hfst_rhs.symm
    · -- mod q component
      have hbz_snd : ((ZMod.chineseRemainder h4q) bz).2 = r := by
        simpa using congrArg Prod.snd hbz
      have hsnd_lhs :
          ((ZMod.chineseRemainder h4q) (bz ^ 2)).2 = (r ^ 2 : ZMod q) := by
        -- same idea as the `fst` component, but in `ZMod q`.
        simpa [pow_two, map_mul, hbz_snd]
          using congrArg Prod.snd ((ZMod.chineseRemainder h4q).map_pow bz 2)
      have hsnd_rhs :
          ((ZMod.chineseRemainder h4q) (-(n : ℤ) : ZMod (4 * q))).2 = (r ^ 2 : ZMod q) := by
        -- second projection is reduction mod q, and `hr` gives `-(n) = r^2` in `ZMod q`.
        have : ((-(n : ℤ)) : ZMod q) = (r ^ 2 : ZMod q) := by
          -- `hr` is in the `IsSquare` form; normalize to `r^2`.
          simpa [pow_two] using hr
        simpa [ZMod.chineseRemainder, ZMod.castHom_apply, Prod.snd_zmod_cast, this]
      exact hsnd_lhs.trans hsnd_rhs.symm

  -- Export the congruence back to `Int.ModEq` using the representative `bz.val`.
  -- Use the canonical integer cast of `bz` (for `4*q > 0` this is `bz.val`).
  let b : ℤ := (ZMod.cast bz : ℤ)
  refine ⟨b, ?_⟩
  have hb_cast : ((b : ℤ) : ZMod (4 * q)) = bz := by
    simpa [b] using (ZMod.intCast_zmod_cast bz)
  have hb_sq_zmod : ((b ^ 2 : ℤ) : ZMod (4 * q)) = (-(n : ℤ) : ZMod (4 * q)) := by
    calc
      ((b ^ 2 : ℤ) : ZMod (4 * q)) = ((b : ZMod (4 * q)) ^ 2) := by simp
      _ = (bz ^ 2) := by simpa [hb_cast]
      _ = (-(n : ℤ) : ZMod (4 * q)) := hbz_sq

  -- Convert the `ZMod` equality into an `Int.ModEq` statement without fighting cast normalization.
  have hz : ((b ^ 2 + (n : ℤ) : ℤ) : ZMod (4 * q)) = 0 := by
    have hz' :
        ((b ^ 2 : ℤ) : ZMod (4 * q)) + (n : ZMod (4 * q)) = 0 := by
      -- add `n` to both sides of `b^2 = -n` in `ZMod (4*q)`
      have := congrArg (fun x : ZMod (4 * q) => x + (n : ZMod (4 * q))) hb_sq_zmod
      simpa [add_assoc] using this
    -- Rewrite `((b^2 + n) : ZMod m)` as `((b^2:ZMod m) + (n:ZMod m))`.
    simpa using hz'

  have hdvd : ((4 * q : ℕ) : ℤ) ∣ (b ^ 2 + (n : ℤ) : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (b ^ 2 + (n : ℤ)) (4 * q)).1 hz

  -- `b^2 ≡ -n [ZMOD 4*q]` is equivalent to `(4*q) ∣ (-n) - b^2`,
  -- and `(-n) - b^2 = -(b^2 + n)`.
  have : b ^ 2 ≡ -(n : ℤ) [ZMOD (4 * q : ℤ)] := by
    apply (Int.modEq_iff_dvd).2
    have : ((4 * q : ℕ) : ℤ) ∣ - (b ^ 2 + (n : ℤ) : ℤ) := by
      simpa using (Int.dvd_neg.2 hdvd)
    -- rewrite the divisor from `(4*q : ℕ)` to `(4*q : ℤ)` and the target difference
    -- `(-n) - b^2` to `-(b^2 + n)`.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  exact this

/-- The Ankeny lattice `L = { (x,y,z) : x ≡ y (mod n), y ≡ bz (mod 2q) }`. -/
def ankeny_lattice (n q : ℕ) (b : ℤ) : AddSubgroup (Fin 3 → ℝ) where
  carrier := { p | ∃ x y z : ℤ, p 0 = x ∧ p 1 = y ∧ p 2 = z ∧
                                x ≡ y [ZMOD n] ∧ y ≡ b * z [ZMOD (2 * q)] }
  add_mem' := by
    rintro _ _ ⟨x1, y1, z1, hx1, hy1, hz1, hmod1x, hmod1y⟩ ⟨x2, y2, z2, hx2, hy2, hz2, hmod2x, hmod2y⟩
    use x1 + x2, y1 + y2, z1 + z2
    constructor; · simp [hx1, hx2]
    constructor; · simp [hy1, hy2]
    constructor; · simp [hz1, hz2]
    constructor
    · exact hmod1x.add hmod2x
    · rw [mul_add]; exact hmod1y.add hmod2y
  zero_mem' := by
    use 0, 0, 0
    simp
  neg_mem' := by
    rintro _ ⟨x, y, z, hx, hy, hz, hmodx, hmody⟩
    use -x, -y, -z
    constructor; · simp [hx]
    constructor; · simp [hy]
    constructor; · simp [hz]
    constructor
    · exact hmodx.neg
    · rw [mul_neg]; exact hmody.neg

/-- A convenient full-rank ℤ-lattice for Ankeny has covolume `2nq`.

We construct an explicit `ℤ`-span lattice `L` generated by three vectors, show
`(L : Set _) ⊆ ankeny_lattice n q b` (so Minkowski points in `L` can be fed to
`ankeny_Q_mod`), and compute `volume` of its fundamental domain as `2nq`.

We do **not** attempt to transport `IsAddFundamentalDomain` across equality of AddSubgroups,
because the proposition depends on the *carrier type* `↥L` (a subtype), and equality of
subgroups does not give definitional equality of those subtypes.
-/
lemma ankeny_lattice_covolume (n q : ℕ) (b : ℤ) (hn : 0 < n) (hq : 0 < q) :
    ∃ (L : AddSubgroup (Fin 3 → ℝ)) (F : Set (Fin 3 → ℝ)),
      IsAddFundamentalDomain L F volume ∧
      volume F = (2 * n * q : ℝ≥0∞) ∧
      (L : Set (Fin 3 → ℝ)) ⊆ ankeny_lattice n q b := by
  classical
  -- We exhibit `ankeny_lattice n q b` as the `ℤ`-span of three vectors in `ℝ^3`:
  --
  --   v0 = (n,   0, 0)
  --   v1 = (2q, 2q, 0)
  --   v2 = (b,   b, 1)
  --
  -- These are linearly independent over `ℝ`, with determinant `2*n*q` (independent of `b`).
  let v0 : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => (n : ℝ)
    | 1 => 0
    | 2 => 0
  let v1 : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => (2 * q : ℝ)
    | 1 => (2 * q : ℝ)
    | 2 => 0
  let v2 : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => (b : ℝ)
    | 1 => (b : ℝ)
    | 2 => 1

  -- The matrix with columns `v0, v1, v2` in the standard basis of `ℝ^3`.
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![ (n : ℝ), (2 * q : ℝ), (b : ℝ)],
      ![ 0,        (2 * q : ℝ), (b : ℝ)],
      ![ 0,        0,           1 ]]

  have hdetA : A.det = (2 * n * q : ℝ) := by
    -- Expand the 3×3 determinant; our matrix is upper triangular.
    -- (We keep it explicit so future refactors don’t depend on more automation.)
    simp [A, Matrix.det_fin_three]
    ring

  have hdetA_ne : A.det ≠ 0 := by
    have : (0 : ℝ) < (2 * n * q : ℝ) := by
      -- `2*n*q` is positive as a real number.
      have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hq' : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      nlinarith
    simpa [hdetA] using ne_of_gt this

  have hdetA_unit : IsUnit A.det := by
    -- Over a field, `IsUnit r` is equivalent to `r ≠ 0`.
    simpa [isUnit_iff_ne_zero, hdetA_ne]

  -- Build an `ℝ`-basis with columns `v0,v1,v2` using `Matrix.toLinearEquiv`.
  let b0 : Basis (Fin 3) ℝ (Fin 3 → ℝ) := Pi.basisFun ℝ (Fin 3)
  let e : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLinearEquiv b0 A hdetA_unit
  let B : Basis (Fin 3) ℝ (Fin 3 → ℝ) := b0.map e

  -- Sanity: the basis vectors are exactly `v0,v1,v2`.
  have hB0 : B 0 = v0 := by
    have hto : Matrix.toLin (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3)) = (Matrix.toLin' : _ ) := by
      simpa using (Matrix.toLin_eq_toLin' (R := ℝ) (n := Fin 3) (m := Fin 3))
    ext i <;> fin_cases i
    · -- coordinate 0
      simp [B, b0, e, Matrix.toLinearEquiv, hto, Matrix.toLin'_apply, Matrix.mulVec_single_one, A, v0]
    ·
      simp [B, b0, e, Matrix.toLinearEquiv, hto, Matrix.toLin'_apply, Matrix.mulVec_single_one, A, v0]
    ·
      simp [B, b0, e, Matrix.toLinearEquiv, hto, Matrix.toLin'_apply, Matrix.mulVec_single_one, A, v0]
  have hB1 : B 1 = v1 := by
    have hto : Matrix.toLin (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3)) = (Matrix.toLin' : _ ) := by
      simpa using (Matrix.toLin_eq_toLin' (R := ℝ) (n := Fin 3) (m := Fin 3))
    ext i <;> fin_cases i
    · simp [B, b0, e, Matrix.toLinearEquiv, hto, Matrix.toLin'_apply, Matrix.mulVec_single_one, A, v1]
    · simp [B, b0, e, Matrix.toLinearEquiv, hto, Matrix.toLin'_apply, Matrix.mulVec_single_one, A, v1]
    · simp [B, b0, e, Matrix.toLinearEquiv, hto, Matrix.toLin'_apply, Matrix.mulVec_single_one, A, v1]
  have hB2 : B 2 = v2 := by
    have hto : Matrix.toLin (Pi.basisFun ℝ (Fin 3)) (Pi.basisFun ℝ (Fin 3)) = (Matrix.toLin' : _ ) := by
      simpa using (Matrix.toLin_eq_toLin' (R := ℝ) (n := Fin 3) (m := Fin 3))
    ext i <;> fin_cases i
    · simp [B, b0, e, Matrix.toLinearEquiv, hto, Matrix.toLin'_apply, Matrix.mulVec_single_one, A, v2]
    · simp [B, b0, e, Matrix.toLinearEquiv, hto, Matrix.toLin'_apply, Matrix.mulVec_single_one, A, v2]
    · simp [B, b0, e, Matrix.toLinearEquiv, hto, Matrix.toLin'_apply, Matrix.mulVec_single_one, A, v2]

  -- The ℤ-span lattice generated by `B`.
  let L : Submodule ℤ (Fin 3 → ℝ) := Submodule.span ℤ (Set.range B)
  let Ladd : AddSubgroup (Fin 3 → ℝ) := L.toAddSubgroup
  let F : Set (Fin 3 → ℝ) := ZSpan.fundamentalDomain B

  have fund : IsAddFundamentalDomain Ladd F volume :=
    ZSpan.isAddFundamentalDomain' B volume

  -- Volume computation: `det (Matrix.of B)` is `det A` up to transpose, hence `2*n*q`.
  have hMat_of : Matrix.of B = Aᵀ := by
    ext i j
    -- `Matrix.of B i j = B i j`; use `hB0/hB1/hB2` to rewrite rows.
    fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply, hB0, hB1, hB2, v0, v1, v2, A]
  have hvol : volume F = (2 * n * q : ℝ≥0∞) := by
    have hvol' : volume F = ENNReal.ofReal |(Matrix.of B).det| := by
      simpa [F] using (ZSpan.volume_fundamentalDomain B)
    have hdet' : (Matrix.of B).det = (2 * n * q : ℝ) := by
      -- `Matrix.of B = Aᵀ`, and `det Aᵀ = det A`.
      simpa [hMat_of, Matrix.det_transpose, hdetA]
    -- Convert `ENNReal.ofReal` back to `ℝ≥0∞` using nonnegativity.
    have hnonneg : (0 : ℝ) ≤ (2 * n * q : ℝ) := by
      have hn' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have hq' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Nat.zero_le q)
      nlinarith
    -- `ENNReal.ofReal |2*n*q| = 2*n*q` for nonnegative `2*n*q`.
    simpa [hvol', hdet', abs_of_nonneg hnonneg]

  -- Inclusion `Ladd ⊆ ankeny_lattice`: it suffices to show the generators lie in the congruence lattice.
  have hsubset : (Ladd : Set (Fin 3 → ℝ)) ⊆ ankeny_lattice n q b := by
    intro p hp
    have hp' : p ∈ L := hp
    have hgen : Set.range B ⊆ (AddSubgroup.toIntSubmodule (ankeny_lattice n q b) : Set (Fin 3 → ℝ)) := by
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · -- `B 0 = v0`
        have : v0 ∈ ankeny_lattice n q b := by
          refine ⟨(n : ℤ), 0, 0, ?_, ?_, ?_, ?_, ?_⟩
          · simp [v0]
          · simp [v0]
          · simp [v0]
          · simpa using (Int.modEq_zero_iff_dvd.mpr (dvd_rfl : (n : ℤ) ∣ (n : ℤ)))
          · simpa using (Int.modEq_zero_iff_dvd.mpr (dvd_rfl : (2 * q : ℤ) ∣ (0 : ℤ)))
        simpa [AddSubgroup.coe_toIntSubmodule, hB0] using this
      · -- `B 1 = v1`
        have : v1 ∈ ankeny_lattice n q b := by
          refine ⟨(2 * q : ℤ), (2 * q : ℤ), 0, ?_, ?_, ?_, ?_, ?_⟩
          · simp [v1]
          · simp [v1]
          · simp [v1]
          · simpa using (Int.ModEq.refl (2 * q : ℤ))
          · simpa using (Int.modEq_zero_iff_dvd.mpr (dvd_rfl : (2 * q : ℤ) ∣ (2 * q : ℤ)))
        simpa [AddSubgroup.coe_toIntSubmodule, hB1] using this
      · -- `B 2 = v2`
        have : v2 ∈ ankeny_lattice n q b := by
          refine ⟨b, b, 1, ?_, ?_, ?_, ?_, ?_⟩
          · simp [v2]
          · simp [v2]
          · simp [v2]
          · simpa using (Int.ModEq.refl b)
          · simpa using (Int.ModEq.refl b)
        simpa [AddSubgroup.coe_toIntSubmodule, hB2] using this
    have hspan_le : L ≤ AddSubgroup.toIntSubmodule (ankeny_lattice n q b) := by
      refine Submodule.span_le.2 ?_
      intro x hx
      exact hgen hx
    have : p ∈ AddSubgroup.toIntSubmodule (ankeny_lattice n q b) := hspan_le hp'
    simpa [AddSubgroup.coe_toIntSubmodule] using this

  refine ⟨Ladd, F, fund, hvol, hsubset⟩

/-- The quadratic form `Q = 2qx² + y² + nz²`. -/
def ankeny_Q (n q : ℕ) (x y z : ℤ) : ℤ :=
  2 * q * x^2 + y^2 + n * z^2

/-- Any point in the Ankeny lattice satisfies `Q ≡ 0 (mod 2nq)`. -/
lemma ankeny_Q_mod (n q : ℕ) (b : ℤ) (x y z : ℤ)
    (hn_odd : n % 2 = 1)
    (hq_mod : (q : ZMod n) = - (2 : ZMod n)⁻¹)
    (h_lat : (fun i => match i with | 0 => (x:ℝ) | 1 => (y:ℝ) | 2 => (z:ℝ)) ∈ ankeny_lattice n q b)
    (hb : b^2 ≡ - (n : ℤ) [ZMOD (2 * q)]) :
    (ankeny_Q n q x y z) ≡ 0 [ZMOD (2 * n * q)] := by
  -- Unpack lattice membership into the two congruence conditions.
  rcases h_lat with ⟨x', y', z', hx', hy', hz', hxy, hybz⟩
  -- The membership witness must match the input `(x,y,z)` (by `Int.cast` injectivity into `ℝ`).
  have hx_int : x' = x := by
    -- hx' : (x:ℝ) = (x':ℝ)
    have : ((x' : ℝ) = (x : ℝ)) := by simpa using hx'.symm
    exact_mod_cast this
  have hy_int : y' = y := by
    have : ((y' : ℝ) = (y : ℝ)) := by simpa using hy'.symm
    exact_mod_cast this
  have hz_int : z' = z := by
    have : ((z' : ℝ) = (z : ℝ)) := by simpa using hz'.symm
    exact_mod_cast this

  have hxy' : x ≡ y [ZMOD (n : ℤ)] := by simpa [hx_int, hy_int] using hxy
  have hybz' : y ≡ b * z [ZMOD (2 * q : ℤ)] := by
    simpa [hy_int, hz_int, Nat.cast_mul] using hybz

  -- First, show `Q ≡ 0 (mod n)`.
  have hu2n : IsUnit (2 : ZMod n) := isUnit_two_zmod n hn_odd
  have h2q_zmod : (2 : ZMod n) * (q : ZMod n) = (-1 : ZMod n) := by
    have hmul : (2 : ZMod n) * (2 : ZMod n)⁻¹ = 1 :=
      ZMod.mul_inv_of_unit (2 : ZMod n) hu2n
    calc
      (2 : ZMod n) * (q : ZMod n)
          = (2 : ZMod n) * (- (2 : ZMod n)⁻¹) := by simpa [hq_mod]
      _ = - ((2 : ZMod n) * (2 : ZMod n)⁻¹) := by simp [mul_neg]
      _ = -1 := by simpa [hmul]
  have hn_dvd : n ∣ (2 * q + 1) := by
    have hz : ((2 * q + 1 : ℕ) : ZMod n) = 0 := by
      -- cast `(2*q+1)` into `ZMod n` and simplify using `h2q_zmod`.
      simpa [Nat.cast_add, Nat.cast_mul, h2q_zmod] using
        congrArg (fun t => t + (1 : ZMod n)) h2q_zmod
    exact (ZMod.natCast_eq_zero_iff (2 * q + 1) n).1 hz
  have h2q_mod_n : ((2 * q : ℤ)) ≡ (-1 : ℤ) [ZMOD (n : ℤ)] := by
    -- `n ∣ 2q+1` implies `2q ≡ -1 (mod n)`.
    apply (Int.modEq_iff_dvd).2
    have : (n : ℤ) ∣ (2 * q + 1 : ℤ) := Int.natCast_dvd_natCast.2 hn_dvd
    -- `(-1) - (2q) = -(2q+1)`
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]
      using (Int.dvd_neg.2 this)

  have hx2y2 : x ^ 2 ≡ y ^ 2 [ZMOD (n : ℤ)] :=
    Int.ModEq.pow 2 hxy'

  have hQ_mod_n : (ankeny_Q n q x y z) ≡ 0 [ZMOD (n : ℤ)] := by
    -- Reduce `Q` mod `n`:
    -- `n*z^2 ≡ 0`, and `2q*x^2 ≡ (-1)*x^2`, and `y^2 ≡ x^2`.
    have hz0 : (n : ℤ) ∣ (n * z ^ 2 : ℤ) := by exact dvd_mul_right _ _
    have hterm_z : (n * z ^ 2 : ℤ) ≡ 0 [ZMOD (n : ℤ)] := hz0.modEq_zero_int
    have hterm_2qx : ((2 * q : ℤ) * x ^ 2) ≡ ((-1 : ℤ) * x ^ 2) [ZMOD (n : ℤ)] :=
      (Int.ModEq.mul_right (x ^ 2) h2q_mod_n)
    have hy2x2 : (y ^ 2 : ℤ) ≡ (x ^ 2 : ℤ) [ZMOD (n : ℤ)] :=
      by simpa [pow_two, mul_assoc, mul_comm, mul_left_comm] using hx2y2.symm
    -- Now assemble.
    -- Start from `Q = 2*q*x^2 + y^2 + n*z^2`.
    have h :=
      (hterm_2qx.add (hy2x2.add hterm_z))  -- note: parentheses are `2q*x^2 + (y^2 + n*z^2)`
    -- normalize associativity and the `ankeny_Q` definition
    simpa [ankeny_Q, mul_assoc, add_assoc, add_left_comm, add_comm] using h

  -- Second, show `Q ≡ 0 (mod 2q)`.
  have hQ_mod_2q : (ankeny_Q n q x y z) ≡ 0 [ZMOD (2 * q : ℤ)] := by
    -- `2*q*x^2` is 0 mod `2*q`.
    have h0a : (2 * q : ℤ) ∣ (2 * (q : ℤ) * x ^ 2) := by
      -- `2*q` divides `2*q*x^2`.
      refine dvd_mul_of_dvd_left ?_ (x ^ 2)
      simp [Nat.cast_mul, mul_assoc]
    have hterm0 : (2 * (q : ℤ) * x ^ 2) ≡ 0 [ZMOD (2 * q : ℤ)] := h0a.modEq_zero_int
    -- From `y ≡ b*z (mod 2q)`, get `y^2 ≡ (b*z)^2`.
    have hy2 : y ^ 2 ≡ (b * z) ^ 2 [ZMOD (2 * q : ℤ)] :=
      Int.ModEq.pow 2 hybz'
    -- From `hb : b^2 ≡ -n (mod 2q)`, deduce `(b^2 + n) ≡ 0`.
    have hb0 : (b ^ 2 + (n : ℤ)) ≡ 0 [ZMOD (2 * q : ℤ)] := by
      -- add `n` to both sides of `b^2 ≡ -n`
      have := hb.add_right (n : ℤ)
      -- RHS: `(-n) + n = 0`
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    -- Multiply `hb0` by `z^2` to get `(b^2 + n) * z^2 ≡ 0`.
    have hb0_mul : (b ^ 2 + (n : ℤ)) * z ^ 2 ≡ 0 [ZMOD (2 * q : ℤ)] := by
      -- `mul_right` gives `… ≡ 0 * z^2`; `simp` turns that into `… ≡ 0`.
      simpa using (Int.ModEq.mul_right (z ^ 2) hb0)
    -- Bundle `(b*z)^2 + n*z^2` as `(b^2 + n) * z^2` using a literal equality.
    have hsum_eq : ((b * z) ^ 2 + (n : ℤ) * z ^ 2) = (b ^ 2 + (n : ℤ)) * z ^ 2 := by
      simp [pow_two]
      ring
    have hsum :
        ((b * z) ^ 2 + (n : ℤ) * z ^ 2) ≡ ((b ^ 2 + (n : ℤ)) * z ^ 2) [ZMOD (2 * q : ℤ)] := by
      simpa [hsum_eq] using
        (Int.ModEq.rfl :
          ((b * z) ^ 2 + (n : ℤ) * z ^ 2) ≡ ((b * z) ^ 2 + (n : ℤ) * z ^ 2) [ZMOD (2 * q : ℤ)])
    -- Now assemble: first show `y^2 + n*z^2 ≡ 0 (mod 2q)`, then add the `2q*x^2` term (which is 0).
    have hy2' :
        (y ^ 2 + (n : ℤ) * z ^ 2) ≡ ((b * z) ^ 2 + (n : ℤ) * z ^ 2) [ZMOD (2 * q : ℤ)] :=
      hy2.add_right _
    have hrest : (y ^ 2 + (n : ℤ) * z ^ 2) ≡ 0 [ZMOD (2 * q : ℤ)] :=
      hy2'.trans (hsum.trans hb0_mul)
    have htotal :
        (2 * (q : ℤ) * x ^ 2 + (y ^ 2 + (n : ℤ) * z ^ 2)) ≡ 0 [ZMOD (2 * q : ℤ)] :=
      hterm0.add hrest
    simpa [ankeny_Q, mul_assoc, add_assoc, add_comm, add_left_comm] using htotal

  -- Combine the two congruences using coprimality: `gcd(n, 2q) = 1`.
  have hcop_nq : Nat.Coprime n q := by
    -- `q ≡ -1/2 (mod n)` implies `q` is a unit in `ZMod n`.
    have huq : IsUnit (q : ZMod n) := by
      have hu2 : IsUnit (2 : ZMod n) := isUnit_two_zmod n hn_odd
      have hu2inv : IsUnit ((2 : ZMod n)⁻¹) := by
        refine (isUnit_iff_exists_inv).2 ?_
        exact ⟨(2 : ZMod n), (ZMod.inv_mul_of_unit (2 : ZMod n) hu2)⟩
      have : IsUnit (-(2 : ZMod n)⁻¹) := IsUnit.neg hu2inv
      simpa [hq_mod] using this
    exact ((ZMod.isUnit_iff_coprime q n).1 huq).symm
  have hcop_n2 : Nat.Coprime n 2 := by
    have h2 : Nat.Coprime 2 n := by
      apply (Nat.prime_two.coprime_iff_not_dvd).mpr
      intro h
      have : n % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
      rw [hn_odd] at this; contradiction
    exact h2.symm
  have hcop_n2q : Nat.Coprime n (2 * q) := (hcop_n2.mul_right hcop_nq)
  have hmn : (n : ℤ).natAbs.Coprime (2 * q : ℤ).natAbs := by
    simpa using hcop_n2q
  have hboth : (ankeny_Q n q x y z) ≡ 0 [ZMOD (n : ℤ)] ∧ (ankeny_Q n q x y z) ≡ 0 [ZMOD (2 * q : ℤ)] :=
    ⟨hQ_mod_n, hQ_mod_2q⟩
  have : (ankeny_Q n q x y z) ≡ 0 [ZMOD ((n : ℤ) * (2 * q : ℤ))] :=
    (Int.modEq_and_modEq_iff_modEq_mul (a := ankeny_Q n q x y z) (b := 0) (m := (n : ℤ)) (n := (2 * q : ℤ)) hmn).1 hboth
  -- normalize `n * (2*q)` to `2*n*q`
  simpa [mul_assoc, mul_comm, mul_left_comm, Nat.cast_mul] using this

/-- Minkowski application: there exists a representation `2qx² + y² + nz² = 2nq`. -/
lemma exists_ankeny_representation (n q : ℕ) (b : ℤ) (hn : n % 8 = 3) (hq : Nat.Prime q)
    (hq1 : q % 4 = 1) (hb : b^2 ≡ - (n : ℤ) [ZMOD (4 * q)]) :
    ∃ x y z : ℤ, 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q ∧ (x, y, z) ≠ 0 := by
  -- 1. Ellipsoid E with volume > 8 * covolume.
  -- 2. Minkowski point.
  -- 3. Q is divisible by 2nq and 0 < Q < 4nq => Q = 2nq.
  sorry

/-- Reduction of `2qx² + y² + nz² = 2nq` to `n = x² + u² + v²`. -/
lemma reduction_to_sum_three_squares (n q : ℕ) (x y z : ℤ)
    (h_ankeny : 2 * q * x^2 + y^2 + n * z^2 = 2 * n * q)
    (hq : Nat.Prime q) (hq1 : q % 4 = 1) :
    ∃ u v : ℤ, n = x^2 + u^2 + v^2 := by
  -- Use Sum of Two Squares theorem on (y² + nz²)/(2q).
  sorry

/-- Final theorem for `n ≡ 3 (mod 8)`. -/
theorem sum_three_squares_of_three_mod_eight (n : ℕ) (hn : n % 8 = 3) :
    ∃ x y z : ℕ, x^2 + y^2 + z^2 = n := by
  -- 1. Assume n square-free (wlog).
  -- 2. Find q, b.
  -- 3. Find x, y, z.
  -- 4. Reduce.
  sorry

end PolygonalNumberTheorem
