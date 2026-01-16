import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Tactic

noncomputable section

/-!
# Minkowski route: import sanity check (scratch)

Copied (and updated) from `../Scripts/CheckMinkowski.lean`.

The relevant theorem in Mathlib is *not* `exists_nonzero_mem_of_measure_lt_pi_two_pow`.
It is:

- `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`

from `Mathlib.MeasureTheory.Group.GeometryOfNumbers`.

This file exists just to force the imports to typecheck once `elan`/`lake` are installed.
-/

open MeasureTheory MeasureTheory.Measure

-- Probes for the exact lemma names/shapes we’ll need for the Ankeny route:
-- - Minkowski theorem (`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`)
-- - covolume computation via determinant (`ZLattice.covolume_eq_det`)
#check MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
#check MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
#check ZLattice.covolume_eq_det
#check ZLattice.covolume_eq_measure_fundamentalDomain

/-!
## Toy 1: ZSpan fundamental domain and volume for a simple ℤ-span lattice in `ℝ^3`

This mirrors what we ended up doing in `PolygonalNumberTheorem/Legendre/Ankeny.lean`,
but pared down to the minimum: pick a basis `B`, then `F := ZSpan.fundamentalDomain B`,
then:

- `ZSpan.isAddFundamentalDomain' B volume`
- `ZSpan.volume_fundamentalDomain B`
-/

open scoped BigOperators Matrix

section ToyZSpan

-- A concrete diagonal matrix in `ℝ^3`.
def toyA : Matrix (Fin 3) (Fin 3) ℝ :=
  (![![2, 0, 0], ![0, 3, 0], ![0, 0, 5]] : Matrix (Fin 3) (Fin 3) ℝ)

-- A diagonal-ish basis of `ℝ^3`, so determinant is obvious.
def toyBasis : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ) :=
  (Pi.basisFun ℝ (Fin 3)).map
    (Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 3))
      toyA
      (by
        -- det = 2*3*5 ≠ 0
        have : toyA.det = (30 : ℝ) := by
          simp [toyA, Matrix.det_fin_three]
          norm_num
        -- over a field, det ≠ 0 ↔ IsUnit det
        have : toyA.det ≠ 0 := by
          simpa [this]
        simpa [isUnit_iff_ne_zero, this]))

-- The ℤ-span lattice and its fundamental domain.
def toyLattice : AddSubgroup (Fin 3 → ℝ) :=
  (Submodule.span ℤ (Set.range (toyBasis))).toAddSubgroup

def toyFD : Set (Fin 3 → ℝ) :=
  ZSpan.fundamentalDomain (toyBasis)

-- The fundamental-domain theorem for the span lattice.
example : IsAddFundamentalDomain toyLattice toyFD volume := by
  -- This is exactly the lemma we use in the Ankeny proof, but with a tiny toy basis.
  simpa [toyLattice, toyFD] using (ZSpan.isAddFundamentalDomain' (toyBasis) volume)

-- Volume of the fundamental domain is `ENNReal.ofReal |det|`.
example :
    volume toyFD =
      ENNReal.ofReal |(Matrix.of (toyBasis)).det| := by
  simpa [toyFD] using (ZSpan.volume_fundamentalDomain (toyBasis))

end ToyZSpan

/-!
## Toy 2: Minkowski invocation skeleton

This is *not* a proof yet; it’s a “shape check” for the lemma:
`MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure`.

The hard part in our real proof is building a measurable symmetric convex body `s`
and proving the measure inequality. This snippet is just meant to show how the
quantifiers line up once we have that inequality.
-/

section ToyMinkowski

open MeasureTheory

-- We keep everything abstract; the point is the statement shape.
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (L : AddSubgroup E) (s : Set E)
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

#check MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure

-- The (expected) way we’ll use it:
-- given `hs : MeasurableSet s` and `hvol : volume s > 2^dim * covolume(L)`,
-- conclude existence of `x ≠ 0` in `L ∩ s`.
--
-- (We don't fill the hypotheses here; this is just a placeholder “spine”.)
example
    (hs0 : MeasurableSet s)
    (h : True) :
    True := by
  -- In the real proof, this `have` will produce `∃ x ≠ 0, x ∈ L ∧ x ∈ s`.
  -- have hx :=
  --   MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
  --     (L := L) (s := s) (μ := volume) ?... ?...
  trivial

end ToyMinkowski

-- For Ankeny, the intended covolume computation is via an explicit ℤ-basis in ℤ^3:
--
--   v1 = (n, 0, 0)
--   v2 = (2q, 2q, 0)
--   v3 = (b, b, 1)
--
-- det([v1 v2 v3]) = 2*n*q
--
-- The main missing work is turning `ankeny_lattice` (defined by congruences) into a `ZLattice`
-- or an equivalent `Submodule ℤ (Fin 3 → ℝ)` with that basis, so we can plug into `covolume_eq_det`.

def checkMinkowskiAvailable : IO Unit := do
  IO.println "Checking Minkowski (GeometryOfNumbers) imports..."
  IO.println "See `#check` outputs above for lemma names."

def main : IO Unit := checkMinkowskiAvailable

#eval main

