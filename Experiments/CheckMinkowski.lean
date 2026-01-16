import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Tactic

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

