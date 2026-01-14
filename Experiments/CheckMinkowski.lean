import Mathlib.MeasureTheory.Group.GeometryOfNumbers
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

def checkMinkowskiAvailable : IO Unit := do
  IO.println "Checking Minkowski (GeometryOfNumbers) imports..."
  let _ := @MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
  IO.println "Found: exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure"

def main : IO Unit := checkMinkowskiAvailable

#eval main

