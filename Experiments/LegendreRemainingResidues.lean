import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-!
Brute checks for the remaining residue classes in `GeometryOfNumbers.Legendre.Main`.

This file exists for two reasons:

1. **Reality check**: before investing in a large formal proof, confirm that small instances behave
   as expected (no surprises in the “reduced” cases `n % 8 ∈ {2,5,6}`).
2. **Debugging aid**: when a future proof attempt fails, we can compare against concrete witnesses.

This is not intended to be fast; it is intended to be small and explicit.
-/

namespace GeometryOfNumbers.Experiments

private def sq (x : Nat) : Nat := x ^ 2

private partial def search_z (n x y z : Nat) : Option (Nat × Nat × Nat) :=
  if z > n then none
  else if sq x + sq y + sq z = n then some (x, y, z)
  else search_z n x y (z + 1)

private partial def search_y (n x y : Nat) : Option (Nat × Nat × Nat) :=
  if y > n then none
  else
    match search_z n x y 0 with
    | some t => some t
    | none => search_y n x (y + 1)

private partial def search_x (n x : Nat) : Option (Nat × Nat × Nat) :=
  if x > n then none
  else
    match search_y n x 0 with
    | some t => some t
    | none => search_x n (x + 1)

def find_three_squares (n : Nat) : Option (Nat × Nat × Nat) :=
  search_x n 0

private def is_exception_aux (n a : Nat) : Bool :=
  let p : Nat := 4 ^ a
  if p = 0 then false
  else if n % p != 0 then false
  else
    let t := n / p
    t % 8 == 7

private partial def is_exception_loop (n a : Nat) : Bool :=
  -- Once 4^a > n (and n>0), larger a won't divide n.
  if a > n then false
  else if is_exception_aux n a then true
  else is_exception_loop n (a + 1)

def is_exception (n : Nat) : Bool :=
  if n = 0 then false else is_exception_loop n 0

def needs_legendre_remaining_work (n : Nat) : Bool :=
  -- Focus on the reduced residue classes that are TODO in `sum_three_squares_of_not_exception`.
  (n % 8 == 2) || (n % 8 == 5) || (n % 8 == 6)

def first_counterexamples (limit : Nat) : List Nat :=
  ((List.range (limit + 1)).filter fun n =>
    needs_legendre_remaining_work n &&
    (!is_exception n) &&
    (find_three_squares n).isNone)

-- For small limits, this should evaluate to `[]`.
-- If it does not, the first counterexample(s) are printed.
#eval first_counterexamples 200

end GeometryOfNumbers.Experiments

