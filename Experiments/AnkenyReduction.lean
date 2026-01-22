
import GeometryOfNumbers.Legendre.Ankeny

section AnkenyReduction

variable (n q : ℕ) (x y z : ℤ)

/-!
This file used to be a scratchpad for the “reduction step” in Ankeny’s proof.

That work is now completed (and considerably refactored) in `GeometryOfNumbers/Legendre/Ankeny.lean`,
in particular around the descent from the representation of `2*n*q` to a representation of `n`
(see `reduction_to_sum_three_squares` and the lemmas it depends on).

We keep this file as a pointer so older links don’t rot, but we intentionally avoid duplicating a
second incomplete proof in `Experiments/`.
-/

end AnkenyReduction
