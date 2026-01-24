import GeometryOfNumbers.Computable.LLLExact

/-!
## Experiment: LLL on the Ankeny span lattice basis

In `GeometryOfNumbers/Legendre/Ankeny.lean` we use an explicit ℤ-span lattice in `E3 = Fin 3 → ℝ`
whose basis matrix (with basis vectors as columns) is:

```text
⎡ n    2q   b ⎤
⎢ 0    2q   b ⎥
⎣ 0     0   1 ⎦
```

This file builds the corresponding **integer** matrix and runs the exact (ℚ) computable LLL reducer
on its transpose (since `LLLExact` treats rows as basis vectors).

This is not used by the formal Ankeny proof yet; it is a “sanity bridge”:
- reduced bases make it easier to enumerate short lattice vectors,
- which is the constructive analogue of the Minkowski witness step.
-/

namespace GeometryOfNumbers.Experiments

open GeometryOfNumbers.Computable

def ankenySpanMatrixZ (n q : ℕ) (b : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![(n : ℤ), (2 * q : ℤ), b;
    0, (2 * q : ℤ), b;
    0, 0, (1 : ℤ)]

def ankenySpanBasisRowsZ (n q : ℕ) (b : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  (ankenySpanMatrixZ n q b).transpose

def δ_default : ℚ := (3 / 4 : ℚ)

-- A tiny E2E smoke: run the executable LLL loop and check the boolean reducedness predicate.
-- Keep the instance small so compilation stays fast.
def demoResult : LLLRunResult 3 :=
  lllRunExact (n := 3) (B := ankenySpanBasisRowsZ 7 5 (-3)) (δ := δ_default) (limit := 8000)

-- If you want to actually run this locally, use an interactive `#eval` in a scratch buffer; we keep
-- this file compile-only so CI stays fast.
#check demoResult

end GeometryOfNumbers.Experiments

