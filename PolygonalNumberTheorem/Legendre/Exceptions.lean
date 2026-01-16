import Mathlib.Data.Nat.Basic

namespace Nat

/-!
## Three-squares exception set

This is the standard obstruction set for representation by `x^2 + y^2 + z^2`:

```text
n is a three-square exception ⇔ ∃ a k, n = 4^a (8k + 7).
```

We keep the definition in a small file so it can be shared by multiple proof attempts
(Minkowski/Ankeny/ternary QF) without creating import cycles.
-/

def is_three_square_exception (n : ℕ) : Prop :=
  ∃ a k : ℕ, n = 4 ^ a * (8 * k + 7)

end Nat

