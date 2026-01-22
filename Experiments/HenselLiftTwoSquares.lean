import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
Scratch space for the prime-power lifting step in `GeometryOfNumbers/Core/ModularSquares.lean`.

Goal: if we have a solution to
\[
u^2 + v^2 + 1 \equiv 0 \pmod{p^k}
\]
with `p` an odd prime and `p ∤ u`, then we can adjust `u` by a multiple of `p^k` to obtain a
solution modulo `p^(k+1)`.

This file is intentionally small: we want the proof to be robust before porting it into the
library file (so we don’t repeatedly break `lake build` while iterating).
-/

namespace GeometryOfNumbers.Experiments

open scoped BigOperators

/-!
## Status

This file was an in-progress attempt to “Hensel lift” a congruence of the form

- `u^2 + v^2 + 1 ≡ 0 [ZMOD p^k]`

to modulus `p^(k+1)` under the side condition `p ∤ u` (for odd prime `p`).

The proof sketch is standard:
- write `u^2 + v^2 + 1 = p^k * m`,
- choose `x : ZMod p` solving `m + (2u)x = 0`,
- set `u' = u + x * p^k` and expand.

However, the details are subtle (casts `ℕ↔ℤ`, the exact `ZMod` divisibility lemmas, and the
normal-form goals you want in `Int.ModEq`), and this scratch file was drifting and breaking builds.

We keep the *idea* documented here, but remove the unstable proof attempt so `just experiments`
remains a reliable “everything compiles” gate.
-/

example : True := by
  trivial

end GeometryOfNumbers.Experiments

