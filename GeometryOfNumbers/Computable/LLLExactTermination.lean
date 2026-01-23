import GeometryOfNumbers.Computable.LLLExact
import GeometryOfNumbers.Computable.LLLExactProofs

namespace GeometryOfNumbers.Computable

/-!
## Termination scaffolding (exact / ℚ GS)

This file is the start of the “hard” LLL story: a potential-function argument for termination.

The goal is to keep this development:
- **incremental** (small lemmas that compile),
- **backend-free** (pure Lean/Mathlib),
- and **sorry-free**.

See `doc/LLLTerminationRoadmap.md` for the proof plan.
-/

/-- The classic LLL potential, specialized to the exact-ℚ Gram–Schmidt track.

\[
\Phi(B) := \prod_{i=0}^{n-1} \bigl(\|b_i^\*\|^2\bigr)^{(n-1-i)}.
\]

We keep it in `ℚ` so later proofs can stay in rational arithmetic.
-/
def potentialQ {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℚ :=
  (Finset.univ : Finset (Fin n)).prod fun i =>
    (gsoNormSqQ (n := n) B i) ^ (n - 1 - i.1)

@[simp] lemma potentialQ_def {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :
    potentialQ (n := n) B =
      (Finset.univ : Finset (Fin n)).prod (fun i => (gsoNormSqQ (n := n) B i) ^ (n - 1 - i.1)) := by
  rfl

/-!
### First “leaf” lemmas

These are tiny facts we’ll reuse repeatedly once the swap-step inequality is in view.
-/

lemma gsoNormSqQ_nonneg {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
    (0 : ℚ) ≤ gsoNormSqQ (n := n) B i := by
  classical
  -- `dotQ v v` is a sum of squares.
  simp [gsoNormSqQ, dotQ]
  exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (gsoAtQ (n := n) B i j))

end GeometryOfNumbers.Computable

