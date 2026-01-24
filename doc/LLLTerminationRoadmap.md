# LLL termination roadmap (Computable / exact track)

This note is a **proof-plan artifact** for the `GeometryOfNumbers/Computable` LLL track.
It is intentionally *non-code* so we can keep the Lean sources `sorry`-free while still
making forward progress on the hard parts.

## Status (January 2026)

This roadmap started as a “proof plan” while keeping the Lean sources `sorry`-free.
The core termination proof is now implemented in:

- `GeometryOfNumbers/Computable/LLLExactTermination.lean`

Current “end-to-end” contract:

- `LLLExact.lean`: executable runner (`lllRunExactGo` / `lllRunExact`) + checkers/specs
- `LLLExactProofs.lean`: `finished → LLLReducedQ`
- `LLLExactTermination.lean`: under `RowLIQ` and `δ < 1`, `∃ limit, reason = .finished`
  (and thus `∃ limit, LLLReducedQ ...`)

## What “termination” means here

`lllRunExact` is **fuel-bounded**, so it is total by construction.
A termination proof is about the *unbounded* algorithmic behavior:

- show that there exists a bound `T(B, δ)` such that for all `limit ≥ T`,
  the runner reaches `.finished`.

In our implementation, this bound is realized by a concrete measure (`termMeasure`) and a lemma
of the form “`fuel ≥ termMeasure + 1` implies `.finished`”.

## The classic proof shape (now implemented)

LLL termination is traditionally proved using a **potential function** that strictly decreases
on swaps and is bounded below.

A robust way to make this work in Lean is to separate the steps:

1. **Basis invariant**: elementary row operations preserve the “basis/rank” invariant (`RowLIQ`).
2. **Swap decreases potential**: the key strict inequality driven by Lovász failure.
3. **Potential bounded below**: because it is a positive rational (or integer after scaling).
4. Conclude: **finite swaps**.
5. Conclude: after the last swap, `k` monotonically increases to `n` → `.finished`.

## Potential function choice (recommended)

For the exact-`ℚ` track, prefer a *denominator-free* multiplicative potential in `ℚ` that avoids
`Real`/`log`:

- Define `d_i := ‖b*_i‖²` using the existing `gsoNormSqQ`.
- Define

  \[
  \Phi(B) := \prod_{i=0}^{n-1} d_i^{(n-1-i)}.
  \]

This matches the standard LLL “projected volume” viewpoint and mirrors the (ℝ) potential described
in `GeometryOfNumbers/Computable/LLL.lean`.

## Where SMT helps (and where it won’t)

SMT is useful for “leaf” arithmetic goals once we reduce to rational inequalities.
It won’t solve:

- definitional rewriting / simp-normal-form drift,
- Gram–Schmidt structure lemmas (prefix-vs-full GSO),
- induction on the runner.

So the plan is:

- Lean does the *structural* work,
- SMT discharges the *numeric inequality* leaves.

## Next steps (what “more progress” means now)

- **Complexity bounds**: relate `termMeasure` / the potentials to a textbook polynomial-time bound
  (swap count / iteration count) in a recognizable form.
- **Statement polish**: expose a “semantic” reducedness theorem closer to common LLL literature
  (rather than the current checker-shaped `LLLReducedQ`).
- **Refactoring**: split `LLLExactTermination.lean` if the computable LLL track stays active.

## References to mirror (structure, not code)

- Isabelle AFP: *LLL Basis Reduction* (proof decomposition + invariants)  
  `https://www.isa-afp.org/browser_info/current/AFP/LLL_Basis_Reduction/outline.pdf`

