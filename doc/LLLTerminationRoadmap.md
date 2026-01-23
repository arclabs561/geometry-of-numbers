# LLL termination roadmap (Computable / exact track)

This note is a **proof-plan artifact** for the `GeometryOfNumbers/Computable` LLL track.
It is intentionally *non-code* so we can keep the Lean sources `sorry`-free while still
making forward progress on the hard parts.

## Current contract surface (what we can already prove)

- `GeometryOfNumbers/Computable/LLLExact.lean` provides:
  - the executable loop (`lllRunExactGo` / `lllRunExact`),
  - checkers `isSizeReducedQ`, `isLovaszReducedQ`, `isLLLReducedQ`,
  - Prop wrappers `SizeReducedQ`, `LovaszReducedQ`, `LLLReducedQ`.
- `GeometryOfNumbers/Computable/LLLExactProofs.lean` proves the central postcondition:
  - `lllRunExact_finished_LLLReducedQ_of_RowLIQ`:
    if a run finishes, the output satisfies the (Prop) reducedness spec.

So the *semantic correctness* goal is already stable:

- **target**: `finished → LLLReducedQ` (and later: a more semantic reformulation of `LLLReducedQ`).

## What “termination” means here

`lllRunExact` is **fuel-bounded**, so it is total by construction.
A termination proof is about the *unbounded* algorithmic behavior:

- show that there exists a bound `T(B, δ)` such that for all `limit ≥ T`,
  the runner reaches `.finished`.

Equivalently: define an unbounded loop and prove it terminates.

## The classic proof shape (what we’ll formalize)

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

## Concrete next lemma milestones (in order)

### A. A computable potential definition

- Add `potentialQ : Matrix (Fin n) (Fin n) ℤ → ℚ` (new file recommended).
- Prove basic facts:
  - `potentialQ` is a finite product over `Fin n`,
  - `dotQ v v = 0 ↔ v = 0` (already proved) will be the main lever for “nonzero under `RowLIQ`”.

### B. Swap-step decrease (main hard inequality)

- Prove: when `lovaszQ` fails at `(k, k-1)`, swapping decreases `potentialQ` strictly.
- This is the best place to use `proofpatch tree-search-nearest --smt-precheck`.

### C. Bound + termination wrapper

- Show `potentialQ` lives in a well-founded set:
  - either “positive rationals with bounded denominator”, or
  - “integers after scaling by a common denominator”.
- Conclude a bound on number of swaps.

### D. From “finite swaps” to “finished”

- Once swaps stop, show `k` only increases until it reaches `n`.

## References to mirror (structure, not code)

- Isabelle AFP: *LLL Basis Reduction* (proof decomposition + invariants)  
  `https://www.isa-afp.org/browser_info/current/AFP/LLL_Basis_Reduction/outline.pdf`

