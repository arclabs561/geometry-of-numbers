# LLL complexity notes (Computable / exact track)

This note records the *next* phase of the computable LLL track: moving from “it finishes” to a
**recognizable complexity bound** (swap/iteration count) comparable to the textbook LLL story.

Code pointers:

- Termination proof + explicit fuel bound: `GeometryOfNumbers/Computable/LLLExactTermination.lean`
- Postcondition: `finished → LLLReducedQ`: `GeometryOfNumbers/Computable/LLLExactProofs.lean`

## What we already have (a checkable bound)

`LLLExactTermination.lean` proves a concrete measure `termMeasure(B,k)` and shows:

- if `fuel ≥ termMeasure(B,k) + 1` then `lllRunExactGo B δ k steps fuel` reaches `.finished`,
- in particular, for the entry state `(k=1, steps=0)`:
  `limit ≥ termMeasure(B,1) + 1` implies `(lllRunExact B δ limit).reason = .finished`.

This is already a *complexity-style* statement: **the run finishes within a known number of
recursive steps**. What it is *not yet* is a “textbook LLL complexity bound”, because it does not
relate `termMeasure` to input bit-length in the usual way.

## Potential functions: mapping our definitions to the textbook ones

Textbook LLL analyses usually use a multiplicative potential such as
\[
\Phi(B) := \prod_{i=0}^{n-1} \lVert b_i^\*\rVert^2^{(n-1-i)}.
\]

In `LLLExactTermination.lean` we use the “product of prefix volumes” version (`potentialVQ`),
and keep the “textbook exponent” form as `potentialPhiQ` (a named reference).

The file’s default `potentialQ` is an alias for `potentialVQ` (good default for proofs).
\[
\Psi(B) := \prod_{k=0}^{n-1} V_k(B),
\quad
V_k(B) := \prod_{i=0}^{k-1} \lVert b_i^\*\rVert^2.
\]

These are equivalent by rearranging exponents:
\[
\Psi(B) = \prod_{i=0}^{n-1} \lVert b_i^\*\rVert^2^{(n-1-i)} = \Phi(B).
\]

Why `Ψ` is convenient in Lean:

- each `V_k` can be bridged to a **Gram determinant** (`det gramPrefix`) and is order-invariant,
- size-reduction operations preserve each prefix Gram determinant,
- a Lovász-failing adjacent swap strictly decreases the one prefix factor that matters.

## What “complexity” should mean in this repo

There are three different “bound stories”, all useful but with different difficulty:

- **A. Termination/fuel bound (already done)**: “there exists a concrete `T(B,δ)` so the runner
  is finished for all `limit ≥ T`.” This is what `termMeasure` gives today.
- **B. Swap/iteration count bound (next target)**: show a bound on the number of swaps (or
  Lovász-failure branches) in terms of a potential decrease argument.
- **C. Bit complexity / polynomial-time bound**: relate (B) to input size (bit lengths), and
  account for arithmetic costs (exact-ℚ vs floating-point LLL).

For this repository’s goals, (B) is the “most important next” step: it turns the proof into a
recognizable LLL analysis without dragging in a large bit-complexity development immediately.

## Immediate “swap count” bound we can already state (but it’s weak)

Because we also build an integer/Nat-valued potential `potentialVN` and show it strictly decreases
on every Lovász-failing swap, we automatically get:

- number of swaps is at most `potentialVN(B₀)` (minus 1).

Concrete theorems (so this doesn’t drift):

- `swapCountGo_le_potentialVN`: `swapCountGo B δ k fuel ≤ potentialVN B`
- `swapCount_le_potentialVN`: `swapCount B δ limit ≤ potentialVN B`

This is *mathematically correct* but not the classical bound (it is typically enormous).
To get a useful bound, we want a **multiplicative decrease** story (or a log bound), and we want a
lower bound on the potential (often in terms of `det(L)`).

## Useful external references (for structure to mirror)

We’re not copying these proofs; the point is to mirror the decomposition and identify which
lemmas correspond to which “leaf” obligations in Lean.

- Chen–Stehlé–Villard, *Computing an LLL-reduced basis of the orthogonal lattice* (2018).
  This is directly relevant because it discusses **iteration count bounds** using a variant
  of the classical potential. `http://arxiv.org/abs/1805.03418`
- Van Hoeij–Novocin, *Gradual sub-lattice reduction and a new complexity for factoring polynomials* (2010).
  Useful for thinking about complexity bounds that depend on an output norm bound rather than raw
  input bit-length. `http://arxiv.org/abs/1002.0739`
- Novocin–Stehlé–Villard, *An LLL-reduction algorithm with quasi-linear time complexity* (STOC 2011, extended abstract).
  This is the key reference once we want to move from “swap-count bound” to **bit complexity** bounds.
  Open PDF (HAL): `https://ens-lyon.hal.science/ensl-00534899/file/L1-hal.pdf`
- Lyu–Ling, *Boosted KZ and LLL Algorithms* (2017). A modern view of LLL variants; occasionally
  helpful for framing alternative potentials. `http://arxiv.org/abs/1703.03303`

### What to mirror from Chen–Stehlé–Villard (high signal)

The paper `http://arxiv.org/abs/1805.03418` is valuable because it restates the standard
termination/complexity decomposition in a way that matches our existing Lean structure:

- **Lemma 2.1 (swap step facts)**: the swap only affects two adjacent Gram–Schmidt norms, preserves
  their product, and increases the “bad” ratio by a constant factor.
- **Classical potential** (their Eq. (6)): a log-sum potential
  \(\Pi(B) = \sum_{i=1}^{n-1} (n-i)\log \lVert b_i^\*\rVert\),
  which is equivalent to a multiplicative potential (avoid logs in Lean by working with products).
- **Potential drop per swap**: they show a *uniform* lower bound on potential decrease per swap
  (their Proposition 3.2 uses \(\log(2/\sqrt{3})\) for \(\delta=3/4\)).
- **A refined potential \(\Pi_k\)**: tailored to “unbalanced” bases (many small vs many large GS
  norms), yielding a better bound on swap count for structured inputs.

What this suggests for our repo:

- keep our multiplicative `Ψ`/`Φ` as the “baseline textbook” potential,
- add an **optional refined potential** (a `k`-split analogue) once we have a concrete target family
  of inputs (e.g. the “orthogonal lattice” shaped bases, or the Legendre/Ankeny bridge matrices),
- prove a bound in the style “each swap decreases the potential by at least a fixed multiplicative
  factor”, then turn it into a **log-free swap count bound** using `pow` monotonicity.

## Optional tooling: `proofpatch research-auto` (LL ops)

This repo ships a small `proofpatch.toml` with a preset meant for this file:

```bash
proofpatch research-auto --repo . --preset lll_complexity --output-json /tmp/lll_complexity_research.json
```

The `lll_complexity` preset uses **two** filters:

- `must_include_any`: keep results “LLL-ish” (avoid SWAP/QCD hits).
- `must_include_all`: pin to a specific family/phrase (e.g. `"orthogonal lattice"`).

This is not a dependency of the Lean proof (it’s just a way to keep research notes reproducible).

## Concrete next Lean lemma targets (in order)

1. **Monotone-fuel wrapper** (done): a theorem of the form
   `limit ≥ termMeasure(B,1)+1 → finished`. (This is now in `LLLExactTermination.lean`.)
2. **Swap-count extraction** (done, basic): define a computable `swapCount` that mirrors the runner,
   and prove the “sanity bounds”:
   - `swapCount ≤ limit` (always), and
   - `swapCount (limit = termMeasure+1) ≤ termMeasure+1`.
   This is now in `LLLExactTermination.lean` as `swapCountGo` / `swapCount`.
3. **Textbook-potential lemma pack**:
   - show `Ψ = Φ` (pure algebra / `Finset` products),
   - isolate the exact “swap decreases Φ by factor δ” lemma in the statement form used in books.
4. **Lower bound on the potential**:
   - connect prefix Gram determinants to `det(L)`-style invariants,
   - extract a nontrivial lower bound (so a multiplicative-decrease → logarithmic swap bound).

Once (4) exists, the “classic” inequality chain becomes available:
\[
\#\text{swaps} \;\le\; \frac{\log(\Phi(B_0)) - \log(\Phi_{\min})}{\log(1/\delta)}.
\]

We can keep logs out of Lean by proving an equivalent statement with integer floors/ceils and
monotonicity of `pow` (this is usually the cleanest formalization strategy).

