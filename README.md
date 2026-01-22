## Geometry of Numbers (Lean)

[![Lean Action CI](https://github.com/arclabs561/geometry-of-numbers/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/arclabs561/geometry-of-numbers/actions/workflows/lean_action_ci.yml)

Lean 4 formalization around a geometry-of-numbers route to:

- **Legendre’s three-square theorem** (Ankeny 1957 + Minkowski)
- **Cauchy’s reduction** for Fermat’s polygonal number theorem

This repo is intended to stay **buildable and `sorry`-free**; see `just status` / `lake exe status_report`.
Some modules are still **scaffolds** in the sense of “compiles, but not the final story” (e.g. the LLL work).

Dual-licensed under MIT or Apache-2.0.

### Quickstart

Install Lean (one-time; pinned by `lean-toolchain`):

```bash
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh
```

Or via Homebrew (macOS):

```bash
brew install elan-init
elan-init -y
```

Build and run local checks:

```bash
# If `lake` isn't on PATH, use `~/.elan/bin/lake` (or just use `just`, which defaults to it).
lake build
./Scripts/check.sh pre-commit
./Scripts/check.sh pre-push
```

Fast feedback loop (recommended during active work):

```bash
just fast
just status
just ankeny
just regen-check
```

### Generated artifacts + safety

- **Generated tables are audited**: `just regen-check` regenerates Cauchy medium-regime tables into `.generated/` and fails on drift.
- **Artifacts are local-only**: `tmp/` and `.generated/` are gitignored.
- **Secrets**: `.env` is gitignored. Don’t commit API keys; prefer env vars or a local `.env` file.

### Two formulas

Three-square “exception” numbers have the form:

$$
n = 4^a(8k+7).
$$

Ankeny’s descent is organized around the ternary quadratic form:

$$
Q(x,y,z) = 2qx^2 + y^2 + nz^2.
$$

## What’s here (roughly)

- `GeometryOfNumbers.lean`: public import root
- `GeometryOfNumbers/Core/`: reusable lemmas/definitions (some files are still scaffolds)
- `GeometryOfNumbers/Legendre/`: the Ankeny proof path and the three-square theorem entry point
- `GeometryOfNumbers/Cauchy/`: the polygonal-number reduction (currently scaffolded)
- `GeometryOfNumbers/Computable/LLL.lean`: LLL scaffold; see also `Experiments/LLLRational.lean`
- `Experiments/`: small probes and scratch files; these are allowed to use `sorry` but must compile

### Tooling

`./Scripts/check.sh pre-commit` runs `lake exe gon_checks` + lint-style. If a sibling checkout of `../proofpatch`
exists (or `proofpatch` is on PATH), it also runs a bounded “review-diff” step via the Rust helper CLI
(non-blocking unless strict). Back-compat: a `../proofloops` checkout is also recognized (legacy name).

Controls:
- `GON_LLM_REVIEW=0` disables the review step
- `GON_LLM_REVIEW_STRICT=1` makes “no reviewer available” / “review failed” fail the check
- `GON_ARTIFACT_DIR` sets the local artifact directory (default: `tmp/proofpatch/`; legacy: `tmp/proofloops/`)
- `GON_LLM_REVIEW_PRINT=0` suppresses printing `review_text` to stdout (JSON artifact still written)
- `GON_LLM_REVIEW_FAIL_VERDICT=request_changes` fails the check if the reviewer verdict is `request_changes`
- `GON_LLM_REVIEW_VERIFY_TIMEOUT_S` / `GON_LLM_REVIEW_VERIFY_MAX_FILES` tune how much Lean verification `review-diff` performs

If LLM review is enabled, `./Scripts/check.sh` also supports bounding the prompt pack (useful when
providers have tight context windows):

- `GON_LLM_REVIEW_MAX_TOTAL_BYTES` (default: 40000)
- `GON_LLM_REVIEW_PER_FILE_BYTES` (default: 8000)
- `GON_LLM_REVIEW_TRANSCRIPT_BYTES` (default: 8000)

## Structure

```
GeometryOfNumbers/
  Core/
    Basic.lean            -- Polygonal number definitions and identities.
    QuadraticLattice.lean -- Quadratic forms ↔ lattices (scaffold).
    SuccessiveMinima.lean -- Lattice spectral theory.
    SuccessiveMinimaTheorems.lean -- Theorem layer (monotonicity, etc.).
    Composition.lean      -- Composition-law scaffolding.
    ModularSquares.lean   -- Local solvability conditions.
    Determinant.lean      -- Lattice determinant and covolume links.
    MinkowskiEngine.lean  -- Thin wrapper around Mathlib's Minkowski theorem (stable call-site).
  Computable/
    LLL.lean              -- LLL scaffold.
  Legendre/
    AnkenyLemmas.lean     -- Squarefree decomposition and mod-8 logic.
    Ankeny.lean           -- Ankeny (1957) descent proof.
    Main.lean             -- Legendre's Three-Square Theorem entry point.
  Cauchy/
    Main.lean             -- Cauchy Lemma and Fermat Polygonal Theorem reduction.
    MediumTablesSmall.lean -- Generated (sharded) medium-regime tables for `5 ≤ s ≤ 23`.
    MediumTablesMge22.lean -- Generated medium-regime tables for `s-2 ≥ 22`.
    MediumTablesSmall/      -- Shards `S05..S23` imported by `MediumTablesSmall.lean`.

Scripts/
  StatusReport.lean          -- Project status summary generator.

Experiments/
  CheckZMod.lean             -- Congruence bridge validation.
  AnkenyCheck.lean           -- Ankeny prime existence probes.
  LLLBasic.lean              -- LLL step and Gram-Schmidt probing.
  SuccessiveMinimaBasic.lean -- Successive minima: definitions + notes.
  SuccessiveMinimaZ2.lean    -- ℤ² + unit disk: tiny exercised lemma (witness nonempty, λ₁ ≤ 1).
  PoissonTheta.lean          -- Poisson summation → theta identity (Mathlib infrastructure check).
  BhargavaCubes.lean         -- Discriminant invariant checks.
  DescentValuation.lean      -- Valuation contradiction formalization.
```

## Entry points (some are scaffolds)

**Legendre's Three-Square Theorem** (target):
```lean
theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ is_three_square_exception n
```

**Gauss's Triangular Number Theorem** (target):
```lean
theorem gauss_triangular (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n
```

**Fermat's Polygonal Number Theorem** (target):
```lean
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n
```

## Note: Nathanson (1987)
For the `s ≥ 5` case, we target the Cauchy/Nathanson reduction in the “four terms + residue” form
$n = \sum_{i=1}^4 P(s,x_i) + r$ with $0 \le r \le s-4$, then pad with `0/1` polygonals.

There is a known residue-class gap in some short presentations; we are following the modern
streamlined route (e.g. Nathanson’s book treatment / the Whitty talk notes) rather than relying on
an unverified modulo argument.

## References

- Legendre, A. M. (1798). *Essai sur la théorie des nombres*.
- Cauchy, A. L. (1813). *Démonstration du théorème général de Fermat sur les nombres polygones*.
- Ankeny, N. C. (1957). *Sums of three squares*. Proceedings of the American Mathematical Society.
- Nathanson, M. B. (1987). *A short proof of Cauchy's polygonal number theorem*.
- Bhargava, M. (2004). *Higher composition laws*. Annals of Mathematics.
