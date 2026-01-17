# Polygonal Number Theorem

Formalization of **Legendre's Three-Square Theorem** and the **Fermat/Cauchy Polygonal Number Theorem** in Lean 4.

Dual-licensed under MIT or Apache-2.0.

```sh
# Install Lean + lake (one-time). This repo is pinned by `lean-toolchain`.
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

```
lake build
lake exe status_report
```

If `lake` isn’t on your PATH, try `"$HOME/.elan/bin/lake"` instead.

Note: this workspace also has a sibling directory `../PolygonalNumberTheorem/` with
scratch Lean files. We’re merging useful bits into this repo (copying, not deleting).

## Status

`lake build` succeeds, but the development files still contain `sorry` placeholders.
Treat “done” as “typechecks”, not “fully proved”.

As of Jan 2026 (rough accounting):
- `Legendre/AnkenyLemmas.lean` has **0** `sorry` (it is the cleanest “finished” component).
- The main development spine still has **21** `sorry` occurrences across:
  - `Legendre/Ankeny.lean` (6)
  - `Legendre/Minkowski.lean` (6)
  - `Cauchy/Main.lean` (5)
  - `Legendre/Main.lean` (2)
  - `Core/ModularSquares.lean` (2)

## Structure

```
PolygonalNumberTheorem/
  Core/Basic.lean            -- polygonal(s,n) definition + algebra spine
  Core/ModularSquares.lean   -- modular “u²+v²+1≡0” root existence (WIP)
  Legendre/Exceptions.lean   -- exception set: 4^a(8k+7)
  Legendre/Minkowski.lean    -- Minkowski/descent scaffolding (WIP)
  Legendre/AnkenyLemmas.lean -- squarefree decomposition + mod-8 lemma glue (proved)
  Legendre/Ankeny.lean       -- Ankeny proof skeleton (WIP; several `sorry`)
  Legendre/Main.lean         -- Legendre statement + glue to proof attempt (WIP)
  Cauchy/Main.lean           -- Cauchy lemma + polygonal theorem scaffolding (WIP)

Scripts/
  StatusReport.lean          -- prints the current (manual) status summary

Experiments/
  CheckZMod.lean             -- compiling “bridge lemmas” for ZMod ⇄ Int.ModEq + CRT
  AnkenyCheck.lean           -- API probes / scratch for Ankeny steps
  ankeny_check.py            -- numeric sanity checks for small n (not a proof)
```

## Key Theorems

**Legendre** (characterization):
```lean
theorem sum_three_squares_iff (n : ℕ) :
    (∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n) ↔ ¬ is_three_square_exception n
```

**Gauss Eureka** (every n is sum of 3 triangular numbers):
```lean
theorem gauss_eureka (n : ℕ) :
    ∃ a b c : ℕ, triangular a + triangular b + triangular c = n
```

**Fermat Polygonal** (every n is sum of s s-gonal numbers):
```lean
theorem fermat_polygonal (s : ℕ) (hs : 3 ≤ s) (n : ℕ) :
    ∃ terms : Fin s → ℕ, (∑ i, polygonal s (terms i)) = n
```

## Evidence (practical, not formal)

This repo keeps a small amount of *executable evidence* to reduce proof friction:

- **Cast / congruence bridges**: `Experiments/CheckZMod.lean` contains compiling examples for the
  exact bridge pattern used in `Legendre/Ankeny.lean`:
  \( (q : ZMod\,n) = -(2 : ZMod\,n)^{-1} \Rightarrow 2q \equiv -1 \pmod n \)
  and a minimal use of `Int.modEq_and_modEq_iff_modEq_mul` (CRT-style combination).

- **Numeric sanity checks**: `uv run Experiments/ankeny_check.py` searches for small witnesses
  in the Ankeny quadratic form setup and checks the “\(n - x^2\) is a sum of two squares” condition
  on a sample of inputs. This is *not* a substitute for proofs, but it is useful for catching
  sign/cast mistakes and for validating “this should be true” before spending hours in Lean.

## Proof Strategy for Legendre Hard Direction

The main blocker. Three possible approaches:

1. **Minkowski** (geometry of numbers): Show a lattice point exists in a suitable region
2. **Ankeny** (elementary): Use primes in arithmetic progressions
3. **Reduction theory**: Show x² + y² + z² represents all valid n via class number 1

## References

- Legendre (1798). *Essai sur la théorie des nombres*.
- Cauchy (1813). *Démonstration du théorème général de Fermat*.
- Ankeny (1957). *Sums of three squares*. Proc. AMS.
- Nathanson (1987). *A short proof of Cauchy's polygonal number theorem*.
