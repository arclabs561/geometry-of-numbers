# Proof Roadmap

## Dependency Graph

```
Nat.sum_four_squares (Mathlib)
         │
         ▼
sum_three_squares_of_not_exception  ◄── THE MAIN GAP (currently a scaffold)
         │
         ├──────────────────────────────┐
         ▼                              ▼
four_nonneg_sum_from_cauchy      gauss_eureka
         │                              │
         ▼                              │
cauchy_decomposition                    │
         │                              │
         ▼                              │
fermat_polygonal (s ≥ 5)    fermat_polygonal (s = 3)
```

## The Key Missing Piece: current structure

**`sum_three_squares_of_not_exception`** is intended to be routed through **Ankeny (1957)** (geometry-of-numbers).
At the moment this route **typechecks** but is not yet fully proved (several `sorry` remain).

### Ankeny's Proof (`Covolume/Legendre/Ankeny.lean`)

1.  **Ankeny Lemmas (proved)**: `Covolume/Legendre/AnkenyLemmas.lean` currently has **0** `sorry` and contains the
    squarefree decomposition + the mod‑8 squarefree-part lemma.
2.  **Lattice definition (typechecks)**: `ankeny_lattice` is defined as an `AddSubgroup (Fin 3 → ℝ)` encoding:
    \(x \equiv y \pmod n\) and \(y \equiv bz \pmod{2q}\).
3.  **Algebraic congruence glue (missing)**: `ankeny_Q_mod` should prove
    \(Q(x,y,z) = 2qx^2 + y^2 + nz^2 \equiv 0 \pmod{2nq}\) from lattice membership and the `b^2 ≡ -n` hypothesis.
    This is currently a `sorry`, but it is purely algebraic (no Minkowski yet).
4.  **Minkowski step (missing)**: `ankeny_lattice_covolume` + `exists_ankeny_representation` are scaffolds.
5.  **Descent / reduction (missing)**: `reduction_to_sum_three_squares` is a scaffold; see also `Experiments/AnkenyReduction.lean`.

## Cauchy's Lemma (`Covolume/Cauchy/Main.lean`)

Once we have the three-square theorem, `four_nonneg_sum_from_cauchy` follows by reducing the general `s`-gonal case to the sum of four `s`-gonal numbers.

## Timeline & Status

| Task | Status | Location |
|------|--------|----------|
| **Core Algebra** | Mixed | `Covolume/Core/Basic.lean` (proved), `Covolume/Core/ModularSquares.lean` (WIP; `sorry`) |
| **Ankeny Lemmas** | ✅ proved | `Covolume/Legendre/AnkenyLemmas.lean` (0 `sorry`) |
| **Ankeny main file** | 🚧 scaffold | `Covolume/Legendre/Ankeny.lean` (multiple `sorry`) |
| **Cauchy reduction** | 🚧 scaffold | `Covolume/Cauchy/Main.lean` (`sorry`) |
| **Gauss Eureka** | 🚧 scaffold | `Covolume/Cauchy/Main.lean` (`sorry`) |

## Evidence / experiments (why the scaffolds are shaped this way)

- `Experiments/CheckZMod.lean` contains compiling “bridge” examples used to avoid brittle rewriting when
  moving between `ZMod` equalities and `Int.ModEq` congruences, and for the CRT-style combination lemma.
- `uv run Experiments/ankeny_check.py` performs small numeric searches for witnesses in the Ankeny setup.
  This is not a proof, but it has been useful for validating the intended algebra before formalization.

## Notes on `Covolume/Legendre/Minkowski.lean`

`Covolume/Legendre/Minkowski.lean` is an exploratory Minkowski-centric attempt. We are currently prioritizing
the Ankeny route, but Minkowski experiments remain useful as a reference for the measure-theory API.
