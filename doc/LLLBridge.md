# LLL ↔ Legendre/Cauchy: why this track exists

This repo has two “main theorem” tracks:

- **Legendre / Ankeny**: Minkowski-style existence arguments in \( \mathbb{R}^3 \).
- **Cauchy / Nathanson**: a modular+case-split route to polygonal number representations.

The **computable LLL** track (`GeometryOfNumbers/Computable/LLLExact*.lean`) is intentionally
orthogonal to both: it is not required for the current proofs to go through.

So why invest in it?

## 1) A constructive analogue of Minkowski witnesses

Minkowski’s theorem guarantees *existence* of a nonzero lattice point in a large symmetric convex
body, but it does not give a witness algorithmically.

In low dimensions, the usual constructive story is:

- reduce the basis (LLL / Gauss reduction),
- enumerate short combinations in the reduced basis,
- find a small vector that lies in the target region.

This is the practical “bridge” between covolume/determinant arguments and actual witnesses.

### Concrete touchpoint in this repo

In `GeometryOfNumbers/Legendre/Ankeny.lean`, the covolume computation uses an explicit span basis
matrix with integer entries (written as an \( \mathbb{R} \)-matrix for the measure-theory pipeline).

`Experiments/LLLAnkenyBridge.lean` builds the corresponding **integer** matrix and runs the exact-ℚ
LLL reducer on its transpose (since our LLL code treats rows as basis vectors).

This experiment is not part of the proof; it exists as:

- a sanity bridge (the LLL code is “about the same lattice” as the Minkowski call-site),
- a motivation anchor for future work: *constructive Minkowski witnesses* in small dimensions.

## 2) Shared “volume-squared” invariants

Both Minkowski-style arguments and LLL termination proofs want the same kind of invariant:

- lattice volume / covolume (determinants),
- Gram matrices (“volume squared” as `det(Gram)`),
- invariance under unimodular row operations (swaps / transvections).

The `LLLExactTermination.lean` scaffolding is pushing toward a reusable statement:

- a prefix Gram determinant is an **integer** invariant,
- swaps that fail Lovász strictly decrease an appropriate integer-valued measure,
- therefore only finitely many swaps occur, and the fuel-bounded runner will finish for large enough fuel.

This is the “theory bridge”: it connects the computable LLL track to the same determinant/covolume
language already present in `GeometryOfNumbers/Core/Determinant.lean`.

## 3) Why this does not (yet) benefit the Cauchy track

The polygonal-number proof is dominated by:

- modular constraints,
- finite regime splitting,
- and precomputed “medium tables”.

LLL could still be used as a general-purpose “find short relation / small solution” heuristic,
but there is no clean, direct call-site today that improves the proof story (or removes tables).

So for now, the expected integration is:

- **Legendre/Ankeny**: constructive witnesses / sanity checks for the lattice step.
- **Core**: shared determinant/covolume abstractions.

