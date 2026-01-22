# Experiments (GeometryOfNumbers)

This directory contains **compiling scratchpads** for probing Mathlib APIs and validating “glue points”
between analysis/measure theory and arithmetic (lattices, covolumes, congruences).

## Contract

- **Every file here must compile** under `lake build`.
- Prefer **small, concrete examples** that pin down binder shapes and simp normal forms.
- Avoid `#eval` in `Experiments/` (it can run during `lake build`). If you need computation, add a
  `Scripts/*.lean` executable wrapper and run it via `lake exe ...`.

## How to run

From `geometry-of-numbers/`:

- `just experiments` (build all experiment roots explicitly)
- `just fast` (fast feedback lane; includes a couple key experiments)

## Priority experiment directions (backlog)

- **Minkowski ⇒ Dirichlet (Diophantine approximation)**:
 - goal: a small “bridge proof” that derives Dirichlet’s theorem from a Minkowski convex body argument.
 - good reference notes: <https://www.epfl.ch/labs/disopt/wp-content/uploads/2018/09/minkowski.pdf>
 - (related “algorithmic” viewpoint): <https://www.math.ucla.edu/~wdduke/preprints/minkJTNB.pdf>

- **Poisson summation + theta series (analytic bridge)**:
 - goal: make a clean experimental path from “lattice as a discrete subgroup” → Poisson summation → a theta-series identity.
 - reference notes: <https://personal.math.ubc.ca/~lior/teaching/1011/613D_F10/Fourier+PoissonSum.pdf>
 - this is a natural bridge toward lattice point counting / transference via analytic methods.

- **Space of lattices / moduli viewpoint (dynamics bridge)**:
 - goal: a toy “\(n=2\)” story: classify lattices up to isometry and connect with fundamental domains.
 - reference notes: <https://math.berkeley.edu/~fengt/245C_2016.pdf>

- **Transference (polar bodies, dual lattices, successive minima)**:
 - goal: build a small “definitions + lemma stubs + examples” file that pins down the exact Mathlib objects used
   for transference statements (polar body, covering radius, successive minima of dual).
 - one modern entrypoint touching theta-series + transference context: <https://nyjm.albany.edu/j/2025/31-45v.pdf>
 - successive minima survey (useful for statement shapes and historical context): <https://arxiv.org/pdf/2304.00120>
