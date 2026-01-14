# Proof Roadmap

## Dependency Graph

```
Nat.sum_four_squares (Mathlib)
         │
         ▼
sum_three_squares_of_not_exception  ◄── THE MAIN GAP
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

## The Key Missing Piece

**`sum_three_squares_of_not_exception`**: Every n NOT of the form 4^a(8k+7) is a sum of three squares.

### Why It's Hard

Unlike the two-square and four-square theorems, the three-square theorem is a
*characterization* - it says exactly which numbers ARE representable. The proof
requires either:

1. **Geometry of numbers** (Minkowski): Existence of lattice points in convex bodies
2. **Elementary descent** (Ankeny): Primes in arithmetic progressions
3. **Quadratic form theory**: Class number calculations

### What We Have

The **easy direction** is done: if n = x² + y² + z², then n ≢ 4^a(8k+7).

Proof: By descent. If 4|n and n is sum of 3 squares, then all three squares are
even (mod 4 argument), so n/4 is also a sum of 3 squares. Repeat until n is not
divisible by 4. Then n ≡ 0,1,2,3,4,5,6 (mod 8), never 7.

## Recommended Path: Minkowski

The geometry-of-numbers approach is cleanest for formalization:

### Step 1: Odd n ≢ 7 (mod 8)

For odd n, the lattice is ℤ³. We need a point (x,y,z) ∈ ℤ³ with 0 < x²+y²+z² ≤ n.

The ball B(√n) has volume (4π/3)n^{3/2}. For n ≥ 2, this exceeds 8 = 2³·det(ℤ³),
so Minkowski's theorem gives a nonzero lattice point.

### Step 2: n ≡ 2 (mod 4)

Since n ≡ 2 (mod 4) implies n ≢ 7 (mod 8), and squares mod 4 are {0,1}, we need
exactly two odd squares. Similar Minkowski argument on a sublattice.

### Step 3: n ≡ 1 (mod 4)

Similar to Step 1, but may need sublattice for parity.

### Step 4: Descent for n ≡ 0 (mod 4)

Already done in `SumThreeSquares.lean`: if 4|n and n = x²+y²+z², then n/4 = x'²+y'²+z'².

## Mathlib Resources

Potentially useful:
- `Mathlib.Analysis.Normed.Group.Lemmas` - norms
- `Mathlib.NumberTheory.Zsqrtd` - ℤ[√d] for lattice construction  
- `Mathlib.Topology.MetricSpace.Basic` - balls

Not yet in Mathlib (would need):
- Minkowski's convex body theorem for general lattices
- Volume calculations for sublattices of ℤⁿ

## Alternative: Quaternion Proof

The four-square theorem proof in Mathlib uses Euler's identity. A similar approach
for three squares would use the Hurwitz integers (quaternions with half-integer
coordinates when all four are half-integers).

This is more algebraic but requires:
- Hurwitz integer arithmetic
- Norm form analysis
- Showing the form x²+y²+z² has class number 1

## Cauchy's Lemma

Once we have the three-square theorem, `four_nonneg_sum_from_cauchy` follows by:

1. Given odd a, b satisfying Cauchy conditions, compute c = 4a - b²
2. Show c ≡ 3 (mod 8), hence not exceptional
3. Apply three-square theorem: c = x² + y² + z² with x,y,z odd
4. Construct s,t,u,v by solving:
   - s + t + u + v = b
   - s² + t² + u² + v² = a
   
   Using s = (b+x+y+z)/4, t = (b+x-y-z)/4, etc. (with appropriate sign for z)

## Timeline Estimate

| Task | Difficulty | Dependencies |
|------|------------|--------------|
| Minkowski base cases | Medium | Mathlib lattice/measure theory |
| Volume calculations | Medium | Mathlib measure theory |
| Sublattice construction | Easy | Basic linear algebra |
| Integration | Easy | Above pieces |
| Cauchy from Legendre | Easy | Legendre hard direction |
| Polygonal s≥5 | Medium | Cauchy's lemma |
