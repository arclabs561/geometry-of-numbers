import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Minkowski engine lemmas (thin wrappers)

This module exists to keep **Minkowski call-sites** stable and readable.

Mathlib already has the core theorem; here we provide small adapter lemmas with argument order and
output shape that work well with this repo’s lattice/covolume infrastructure.
-/

noncomputable section

namespace GeometryOfNumbers

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

/-- A thin wrapper around Mathlib's Blichfeldt theorem.

This is the “pair not disjoint under translate” engine that Minkowski's theorem uses internally.

We expose it here because many GoN arguments want to invoke Blichfeldt directly once the covolume
computation (`μ F`) is available.
-/
theorem blichfeldt_exists_pair_mem_lattice_not_disjoint_vadd
    {E L : Type*} [MeasurableSpace E] (μ : Measure E) (F s : Set E)
    [AddGroup L] [Countable L] [AddAction L E] [MeasurableSpace L] [MeasurableVAdd L E]
    [MeasureTheory.VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ)
    (hS : MeasureTheory.NullMeasurableSet s μ)
    (h : μ F < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by
  simpa using MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd
    (μ := μ) (F := F) (s := s) fund hS h

/-- Covolume-shaped wrapper for Blichfeldt's theorem.

This is a rewrite helper, analogous to `minkowski_exists_ne_zero_mem_lattice_of_covolume_mul_two_pow_lt`.
It is useful when you have computed `μ F = covol` and want to state the hypothesis using `covol`
directly.
-/
theorem blichfeldt_exists_pair_mem_lattice_not_disjoint_vadd_of_covolume
    {E L : Type*} [MeasurableSpace E] (μ : Measure E) (F s : Set E)
    [AddGroup L] [Countable L] [AddAction L E] [MeasurableSpace L] [MeasurableVAdd L E]
    [MeasureTheory.VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ)
    (hS : MeasureTheory.NullMeasurableSet s μ)
    (covol : ℝ≥0∞)
    (hμF : μ F = covol)
    (h : covol < μ s) :
    ∃ x y : L, x ≠ y ∧ ¬Disjoint (x +ᵥ s) (y +ᵥ s) := by
  have h' : μ F < μ s := by simpa [hμF] using h
  exact blichfeldt_exists_pair_mem_lattice_not_disjoint_vadd (μ := μ) (F := F) (s := s) fund hS h'

/-- A thin wrapper around Mathlib's Minkowski theorem.

This is intentionally small: the “engine” is Mathlib; our value-add is a stable local interface.
-/
theorem minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    (μ : Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (L : AddSubgroup E) [Countable (↥L)]
    (F s : Set E)
    (hfund : IsAddFundamentalDomain L F μ)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (hineq : μ F * 2 ^ (Module.finrank ℝ E) < μ s) :
    ∃ p : L, p ≠ 0 ∧ (p : E) ∈ s := by
  simpa using
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (μ := μ) (L := L) (F := F) (s := s) hfund hsymm hconv hineq

/-- Minkowski (strict) with `volume` as the ambient Haar measure.

This is a small ergonomics wrapper for the common Euclidean/`Fin n → ℝ` use case: it avoids having
to write `(μ := volume)` at every call-site.
-/
theorem minkowski_exists_ne_zero_mem_lattice_of_volume_mul_two_pow_lt
    {n : ℕ}
    (L : AddSubgroup (Fin n → ℝ)) [Countable (↥L)]
    (F s : Set (Fin n → ℝ))
    (hfund : IsAddFundamentalDomain L F volume)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (hineq : volume F * 2 ^ (Module.finrank ℝ (Fin n → ℝ)) < volume s) :
    ∃ p : L, p ≠ 0 ∧ (p : (Fin n → ℝ)) ∈ s := by
  simpa using
    minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt
      (E := (Fin n → ℝ)) (μ := volume) (L := L) (F := F) (s := s) hfund hsymm hconv hineq

/-- Minkowski (strict), returning the witness in `E` with membership proof in `L`.

This is often the most convenient output shape when downstream steps want to avoid subtype coercions.
-/
theorem minkowski_exists_ne_zero_mem_lattice_of_volume_mul_two_pow_lt'
    {n : ℕ}
    (L : AddSubgroup (Fin n → ℝ)) [Countable (↥L)]
    (F s : Set (Fin n → ℝ))
    (hfund : IsAddFundamentalDomain L F volume)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (hineq : volume F * 2 ^ (Module.finrank ℝ (Fin n → ℝ)) < volume s) :
    ∃ x : (Fin n → ℝ), x ≠ 0 ∧ x ∈ L ∧ x ∈ s := by
  rcases
      minkowski_exists_ne_zero_mem_lattice_of_volume_mul_two_pow_lt
        (L := L) (F := F) (s := s) hfund hsymm hconv hineq with
    ⟨p, hp0, hp_mem⟩
  refine ⟨(p : (Fin n → ℝ)), ?_, ?_, hp_mem⟩
  · -- `p ≠ 0` in the subtype implies the coerced element is not `0`.
    intro h
    apply hp0
    apply Subtype.ext
    simpa using h
  · exact p.property

/-- A thin wrapper around Mathlib's “≤” Minkowski theorem.

Compared to `minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt`, this version requires
`s` to be compact and the lattice `L` to have the discrete topology, but it only assumes a weak
inequality.
-/
theorem minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (L : AddSubgroup E) [Countable (↥L)] [DiscreteTopology (↥L)]
    (F s : Set E)
    (hfund : IsAddFundamentalDomain L F μ)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (hcpt : IsCompact s)
    (hineq : μ F * 2 ^ (Module.finrank ℝ E) ≤ μ s) :
    ∃ p : L, p ≠ 0 ∧ (p : E) ∈ s := by
  simpa using
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure
      (μ := μ) (L := L) (F := F) (s := s) hfund hsymm hconv hcpt hineq

/-- Minkowski (non-strict) with `volume` as the ambient Haar measure. -/
theorem minkowski_exists_ne_zero_mem_lattice_of_volume_mul_two_pow_le
    {n : ℕ}
    [Nontrivial (Fin n → ℝ)]
    (L : AddSubgroup (Fin n → ℝ)) [Countable (↥L)] [DiscreteTopology (↥L)]
    (F s : Set (Fin n → ℝ))
    (hfund : IsAddFundamentalDomain L F volume)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (hcpt : IsCompact s)
    (hineq : volume F * 2 ^ (Module.finrank ℝ (Fin n → ℝ)) ≤ volume s) :
    ∃ p : L, p ≠ 0 ∧ (p : (Fin n → ℝ)) ∈ s := by
  simpa using
    minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le
      (E := (Fin n → ℝ)) (μ := volume) (L := L) (F := F) (s := s) hfund hsymm hconv hcpt hineq

/-- Covolume-shaped wrapper for the strict Minkowski inequality.

This is just a rewrite helper: if you have already computed `μ F = covol` (e.g. from an explicit
fundamental domain volume computation), you can state the Minkowski inequality using `covol`
directly.
-/
theorem minkowski_exists_ne_zero_mem_lattice_of_covolume_mul_two_pow_lt
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E]
    (μ : Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (L : AddSubgroup E) [Countable (↥L)]
    (F s : Set E)
    (hfund : IsAddFundamentalDomain L F μ)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (covol : ℝ≥0∞)
    (hμF : μ F = covol)
    (hineq : covol * 2 ^ (Module.finrank ℝ E) < μ s) :
    ∃ p : L, p ≠ 0 ∧ (p : E) ∈ s := by
  have hineq' : μ F * 2 ^ (Module.finrank ℝ E) < μ s := by
    simpa [hμF] using hineq
  exact
    minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt
      (μ := μ) (L := L) (F := F) (s := s) hfund hsymm hconv hineq'

/-- Covolume-shaped wrapper for the non-strict Minkowski inequality.

This is the “≤” analog of `minkowski_exists_ne_zero_mem_lattice_of_covolume_mul_two_pow_lt`.
-/
theorem minkowski_exists_ne_zero_mem_lattice_of_covolume_mul_two_pow_le
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (μ : Measure E) [MeasureTheory.Measure.IsAddHaarMeasure μ]
    (L : AddSubgroup E) [Countable (↥L)] [DiscreteTopology (↥L)]
    (F s : Set E)
    (hfund : IsAddFundamentalDomain L F μ)
    (hsymm : ∀ x ∈ s, -x ∈ s)
    (hconv : Convex ℝ s)
    (hcpt : IsCompact s)
    (covol : ℝ≥0∞)
    (hμF : μ F = covol)
    (hineq : covol * 2 ^ (Module.finrank ℝ E) ≤ μ s) :
    ∃ p : L, p ≠ 0 ∧ (p : E) ∈ s := by
  have hineq' : μ F * 2 ^ (Module.finrank ℝ E) ≤ μ s := by
    simpa [hμF] using hineq
  exact
    minkowski_exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le
      (μ := μ) (L := L) (F := F) (s := s) hfund hsymm hconv hcpt hineq'

end GeometryOfNumbers

