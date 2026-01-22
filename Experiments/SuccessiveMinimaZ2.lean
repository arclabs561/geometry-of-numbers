import GeometryOfNumbers.Core.SuccessiveMinimaTheorems
import SuccessiveMinimaBasic

/-!
# Successive minima (ℤ²) — tiny exercised lemma

This file is intentionally small: it exists to ensure the successive-minima definitions and the
first theorem-layer lemmas typecheck *in a concrete setting* (ℤ² + unit disk).

We do **not** try to compute the exact value yet; we just prove a trivial bound.
-/

namespace GeometryOfNumbers.Experiments

open Set Pointwise

-- Reuse the definitions from `SuccessiveMinimaBasic.lean`.
open GeometryOfNumbers.Experiments (lattice_z2 unit_disk)

-- `lattice_z2` is a genuine ℤ-lattice (it is a `span ℤ (range basis)` with finite index type),
-- so Mathlib provides a `DiscreteTopology` instance once we unfold the definition.
local instance : DiscreteTopology (lattice_z2) := by
  -- The instance lives in `Mathlib.Algebra.Module.ZLattice.Basic`.
  simpa [lattice_z2] using
    (inferInstance :
      DiscreteTopology (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))))

noncomputable def e0 : Fin 2 → ℝ := Pi.basisFun ℝ (Fin 2) 0

lemma e0_mem_lattice_z2 : e0 ∈ lattice_z2 := by
  -- `lattice_z2` is the ℤ-span of the standard coordinate functions.
  refine Submodule.subset_span ?_
  refine ⟨(0 : Fin 2), rfl⟩

lemma e0_ne_zero : (e0 : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h0 : e0 0 = (0 : (Fin 2 → ℝ)) 0 := congrArg (fun f : Fin 2 → ℝ => f 0) h
  -- `Pi.basisFun` evaluates to `1` at its own coordinate.
  simp [e0] at h0

lemma e0_mem_unit_disk : e0 ∈ unit_disk := by
  -- For the sup norm on `Fin 2 → ℝ`, we have `‖Pi.single 0 1‖ = ‖1‖ = 1`.
  have hn : ‖e0‖ = (1 : ℝ) := by
    simp [e0, Pi.norm_single]
  -- Now discharge the goal `‖e0‖ ≤ 1`.
  simp [unit_disk, hn]

lemma one_mem_witnesses_z2_unit_disk :
    (1 : ℝ) ∈ successive_minima_witnesses lattice_z2 unit_disk 1 := by
  refine ⟨by norm_num, ?_⟩
  refine ⟨({e0} : Set (Fin 2 → ℝ)), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x = e0 := by simpa using hx
    subst hx'
    exact e0_mem_lattice_z2
  · simp
  · -- Linear independence of a singleton set reduces to `e0 ≠ 0`.
    -- Convert `LinearIndepOn` on `{e0}` into `LinearIndependent` on the subtype.
    have hIndepOn :
        LinearIndepOn ℝ (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) ({e0} : Set (Fin 2 → ℝ)) := by
      simpa using
        (linearIndepOn_singleton_iff (R := ℝ)
          (v := (id : (Fin 2 → ℝ) → (Fin 2 → ℝ))) (i := e0)).2 e0_ne_zero
    have hLI :
        LinearIndependent ℝ (Subtype.val : ({e0} : Set (Fin 2 → ℝ)) → (Fin 2 → ℝ)) :=
      (linearIndependent_subtype_iff (R := ℝ) (s := ({e0} : Set (Fin 2 → ℝ)))).2 hIndepOn
    simpa using hLI
  · simp
  · intro x hx
    have hx' : x = e0 := by simpa using hx
    subst hx'
    -- `1 • unit_disk = unit_disk`.
    simpa [one_smul] using e0_mem_unit_disk

lemma witnesses_z2_unit_disk_one_nonempty :
    (successive_minima_witnesses lattice_z2 unit_disk 1).Nonempty := by
  exact ⟨(1 : ℝ), one_mem_witnesses_z2_unit_disk⟩

lemma successive_minima_z2_unit_disk_one_le_one :
    successive_minima lattice_z2 unit_disk 1 ≤ 1 := by
  classical
  have hk : (1 : ℕ) ≤ 1 ∧ 1 ≤ 2 := by decide
  have hbdd : BddBelow (successive_minima_witnesses lattice_z2 unit_disk 1) :=
    successive_minima_witnesses_bddBelow (L := lattice_z2) (K := unit_disk) (k := 1)
  have hmem : (1 : ℝ) ∈ successive_minima_witnesses lattice_z2 unit_disk 1 :=
    one_mem_witnesses_z2_unit_disk
  have : sInf (successive_minima_witnesses lattice_z2 unit_disk 1) ≤ 1 :=
    csInf_le hbdd hmem
  -- Rewrite `successive_minima` to the `sInf` form.
  simpa [successive_minima_eq_sInf_of_range (L := lattice_z2) (K := unit_disk) (k := 1) hk] using this

/-!
We also “touch” the monotonicity lemma (in a trivial way) to ensure it stays usable.
-/
example :
    successive_minima lattice_z2 unit_disk 1 ≤ successive_minima lattice_z2 unit_disk 1 := by
  classical
  have hk : (1 : ℕ) ≤ 1 ∧ 1 ≤ 2 := by decide
  exact successive_minima_mono_k_of_nonempty
    (L := lattice_z2) (K := unit_disk) (hk1 := hk) (hk2 := hk) (h := le_rfl)
    witnesses_z2_unit_disk_one_nonempty

end GeometryOfNumbers.Experiments

