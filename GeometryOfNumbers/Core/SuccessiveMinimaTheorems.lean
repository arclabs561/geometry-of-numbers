import GeometryOfNumbers.Core.SuccessiveMinima

/-!
# Successive minima: theorem layer

This file contains **theorems about** `successive_minima`, keeping the base definition file
(`Core/SuccessiveMinima.lean`) small and stable.
-/

namespace GeometryOfNumbers

open Set Pointwise

lemma successive_minima_witnesses_bddBelow {n : ℕ}
    (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L]
    (K : Set (Fin n → ℝ)) (k : ℕ) :
    BddBelow (successive_minima_witnesses L K k) := by
  refine ⟨0, ?_⟩
  intro r hr
  exact le_of_lt hr.1

/-- Successive minima are nonnegative when the witness set is nonempty.

This is the safe statement shape for `sInf` on a conditionally complete order: without a nonempty
assumption, `sInf` can have “default” behavior that depends on the instance.
-/
lemma successive_minima_nonneg_of_nonempty {n : ℕ}
    (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L]
    (K : Set (Fin n → ℝ)) (k : ℕ)
    (hne : (successive_minima_witnesses L K k).Nonempty) :
    0 ≤ successive_minima L K k := by
  classical
  by_cases hk : (1 ≤ k ∧ k ≤ n)
  · have hbdd : BddBelow (successive_minima_witnesses L K k) :=
      successive_minima_witnesses_bddBelow (L := L) (K := K) (k := k)
    have : 0 ≤ sInf (successive_minima_witnesses L K k) :=
      le_csInf hne (by
        intro r hr
        exact le_of_lt hr.1)
    simpa [successive_minima_eq_sInf_of_range (L := L) (K := K) (k := k) hk] using this
  · simp [successive_minima_eq_zero_of_not_range (L := L) (K := K) (k := k) hk]

/-!
## Monotonicity in `k`

Requiring more linearly independent lattice points cannot make the infimum smaller.

This lemma is stated in a way that matches the *conditional* nature of `sInf` on `ℝ`:
we assume the witness set at `k2` is nonempty so the infimum behaves like a true `Inf`.
-/

lemma successive_minima_mono_k_of_nonempty {n : ℕ}
    (L : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L]
    (K : Set (Fin n → ℝ)) {k1 k2 : ℕ}
    (hk1 : 1 ≤ k1 ∧ k1 ≤ n) (hk2 : 1 ≤ k2 ∧ k2 ≤ n) (h : k1 ≤ k2)
    (hne : (successive_minima_witnesses L K k2).Nonempty) :
    successive_minima L K k1 ≤ successive_minima L K k2 := by
  classical
  have hS : successive_minima_witnesses L K k2 ⊆ successive_minima_witnesses L K k1 := by
    intro r hr
    rcases hr with ⟨hr0, s, hsL, hsc, hlin, hcard, hsK⟩
    have hk1_le : k1 ≤ s.ncard := by simpa [hcard] using h
    obtain ⟨t, ht_sub, ht_card⟩ := Set.exists_subset_card_eq (s := s) hk1_le
    refine ⟨hr0, t, ?_, (Set.Countable.mono ht_sub hsc), ?_, ht_card, ?_⟩
    · intro x hx
      exact hsL x (ht_sub hx)
    · let hincl : t → s := fun x => ⟨x.1, ht_sub x.2⟩
      have hinj : Function.Injective hincl := by
        intro a b hab
        apply Subtype.ext
        have : (hincl a).1 = (hincl b).1 := congrArg (fun x : s => x.1) hab
        simpa [hincl] using this
      have hlin' :
          LinearIndependent ℝ ((fun x : s => (x : Fin n → ℝ)) ∘ hincl) :=
        hlin.comp hincl hinj
      simpa [Function.comp, hincl] using hlin'
    · intro x hx
      exact hsK x (ht_sub hx)
  have ht : BddBelow (successive_minima_witnesses L K k1) :=
    successive_minima_witnesses_bddBelow (L := L) (K := K) (k := k1)
  have hinf :
      sInf (successive_minima_witnesses L K k1) ≤
        sInf (successive_minima_witnesses L K k2) := by
    simpa using (csInf_le_csInf (t := successive_minima_witnesses L K k1)
      (s := successive_minima_witnesses L K k2) ht hne hS)
  simpa [successive_minima_eq_sInf_of_range (L := L) (K := K) (k := k1) hk1,
        successive_minima_eq_sInf_of_range (L := L) (K := K) (k := k2) hk2] using hinf

end GeometryOfNumbers

