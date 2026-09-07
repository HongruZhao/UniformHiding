import Mathlib.Probability.Independence.Process.Basic

/-!
# Grouping mutually independent coordinates

This file proves the elementary independence lemma needed when disjoint
families of Gaussian rows are bundled into matrix blocks.  It contains no
model-specific assumption.
-/

open MeasureTheory Set
open ProbabilityTheory

namespace LogdetLean.GramHafnian.ThreePaper.GroupedIndependence

noncomputable section

variable {Omega iota kappa : Type*} [MeasurableSpace Omega]

/-- Mutually independent coordinate sigma-algebras remain mutually
independent after grouping them into pairwise disjoint finite blocks. -/
theorem iIndep_grouped_iSup
    {mu : Measure Omega} {m : iota -> MeasurableSpace Omega}
    (hm_le : forall i, m i <= (inferInstance : MeasurableSpace Omega))
    (hm_indep : iIndep m mu)
    (S : kappa -> Finset iota)
    (hS : Pairwise fun a b => Disjoint (S a) (S b)) :
    iIndep (fun a => ⨆ i ∈ (S a : Set iota), m i) mu := by
  classical
  letI : IsProbabilityMeasure mu := hm_indep.isProbabilityMeasure
  rw [iIndep_iff]
  intro T f hf
  induction T using Finset.induction_on with
  | empty =>
      simpa using measure_univ
  | @insert a T ha ih =>
      let U : Set iota := ⋃ j ∈ (T : Set kappa), (S j : Set iota)
      have hdisj : Disjoint (S a : Set iota) U := by
        rw [Set.disjoint_iUnion_right]
        intro j
        rw [Set.disjoint_iUnion_right]
        intro hj
        have haj : a ≠ j := by
          intro haj
          apply ha
          simpa [haj] using hj
        exact Finset.disjoint_coe.mpr (hS haj)
      have hindep :
          Indep (⨆ i ∈ (S a : Set iota), m i)
            (⨆ i ∈ U, m i) mu :=
        indep_iSup_of_disjoint hm_le hm_indep hdisj
      have hfa : MeasurableSet[⨆ i ∈ (S a : Set iota), m i] (f a) :=
        hf a (Finset.mem_insert_self a T)
      have hrest : MeasurableSet[⨆ i ∈ U, m i] (⋂ j ∈ T, f j) := by
        apply T.measurableSet_biInter
        intro j hj
        apply (show (⨆ i ∈ (S j : Set iota), m i) <=
            (⨆ i ∈ U, m i) by
          apply iSup_le
          intro i
          apply iSup_le
          intro hi
          exact le_iSup_of_le i (le_iSup_of_le (by
            exact Set.mem_iUnion.2
              ⟨j, Set.mem_iUnion.2 ⟨hj, hi⟩⟩) le_rfl))
        exact hf j (Finset.mem_insert_of_mem hj)
      have hmeasure := (Indep_iff _ _ _).1 hindep
        (f a) (⋂ j ∈ T, f j) hfa hrest
      rw [Finset.set_biInter_insert, Finset.prod_insert ha, hmeasure]
      congr 1
      exact ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Function-valued form: if the coordinates are mutually independent and
the finite index blocks are pairwise disjoint, the corresponding coordinate
tuples are mutually independent. -/
theorem iIndepFun_grouped_finsets
    {mu : Measure Omega}
    {beta : iota -> Type*} [forall i, MeasurableSpace (beta i)]
    (X : forall i, Omega -> beta i)
    (hXmeas : forall i, Measurable (X i))
    (hX : iIndepFun X mu)
    (S : kappa -> Finset iota)
    (hS : Pairwise fun a b => Disjoint (S a) (S b)) :
    iIndepFun (fun a omega (i : S a) => X i omega) mu := by
  rw [iIndepFun_iff_iIndep]
  rw [show (fun a => MeasurableSpace.comap
      (fun omega (i : S a) => X i omega) inferInstance) =
      (fun a => ⨆ i ∈ (S a : Set iota),
        MeasurableSpace.comap (X i) inferInstance) by
    funext a
    rw [MeasurableSpace.comap_process_pi]
    apply le_antisymm
    · apply iSup_le
      intro i
      exact le_iSup_of_le i (le_iSup_of_le i.property le_rfl)
    · apply iSup_le
      intro i
      apply iSup_le
      intro hi
      exact le_iSup_of_le (⟨i, hi⟩ : S a) le_rfl]
  exact iIndep_grouped_iSup
    (fun i => (hXmeas i).comap_le)
    hX.iIndep S hS

end

end LogdetLean.GramHafnian.ThreePaper.GroupedIndependence

#print axioms LogdetLean.GramHafnian.ThreePaper.GroupedIndependence.iIndepFun_grouped_finsets
