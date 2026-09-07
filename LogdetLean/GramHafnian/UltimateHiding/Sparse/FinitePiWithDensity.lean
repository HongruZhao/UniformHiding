import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Density

/-!
# Densities of finite product measures

Mathlib supplies the binary theorem `prod_withDensity`, but this checkout has
no corresponding theorem for `Measure.pi`.  The induction below provides the
finite dependent-product form needed for the entrywise Gaussian density in
H19.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- Transport a density through a measurable equivalence.  Keeping this
elementary lemma beside the finite-product construction avoids importing the
anticoncentration paper's mixture-density development. -/
theorem map_measurableEquiv_withDensity_piFin
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ENNReal)
    (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs]
  rw [← lintegral_indicator hs]
  rw [lintegral_map]
  · rw [← lintegral_indicator (hs.preimage e.measurable)]
    congr 1
    funext x
    by_cases hx : e x ∈ s
    · simp [Set.indicator, hx]
    · simp [Set.indicator, hx]
  · exact (hf.comp e.symm.measurable).indicator hs
  · exact e.measurable

/-- A finite product of measures with densities has density equal to the
product of the coordinate densities.  The second sigma-finiteness assumption
is automatic for the finite-valued (`ENNReal.ofReal`) densities used in H19. -/
theorem piFin_withDensity (n : Nat) :
    ∀ {E : Type*} [MeasurableSpace E]
      (mu : Fin n -> Measure E) [∀ i, SigmaFinite (mu i)]
      (f : Fin n -> E -> ENNReal)
      [∀ i, SigmaFinite ((mu i).withDensity (f i))],
      (∀ i, Measurable (f i)) ->
      Measure.pi (fun i => (mu i).withDensity (f i)) =
        (Measure.pi mu).withDensity (fun x => ∏ i, f i (x i)) := by
  induction n with
  | zero =>
      intro E mE mu hmu f hfdens hf
      have hfamilies : (fun i : Fin 0 => (mu i).withDensity (f i)) = mu := by
        funext i
        exact Fin.elim0 i
      rw [hfamilies]
      simp
  | succ n ih =>
      intro E mE mu hmu f hfdens hf
      let e := MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => E) (0 : Fin (n + 1))
      apply e.map_measurableEquiv_injective
      have hleft :
          Measure.map e
              (Measure.pi (fun i => (mu i).withDensity (f i))) =
            ((mu 0).withDensity (f 0)).prod
              (Measure.pi fun j : Fin n =>
                (mu (Fin.succ j)).withDensity (f (Fin.succ j))) :=
        (measurePreserving_piFinSuccAbove
          (fun i => (mu i).withDensity (f i)) 0).map_eq
      have hbase :
          Measure.map e (Measure.pi mu) =
            (mu 0).prod (Measure.pi fun j : Fin n => mu (Fin.succ j)) :=
        (measurePreserving_piFinSuccAbove mu 0).map_eq
      have htail := ih
        (fun j : Fin n => mu (Fin.succ j))
        (fun j : Fin n => f (Fin.succ j))
        (fun j => hf (Fin.succ j))
      have hfull : Measurable
          (fun x : Fin (n + 1) -> E => ∏ i, f i (x i)) := by
        fun_prop
      rw [hleft, htail, prod_withDensity (hf 0)
        (by
          fun_prop : Measurable (fun x : Fin n -> E =>
            ∏ j, f (Fin.succ j) (x j)))]
      rw [map_measurableEquiv_withDensity_piFin
        e (Measure.pi mu) (fun x => ∏ i, f i (x i)) hfull, hbase]
      congr 1
      funext p
      dsimp [e]
      rw [Fin.prod_univ_succ]
      simp

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
