import A3.Definitions

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

namespace A3Research

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Nonnegative finite-product Fubini, including nonintegrable densities. -/
theorem wishart_lintegral_fin_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
          f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
          ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _)]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ x, f 0 x ∂μ 0) *
          ∏ i : Fin n, ∫⁻ x : E i.succ, f i.succ x ∂μ i.succ := by
        have hg : Measurable (fun x : (i : Fin n) → E i.succ ↦ ∏ i, f i.succ (x i)) :=
          Finset.univ.measurable_prod (fun i _ ↦ (hf i.succ).comp (measurable_pi_apply i))
        rw [lintegral_prod_mul (f := f 0)
          (g := fun x : (i : Fin n) → E i.succ ↦ ∏ i, f i.succ (x i)) (hf 0).aemeasurable
          hg.aemeasurable, ih (fun i x ↦ f i.succ x) (fun i ↦ hf i.succ)]
      _ = _ := by rw [Fin.prod_univ_succ]

theorem wishart_lintegral_fintype_prod {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact wishart_lintegral_fin_prod _ (fun i ↦ hf (e i))

/-- Density products use the literal coordinate product measure. -/
theorem wishart_pi_withDensity {ι : Type*} [Fintype ι] {E : ι → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} (μ : (i : ι) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (f : (i : ι) → E i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i ↦ (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x ↦ ∏ i, f i (x i)) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.pi (Set.to_countable _) (fun i _ ↦ hs i))]
  change (∫⁻ x : (i : ι) → E i in Set.pi Set.univ s, ∏ i, f i (x i) ∂Measure.pi μ) = _
  rw [Measure.restrict_pi_pi]
  rw [wishart_lintegral_fintype_prod f hf]
  simp_rw [withDensity_apply _ (hs _)]

end A3Research
