import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Reusable twice-dominated differentiation

This file contains no COE, determinant, or probability input.  It packages
the exact analytic argument needed after a moving-support law has been
rewritten as an integral of a fixed-event indicator against an ambient
density.  The same almost-everywhere majorant works at every parameter value.
-/

open MeasureTheory Filter
open scoped ContDiff Topology

namespace LogdetLean.GramHafnian.UltimateHiding.H3H4Central

noncomputable section

/-- Dominated continuity for a real-valued parameterized integral, with one
integrable majorant that is valid at every parameter value. -/
theorem continuous_integral_of_common_integrable_bound
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {F : ℝ → Omega → ℝ} {bound : Omega → ℝ}
    (hF_meas : ∀ t, AEStronglyMeasurable (F t) mu)
    (h_bound : ∀ᵐ omega ∂mu, ∀ t, ‖F t omega‖ ≤ bound omega)
    (hbound_integrable : Integrable bound mu)
    (h_cont : ∀ᵐ omega ∂mu, Continuous fun t ↦ F t omega) :
    Continuous fun t ↦ ∫ omega, F t omega ∂mu := by
  rw [continuous_iff_continuousAt]
  intro t
  exact tendsto_integral_filter_of_dominated_convergence bound
    (Filter.Eventually.of_forall hF_meas)
    (Filter.Eventually.of_forall fun s ↦
      h_bound.mono fun omega homega ↦ homega s)
    hbound_integrable
    (h_cont.mono fun _ h ↦ h.continuousAt)

/-- Two derivatives may be passed through an integral when the density, its
first derivative, and its second derivative have common integrable
majorants.  The conclusion includes both `C²` regularity and the literal
first/second `iteratedDeriv` formulas at every parameter value.

This is deliberately event-agnostic: an event indicator can be included in
`F`, `F₁`, and `F₂`, while the majorants can be taken from the unrestricted
ambient density jets. -/
theorem contDiff_two_integral_of_common_integrable_bounds
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {F F₁ F₂ : ℝ → Omega → ℝ}
    {bound₀ bound₁ bound₂ : Omega → ℝ}
    (hF_meas : ∀ t, AEStronglyMeasurable (F t) mu)
    (hF₁_meas : ∀ t, AEStronglyMeasurable (F₁ t) mu)
    (hF₂_meas : ∀ t, AEStronglyMeasurable (F₂ t) mu)
    (hbound₀_integrable : Integrable bound₀ mu)
    (hbound₁_integrable : Integrable bound₁ mu)
    (hbound₂_integrable : Integrable bound₂ mu)
    (h_bound₀ : ∀ᵐ omega ∂mu, ∀ t, ‖F t omega‖ ≤ bound₀ omega)
    (h_bound₁ : ∀ᵐ omega ∂mu, ∀ t, ‖F₁ t omega‖ ≤ bound₁ omega)
    (h_bound₂ : ∀ᵐ omega ∂mu, ∀ t, ‖F₂ t omega‖ ≤ bound₂ omega)
    (h_deriv₁ : ∀ᵐ omega ∂mu, ∀ t,
      HasDerivAt (fun s ↦ F s omega) (F₁ t omega) t)
    (h_deriv₂ : ∀ᵐ omega ∂mu, ∀ t,
      HasDerivAt (fun s ↦ F₁ s omega) (F₂ t omega) t)
    (h_cont₂ : ∀ᵐ omega ∂mu, Continuous fun t ↦ F₂ t omega) :
    let I : ℝ → ℝ := fun t ↦ ∫ omega, F t omega ∂mu
    let I₁ : ℝ → ℝ := fun t ↦ ∫ omega, F₁ t omega ∂mu
    let I₂ : ℝ → ℝ := fun t ↦ ∫ omega, F₂ t omega ∂mu
    ContDiff ℝ 2 I ∧
      ∀ t, iteratedDeriv 1 I t = I₁ t ∧ iteratedDeriv 2 I t = I₂ t := by
  dsimp only
  let I : ℝ → ℝ := fun t ↦ ∫ omega, F t omega ∂mu
  let I₁ : ℝ → ℝ := fun t ↦ ∫ omega, F₁ t omega ∂mu
  let I₂ : ℝ → ℝ := fun t ↦ ∫ omega, F₂ t omega ∂mu
  have hF_integrable (t : ℝ) : Integrable (F t) mu :=
    hbound₀_integrable.mono' (hF_meas t)
      (h_bound₀.mono fun omega homega ↦ homega t)
  have hF₁_integrable (t : ℝ) : Integrable (F₁ t) mu :=
    hbound₁_integrable.mono' (hF₁_meas t)
      (h_bound₁.mono fun omega homega ↦ homega t)
  have hI_hasDerivAt (t : ℝ) : HasDerivAt I (I₁ t) t := by
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := mu) (F := F) (F' := F₁) (bound := bound₁)
      (x₀ := t) (s := Set.univ) Filter.univ_mem
      (Filter.Eventually.of_forall hF_meas) (hF_integrable t)
      (hF₁_meas t)
      (h_bound₁.mono fun omega homega s _ ↦ homega s)
      hbound₁_integrable
      (h_deriv₁.mono fun omega homega s _ ↦ homega s)
    simpa only [I, I₁] using h.2
  have hI₁_hasDerivAt (t : ℝ) : HasDerivAt I₁ (I₂ t) t := by
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := mu) (F := F₁) (F' := F₂) (bound := bound₂)
      (x₀ := t) (s := Set.univ) Filter.univ_mem
      (Filter.Eventually.of_forall hF₁_meas) (hF₁_integrable t)
      (hF₂_meas t)
      (h_bound₂.mono fun omega homega s _ ↦ homega s)
      hbound₂_integrable
      (h_deriv₂.mono fun omega homega s _ ↦ homega s)
    simpa only [I₁, I₂] using h.2
  have hI₂_continuous : Continuous I₂ := by
    simpa only [I₂] using
      (continuous_integral_of_common_integrable_bound hF₂_meas h_bound₂
        hbound₂_integrable h_cont₂)
  have hderivI : deriv I = I₁ := by
    funext t
    exact (hI_hasDerivAt t).deriv
  have hderivI₁ : deriv I₁ = I₂ := by
    funext t
    exact (hI₁_hasDerivAt t).deriv
  have hI₁_contDiff : ContDiff ℝ 1 I₁ := by
    apply contDiff_one_iff_deriv.2
    refine ⟨fun t ↦ (hI₁_hasDerivAt t).differentiableAt, ?_⟩
    rw [hderivI₁]
    exact hI₂_continuous
  have hI_contDiff : ContDiff ℝ 2 I := by
    rw [show (2 : ℕ∞ω) = 1 + 1 by norm_num,
      contDiff_succ_iff_deriv]
    refine ⟨fun t ↦ (hI_hasDerivAt t).differentiableAt, ?_, ?_⟩
    · norm_num
    · rw [hderivI]
      exact hI₁_contDiff
  refine ⟨hI_contDiff, fun t ↦ ⟨?_, ?_⟩⟩
  · rw [iteratedDeriv_one, hderivI]
  · rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one, hderivI, hderivI₁]

/-- Local form of twice-dominated differentiation on an open parameter set.
The first and second `iteratedDeriv` formulas are included at every point of
that set.  This is the form needed for transported compactly supported
densities, whose common majorants are naturally local in the parameter. -/
theorem contDiffOn_two_integral_of_dominated_with_derivatives
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {s : Set ℝ} (hs : IsOpen s)
    {F F₁ F₂ : ℝ → Omega → ℝ} {g₁ g₂ : Omega → ℝ}
    (hF_meas : ∀ t ∈ s, AEStronglyMeasurable (F t) mu)
    (hF_int : ∀ t ∈ s, Integrable (F t) mu)
    (hF₁_meas : ∀ t ∈ s, AEStronglyMeasurable (F₁ t) mu)
    (hF₂_meas : ∀ t ∈ s, AEStronglyMeasurable (F₂ t) mu)
    (hg₁ : Integrable g₁ mu) (hg₂ : Integrable g₂ mu)
    (hbound₁ : ∀ᵐ omega ∂mu, ∀ t ∈ s, ‖F₁ t omega‖ ≤ g₁ omega)
    (hbound₂ : ∀ᵐ omega ∂mu, ∀ t ∈ s, ‖F₂ t omega‖ ≤ g₂ omega)
    (hderiv₁ : ∀ᵐ omega ∂mu, ∀ t ∈ s,
      HasDerivAt (fun u ↦ F u omega) (F₁ t omega) t)
    (hderiv₂ : ∀ᵐ omega ∂mu, ∀ t ∈ s,
      HasDerivAt (fun u ↦ F₁ u omega) (F₂ t omega) t)
    (hcont₂ : ∀ᵐ omega ∂mu, ContinuousOn (fun t ↦ F₂ t omega) s) :
    let I : ℝ → ℝ := fun t ↦ ∫ omega, F t omega ∂mu
    let I₁ : ℝ → ℝ := fun t ↦ ∫ omega, F₁ t omega ∂mu
    let I₂ : ℝ → ℝ := fun t ↦ ∫ omega, F₂ t omega ∂mu
    ContDiffOn ℝ 2 I s ∧
      ∀ t ∈ s, iteratedDeriv 1 I t = I₁ t ∧
        iteratedDeriv 2 I t = I₂ t := by
  dsimp only
  let I : ℝ → ℝ := fun t ↦ ∫ omega, F t omega ∂mu
  let I₁ : ℝ → ℝ := fun t ↦ ∫ omega, F₁ t omega ∂mu
  let I₂ : ℝ → ℝ := fun t ↦ ∫ omega, F₂ t omega ∂mu
  have hd₀ : ∀ t ∈ s, HasDerivAt I (I₁ t) t := by
    intro t ht
    have hmeas : ∀ᶠ u in 𝓝 t, AEStronglyMeasurable (F u) mu := by
      filter_upwards [hs.mem_nhds ht] with u hu
      exact hF_meas u hu
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (hs.mem_nhds ht) hmeas (hF_int t ht) (hF₁_meas t ht)
      hbound₁ hg₁ hderiv₁).2
  have hd₁ : ∀ t ∈ s, HasDerivAt I₁ (I₂ t) t := by
    intro t ht
    have hmeas : ∀ᶠ u in 𝓝 t, AEStronglyMeasurable (F₁ u) mu := by
      filter_upwards [hs.mem_nhds ht] with u hu
      exact hF₁_meas u hu
    have hF₁_int : Integrable (F₁ t) mu :=
      (hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (hs.mem_nhds ht)
        (by
          filter_upwards [hs.mem_nhds ht] with u hu
          exact hF_meas u hu)
        (hF_int t ht) (hF₁_meas t ht) hbound₁ hg₁ hderiv₁).1
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (hs.mem_nhds ht) hmeas hF₁_int (hF₂_meas t ht)
      hbound₂ hg₂ hderiv₂).2
  have hI₂_cont : ContinuousOn I₂ s := by
    exact continuousOn_of_dominated
      (fun t ht ↦ hF₂_meas t ht)
      (fun t ht ↦ hbound₂.mono fun omega homega ↦ homega t ht)
      hg₂ hcont₂
  have hdiff₀ : DifferentiableOn ℝ I s := fun t ht ↦
    (hd₀ t ht).differentiableAt.differentiableWithinAt
  have hdiff₁ : DifferentiableOn ℝ I₁ s := fun t ht ↦
    (hd₁ t ht).differentiableAt.differentiableWithinAt
  have hderivI : ∀ t ∈ s, deriv I t = I₁ t := fun t ht ↦ (hd₀ t ht).deriv
  have hderivI₁ : ∀ t ∈ s, deriv I₁ t = I₂ t := fun t ht ↦ (hd₁ t ht).deriv
  have hcontDerivI₁ : ContinuousOn (deriv I₁) s := hI₂_cont.congr hderivI₁
  have hC₁I₁ : ContDiffOn ℝ 1 I₁ s := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) hs).2
    refine ⟨hdiff₁, ?_, ?_⟩
    · simp
    · simpa only [contDiffOn_zero] using hcontDerivI₁
  have hC₂I : ContDiffOn ℝ 2 I s := by
    apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) hs).2
    refine ⟨hdiff₀, ?_, ?_⟩
    · simp
    · exact hC₁I₁.congr hderivI
  refine ⟨hC₂I, fun t ht ↦ ⟨?_, ?_⟩⟩
  · rw [iteratedDeriv_one, (hd₀ t ht).deriv]
  · rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one]
    have hlocal : deriv I =ᶠ[𝓝 t] I₁ := by
      filter_upwards [hs.mem_nhds ht] with u hu
      exact (hd₀ u hu).deriv
    rw [hlocal.deriv_eq, (hd₁ t ht).deriv]

end

end LogdetLean.GramHafnian.UltimateHiding.H3H4Central
