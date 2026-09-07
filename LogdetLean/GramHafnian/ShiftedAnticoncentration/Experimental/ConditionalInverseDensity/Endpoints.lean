import LogdetLean.GramHafnian.LocalAnticoncentration.LocalSharpness
import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.SmallBallLocalFlatness.GramHafnianAdapter

/-!
# Conditional inverse-moment density endpoints

This isolated module records the density and local-power consequences of the
last-column Gaussian mixture under their exact analytic hypotheses.  In
particular, no dimension condition such as `4 * r ≤ k` is assumed here.

The hypotheses are instead stated directly:

* the conditional variance is positive almost everywhere;
* its first inverse moment is integrable;
* for the finite local-flatness estimate, its second inverse moment is also
  integrable.

The existing paper-range results imply these hypotheses when `4 * r ≤ k`.
The present module does not claim a sharper dimension threshold for either
inverse moment.
-/

open MeasureTheory ProbabilityTheory Set Metric Filter
open scoped ENNReal Topology

namespace LogdetLean.GramHafnian

noncomputable section

/-! ## Measure and density under explicit analytic hypotheses -/

/-- The exact Gram-hafnian mixture law requires only almost-everywhere
positivity of the conditional variance. -/
theorem map_gramHafnianObservable_eq_withDensity_mixture_of_ae_pos
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A) :
    (circularGaussianColumnMatrixMeasure r k).map
        (gramHafnianObservable r k) =
      (volume : Measure ℂ).withDensity
        (localAnticoncentrationGramHafnianMixtureDensity (k := k) hr) := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  let μ : Measure (Fin k → ℂ) := circularGaussianVector k
  let e := lastColumnProductEquiv r k hr
  have htransport := (measurePreserving_lastColumnProductEquiv r k hr).map_eq
  rw [← htransport]
  rw [Measure.map_map (measurable_gramHafnianObservable r k) e.measurable]
  have hfun : gramHafnianObservable r k ∘ e =
      conditionalCircularLinearForm
        (pastCofactorCombination (k := k) hr) := by
    funext p
    exact gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm hr p
  rw [hfun]
  ext s hs
  have hconditional :
      Measurable
        (conditionalCircularLinearForm
          (pastCofactorCombination (k := k) hr)) :=
    measurable_conditionalCircularLinearForm
      (measurable_pastCofactorCombination (k := k) hr)
  rw [Measure.map_apply hconditional hs,
    Measure.prod_apply (hs.preimage hconditional), withDensity_apply _ hs]
  have hVpos' : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using hVpos
  have hjoint : Measurable (fun p :
      (OddCofactorIndex r hr → (Fin k → ℂ)) × ℂ ↦
      localAnticoncentrationScaledCircularGaussianDensity
        (pastCofactorV hr p.1) p.2) :=
    measurable_localAnticoncentrationScaledCircularGaussianDensity_uncurry
      (measurable_pastCofactorV hr)
  calc
    (∫⁻ A, μ (Prod.mk A ⁻¹'
        (conditionalCircularLinearForm
          (pastCofactorCombination (k := k) hr) ⁻¹' s)) ∂ν) =
        ∫⁻ A, ∫⁻ w in s,
          localAnticoncentrationScaledCircularGaussianDensity
            (pastCofactorV hr A) w ∂volume ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hVpos'] with A hA
      have hsection :
          Prod.mk A ⁻¹'
              (conditionalCircularLinearForm
                (pastCofactorCombination (k := k) hr) ⁻¹' s) =
            (fun x ↦ gramHafnianObservable r k
              (lastColumnProductEquiv r k hr (A, x))) ⁻¹' s := by
        ext x
        change (conditionalCircularLinearForm
            (pastCofactorCombination (k := k) hr) (A, x) ∈ s) ↔
          gramHafnianObservable r k
            (lastColumnProductEquiv r k hr (A, x)) ∈ s
        rw [gramHafnian_lastColumnProductEquiv_eq_conditionalLinearForm]
      rw [hsection]
      let F : (Fin k → ℂ) → ℂ := fun x ↦
        gramHafnianObservable r k
          (lastColumnProductEquiv r k hr (A, x))
      have hF : Measurable F :=
        (measurable_gramHafnianObservable r k).comp
          ((lastColumnProductEquiv r k hr).measurable.comp
            (measurable_const.prodMk measurable_id))
      calc
        μ (F ⁻¹' s) = (μ.map F) s :=
          (Measure.map_apply hF hs).symm
        _ = ((volume : Measure ℂ).withDensity
              (localAnticoncentrationScaledCircularGaussianDensity
                (pastCofactorV hr A))) s := by
          simpa [μ, F] using congrArg (fun m : Measure ℂ ↦ m s)
            (gramHafnian_lastColumn_conditionalDensity hr A hA)
        _ = ∫⁻ w in s,
              localAnticoncentrationScaledCircularGaussianDensity
                (pastCofactorV hr A) w ∂volume := by
          rw [withDensity_apply _ hs]
    _ = ∫⁻ w in s, ∫⁻ A,
          localAnticoncentrationScaledCircularGaussianDensity
            (pastCofactorV hr A) w ∂ν ∂volume := by
      rw [lintegral_lintegral_swap hjoint.aemeasurable]
    _ = ∫⁻ w in s,
          localAnticoncentrationGramHafnianMixtureDensity (k := k) hr w ∂volume := by
      rfl

/-- Integrability of the real density integrand follows from exactly the
first inverse-moment hypothesis. -/
theorem integrable_localAnticoncentrationGramHafnianDensityIntegrand_of_inverse
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A)
    (hInv : Integrable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k))
    (w : ℂ) :
    Integrable (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
      localAnticoncentrationGramHafnianDensityIntegrand hr A w)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k) := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hVpos' : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using hVpos
  have hdom : Integrable (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
      Real.pi⁻¹ * (pastCofactorV hr A)⁻¹) ν := by
    simpa [ν] using hInv.const_mul Real.pi⁻¹
  apply hdom.mono
  · exact ((measurable_localAnticoncentrationGramHafnianDensityIntegrand_uncurry hr).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [hVpos'] with A hA
    have hcoef : 0 < Real.pi⁻¹ * (pastCofactorV hr A)⁻¹ :=
      mul_pos (inv_pos.mpr Real.pi_pos) (inv_pos.mpr hA)
    calc
      ‖localAnticoncentrationGramHafnianDensityIntegrand hr A w‖ =
          localAnticoncentrationGramHafnianDensityIntegrand hr A w :=
        Real.norm_of_nonneg
          (localAnticoncentrationGramHafnianDensityIntegrand_nonneg hr A w)
      _ ≤ Real.pi⁻¹ * (pastCofactorV hr A)⁻¹ := by
        unfold localAnticoncentrationGramHafnianDensityIntegrand
        apply mul_le_of_le_one_right hcoef.le
        exact Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (sq_nonneg ‖w‖)) hA.le)
      _ = ‖Real.pi⁻¹ * (pastCofactorV hr A)⁻¹‖ :=
        (Real.norm_of_nonneg hcoef.le).symm

/-- Under positivity and the first inverse moment, the `ENNReal` mixture
density is the `ofReal` lift of the paper's real expectation. -/
theorem localAnticoncentrationGramHafnianMixtureDensity_eq_ofReal_of_inverse
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A)
    (hInv : Integrable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k))
    (w : ℂ) :
    localAnticoncentrationGramHafnianMixtureDensity (k := k) hr w =
      ENNReal.ofReal (localAnticoncentrationGramHafnianDensity (k := k) hr w) := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hVpos' : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using hVpos
  have hint := integrable_localAnticoncentrationGramHafnianDensityIntegrand_of_inverse
    hr hVpos hInv w
  have hnonneg : ∀ᵐ A ∂ν,
      0 ≤ localAnticoncentrationGramHafnianDensityIntegrand hr A w :=
    ae_of_all _ fun A ↦ localAnticoncentrationGramHafnianDensityIntegrand_nonneg hr A w
  rw [localAnticoncentrationGramHafnianMixtureDensity, localAnticoncentrationGramHafnianDensity,
    ofReal_integral_eq_lintegral_ofReal (by simpa [ν] using hint) hnonneg]
  apply lintegral_congr_ae
  filter_upwards [hVpos'] with A hA
  rw [localAnticoncentrationScaledCircularGaussianDensity_eq hA]
  rfl

/-- Equation (13) under the exact analytic hypotheses, with no dimension
surrogate. -/
theorem map_gramHafnianObservable_eq_withDensity_real_of_inverse
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A)
    (hInv : Integrable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)) :
    (circularGaussianColumnMatrixMeasure r k).map
        (gramHafnianObservable r k) =
      (volume : Measure ℂ).withDensity
        (fun w ↦ ENNReal.ofReal
          (localAnticoncentrationGramHafnianDensity (k := k) hr w)) := by
  rw [map_gramHafnianObservable_eq_withDensity_mixture_of_ae_pos hr hVpos]
  congr 1
  funext w
  exact localAnticoncentrationGramHafnianMixtureDensity_eq_ofReal_of_inverse
    hr hVpos hInv w

/-- Continuity of the mixture density follows from the first inverse moment. -/
theorem continuous_localAnticoncentrationGramHafnianDensity_of_inverse
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A)
    (hInv : Integrable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)) :
    Continuous (localAnticoncentrationGramHafnianDensity (k := k) hr) := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hVpos' : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using hVpos
  have hdom : Integrable (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
      Real.pi⁻¹ * (pastCofactorV hr A)⁻¹) ν := by
    simpa [ν] using hInv.const_mul Real.pi⁻¹
  rw [continuous_iff_continuousAt]
  intro w
  unfold localAnticoncentrationGramHafnianDensity
  apply tendsto_integral_filter_of_dominated_convergence
    (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
      Real.pi⁻¹ * (pastCofactorV hr A)⁻¹)
  · filter_upwards [] with u
    exact ((measurable_localAnticoncentrationGramHafnianDensityIntegrand_uncurry hr).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [] with u
    filter_upwards [hVpos'] with A hA
    have hcoef : 0 < Real.pi⁻¹ * (pastCofactorV hr A)⁻¹ :=
      mul_pos (inv_pos.mpr Real.pi_pos) (inv_pos.mpr hA)
    calc
      ‖localAnticoncentrationGramHafnianDensityIntegrand hr A u‖ =
          localAnticoncentrationGramHafnianDensityIntegrand hr A u :=
        Real.norm_of_nonneg
          (localAnticoncentrationGramHafnianDensityIntegrand_nonneg hr A u)
      _ ≤ Real.pi⁻¹ * (pastCofactorV hr A)⁻¹ := by
        unfold localAnticoncentrationGramHafnianDensityIntegrand
        apply mul_le_of_le_one_right hcoef.le
        exact Real.exp_le_one_iff.mpr
          (div_nonpos_of_nonpos_of_nonneg
            (neg_nonpos.mpr (sq_nonneg ‖u‖)) hA.le)
  · exact hdom
  · filter_upwards [hVpos'] with A hA
    have hcont : Continuous (fun u : ℂ ↦
        localAnticoncentrationGramHafnianDensityIntegrand hr A u) := by
      unfold localAnticoncentrationGramHafnianDensityIntegrand
      fun_prop
    exact hcont.continuousAt

/-- Strict positivity of the density under the exact analytic hypotheses. -/
theorem localAnticoncentrationGramHafnianDensity_pos_of_inverse
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A)
    (hInv : Integrable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k))
    (w : ℂ) :
    0 < localAnticoncentrationGramHafnianDensity (k := k) hr w := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  let g : (OddCofactorIndex r hr → (Fin k → ℂ)) → ℝ :=
    fun A ↦ localAnticoncentrationGramHafnianDensityIntegrand hr A w
  have hint : Integrable g ν := by
    simpa [ν, g] using
      integrable_localAnticoncentrationGramHafnianDensityIntegrand_of_inverse
        hr hVpos hInv w
  have hnonneg : 0 ≤ᵐ[ν] g :=
    ae_of_all _ fun A ↦
      localAnticoncentrationGramHafnianDensityIntegrand_nonneg hr A w
  rw [localAnticoncentrationGramHafnianDensity,
    integral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hVpos' : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using hVpos
  have hsupport : ∀ᵐ A ∂ν, A ∈ Function.support g := by
    filter_upwards [hVpos'] with A hA
    change g A ≠ 0
    apply ne_of_gt
    dsimp [g, localAnticoncentrationGramHafnianDensityIntegrand]
    positivity
  have hfull : ν (Function.support g) = 1 := by
    apply le_antisymm
    · simpa using
        (measure_mono (μ := ν) (Set.subset_univ (Function.support g)))
    have hle : ν Set.univ ≤ ν (Function.support g) := by
      apply measure_mono_ae
      filter_upwards [hsupport] with A hA
      intro _hmem
      exact hA
    simpa using hle
  rw [show
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)
          (Function.support g) = ν (Function.support g) by rfl,
    hfull]
  norm_num

/-- Radial monotonicity under the exact analytic hypotheses. -/
theorem localAnticoncentrationGramHafnianDensity_antitone_norm_of_inverse
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A)
    (hInv : Integrable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k))
    {z w : ℂ} (hzw : ‖z‖ ≤ ‖w‖) :
    localAnticoncentrationGramHafnianDensity (k := k) hr w ≤
      localAnticoncentrationGramHafnianDensity (k := k) hr z := by
  let ν : Measure (OddCofactorIndex r hr → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k
  have hVpos' : ∀ᵐ A ∂ν, 0 < pastCofactorV hr A := by
    simpa [ν] using hVpos
  unfold localAnticoncentrationGramHafnianDensity
  apply integral_mono_ae
    (by
      simpa [ν] using
        (integrable_localAnticoncentrationGramHafnianDensityIntegrand_of_inverse
          hr hVpos hInv w))
    (by
      simpa [ν] using
        (integrable_localAnticoncentrationGramHafnianDensityIntegrand_of_inverse
          hr hVpos hInv z))
  filter_upwards [hVpos'] with A hA
  unfold localAnticoncentrationGramHafnianDensityIntegrand
  apply mul_le_mul_of_nonneg_left
  · apply Real.exp_le_exp.mpr
    have hsq : ‖z‖ ^ 2 ≤ ‖w‖ ^ 2 := by
      nlinarith [norm_nonneg z, norm_nonneg w]
    simpa only [neg_div] using
      neg_le_neg (div_le_div_of_nonneg_right hsq hA.le)
  · exact mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
      (inv_nonneg.mpr hA.le)

/-- The real density is globally integrable because it represents a
probability law. -/
theorem integrable_localAnticoncentrationGramHafnianDensity_volume_of_inverse
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A)
    (hInv : Integrable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)) :
    Integrable (localAnticoncentrationGramHafnianDensity (k := k) hr)
      (volume : Measure ℂ) := by
  let f : ℂ → ℝ := localAnticoncentrationGramHafnianDensity (k := k) hr
  have hfmeas : AEStronglyMeasurable f (volume : Measure ℂ) :=
    (continuous_localAnticoncentrationGramHafnianDensity_of_inverse hr hVpos hInv).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℂ)] f :=
    ae_of_all _ fun w ↦ localAnticoncentrationGramHafnianDensity_nonneg hr w
  apply (lintegral_ofReal_ne_top_iff_integrable hfmeas hnonneg).mp
  have hlaw := map_gramHafnianObservable_eq_withDensity_real_of_inverse
    hr hVpos hInv
  have hmass :
      ((volume : Measure ℂ).withDensity
        (fun w ↦ ENNReal.ofReal (f w))) Set.univ = 1 := by
    rw [← hlaw]
    rw [Measure.map_apply (measurable_gramHafnianObservable r k)
      MeasurableSet.univ]
    simp
  rw [withDensity_apply _ MeasurableSet.univ] at hmass
  rw [Measure.restrict_univ] at hmass
  rw [hmass]
  exact ENNReal.one_ne_top

/-! ## Exact local power under the same hypotheses -/

/-- Unnormalized shrinking-disk local power under the exact first inverse
moment condition. -/
theorem gramHafnian_raw_shrinkingDisk_limit_of_inverse
    {r k : ℕ} (hr : 1 ≤ r)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A)
    (hInv : Integrable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k))
    (z : ℂ) :
    Tendsto
      (fun rho : ℝ ↦
        (circularGaussianColumnMatrixMeasure r k).real
            {X | ‖gramHafnianObservable r k X - z‖ ≤ rho} / rho ^ 2)
      (𝓝[>] 0)
      (𝓝 (Real.pi * localAnticoncentrationGramHafnianDensity (k := k) hr z)) := by
  let f : ℂ → ℝ := localAnticoncentrationGramHafnianDensity (k := k) hr
  have hbase := tendsto_withDensity_complex_closedBall_div_sq f
    (continuous_localAnticoncentrationGramHafnianDensity_of_inverse hr hVpos hInv)
    (integrable_localAnticoncentrationGramHafnianDensity_volume_of_inverse hr hVpos hInv)
    (fun w ↦ localAnticoncentrationGramHafnianDensity_nonneg hr w) z
  rw [← map_gramHafnianObservable_eq_withDensity_real_of_inverse
    hr hVpos hInv] at hbase
  apply hbase.congr'
  filter_upwards [] with rho
  rw [MeasureTheory.map_measureReal_apply
    (measurable_gramHafnianObservable r k) measurableSet_closedBall]
  congr 2
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_closedBall,
    dist_eq_norm]

/-- Normalized shrinking-disk local power under positivity and the exact
first inverse-moment condition.  Positivity of `k` is used only to ensure
that the explicit normalization `sigma_{k,r}` is nonzero. -/
theorem gramHafnian_normalized_shrinkingDisk_limit_density_of_inverse
    {r k : ℕ} (hr : 1 ≤ r) (hkpos : 0 < k)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A)
    (hInv : Integrable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k))
    (z : ℂ) :
    Tendsto
      (fun eps : ℝ ↦
        (circularGaussianColumnMatrixMeasure r k).real
            {X | ‖gramHafnianObservable r k X - z‖ ≤
              eps * gramHafnianSigma k r} / eps ^ 2)
      (𝓝[>] 0)
      (𝓝 (gramHafnianSigma k r ^ 2 *
        (Real.pi * localAnticoncentrationGramHafnianDensity (k := k) hr z))) := by
  have hsigma : 0 < gramHafnianSigma k r :=
    gramHafnianSigma_pos k r hkpos
  have hscale : Tendsto
      (fun eps : ℝ ↦ eps * gramHafnianSigma k r)
      (𝓝[>] 0) (𝓝[>] 0) := by
    have hid : Tendsto (fun eps : ℝ ↦ eps) (𝓝[>] 0) (𝓝[>] 0) :=
      tendsto_id
    simpa using Filter.TendstoNhdsWithinIoi.mul_const hsigma hid
  have hraw :=
    (gramHafnian_raw_shrinkingDisk_limit_of_inverse hr hVpos hInv z).comp
      hscale
  have hmul := hraw.mul_const (gramHafnianSigma k r ^ 2)
  have hmul' : Tendsto
      (fun eps : ℝ ↦
        ((circularGaussianColumnMatrixMeasure r k).real
            {X | ‖gramHafnianObservable r k X - z‖ ≤
              eps * gramHafnianSigma k r} /
            (eps * gramHafnianSigma k r) ^ 2) *
          gramHafnianSigma k r ^ 2)
      (𝓝[>] 0)
      (𝓝 (gramHafnianSigma k r ^ 2 *
        (Real.pi * localAnticoncentrationGramHafnianDensity (k := k) hr z))) := by
    simpa [mul_comm] using hmul
  apply hmul'.congr'
  filter_upwards [self_mem_nhdsWithin] with eps heps
  have hepspos : 0 < eps := heps
  field_simp [hepspos.ne', hsigma.ne']

/-- The normalized shrinking-disk statement in the expectation notation of
the paper. -/
theorem gramHafnian_normalized_shrinkingDisk_limit_of_inverse
    {r k : ℕ} (hr : 1 ≤ r) (hkpos : 0 < k)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A)
    (hInv : Integrable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k))
    (z : ℂ) :
    Tendsto
      (fun eps : ℝ ↦
        (circularGaussianColumnMatrixMeasure r k).real
            {X | ‖gramHafnianObservable r k X - z‖ ≤
              eps * gramHafnianSigma k r} / eps ^ 2)
      (𝓝[>] 0)
      (𝓝 (gramHafnianSigma k r ^ 2 *
        localAnticoncentrationLocalSharpnessCoefficient (k := k) hr z)) := by
  simpa [pi_mul_localAnticoncentrationGramHafnianDensity_eq_localSharpnessCoefficient]
    using gramHafnian_normalized_shrinkingDisk_limit_density_of_inverse
      hr hkpos hVpos hInv z

/-- The local-power coefficient remains strictly positive under the exact
analytic assumptions. -/
theorem gramHafnian_normalized_shrinkingDisk_limit_coefficient_pos_of_inverse
    {r k : ℕ} (hr : 1 ≤ r) (hkpos : 0 < k)
    (hVpos :
      ∀ᵐ A : OddCofactorIndex r hr → (Fin k → ℂ)
        ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k),
        0 < pastCofactorV hr A)
    (hInv : Integrable
      (fun A : OddCofactorIndex r hr → (Fin k → ℂ) ↦
        (pastCofactorV hr A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k))
    (z : ℂ) :
    0 < gramHafnianSigma k r ^ 2 *
      localAnticoncentrationLocalSharpnessCoefficient (k := k) hr z := by
  have hsigma : 0 < gramHafnianSigma k r :=
    gramHafnianSigma_pos k r hkpos
  have hfpos := localAnticoncentrationGramHafnianDensity_pos_of_inverse
    hr hVpos hInv z
  rw [← pi_mul_localAnticoncentrationGramHafnianDensity_eq_localSharpnessCoefficient]
  exact mul_pos (sq_pos_of_pos hsigma) (mul_pos Real.pi_pos hfpos)

end

end LogdetLean.GramHafnian
