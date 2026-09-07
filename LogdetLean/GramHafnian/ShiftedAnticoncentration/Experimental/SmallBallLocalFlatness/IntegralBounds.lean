import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.SmallBallLocalFlatness.ExponentialMixture

/-!
# Integral local-flatness bounds for exponential mixtures

This module integrates the pointwise estimates in `ExponentialMixture`.  The
only analytic hypotheses are positivity of the mixing variable and finiteness
of its first two inverse moments.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

def exponentialMixtureLambda (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω)⁻¹ ∂μ

def exponentialMixtureSecondInverseMoment
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω)⁻¹ ^ 2 ∂μ

def exponentialMixtureDensity
    (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, exponentialMixtureDensityKernel (X ω) t ∂μ

def exponentialMixtureCDF
    (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  ∫ ω, exponentialMixtureCDFKernel (X ω) t ∂μ

theorem measurable_exponentialMixtureDensityKernel_comp
    {X : Ω → ℝ} (hXmeas : Measurable X) (t : ℝ) :
    Measurable (fun ω ↦ exponentialMixtureDensityKernel (X ω) t) := by
  unfold exponentialMixtureDensityKernel
  fun_prop

theorem measurable_exponentialMixtureCDFKernel_comp
    {X : Ω → ℝ} (hXmeas : Measurable X) (t : ℝ) :
    Measurable (fun ω ↦ exponentialMixtureCDFKernel (X ω) t) := by
  unfold exponentialMixtureCDFKernel
  fun_prop

/-- The density kernel is integrable whenever the first inverse moment is. -/
theorem integrable_exponentialMixtureDensityKernel
    {μ : Measure Ω} {X : Ω → ℝ} (hXmeas : Measurable X)
    (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    (hInv : Integrable (fun ω ↦ (X ω)⁻¹) μ) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω ↦ exponentialMixtureDensityKernel (X ω) t) μ := by
  apply hInv.mono'
  · exact (measurable_exponentialMixtureDensityKernel_comp hXmeas t).aestronglyMeasurable
  · filter_upwards [hXpos] with ω hω
    have hnonneg : 0 ≤ exponentialMixtureDensityKernel (X ω) t := by
      unfold exponentialMixtureDensityKernel
      positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using
      exponentialMixtureDensityKernel_le_inv hω ht

/-- The CDF kernel is integrable under any finite measure. -/
theorem integrable_exponentialMixtureCDFKernel
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hXmeas : Measurable X) (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun ω ↦ exponentialMixtureCDFKernel (X ω) t) μ := by
  apply (integrable_const (μ := μ) (c := (1 : ℝ))).mono'
  · exact (measurable_exponentialMixtureCDFKernel_comp hXmeas t).aestronglyMeasurable
  · filter_upwards [hXpos] with ω hω
    have hnonneg := exponentialMixtureCDFKernel_nonneg hω ht
    have hle : exponentialMixtureCDFKernel (X ω) t ≤ 1 := by
      unfold exponentialMixtureCDFKernel
      nlinarith [Real.exp_pos (-t / X ω)]
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

/-- Exact representation of the density loss as one integral. -/
theorem exponentialMixtureLambda_sub_density_eq_integral
    {μ : Measure Ω} {X : Ω → ℝ} (hXmeas : Measurable X)
    (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    (hInv : Integrable (fun ω ↦ (X ω)⁻¹) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    exponentialMixtureLambda μ X - exponentialMixtureDensity μ X t =
      ∫ ω, ((X ω)⁻¹ - exponentialMixtureDensityKernel (X ω) t) ∂μ := by
  unfold exponentialMixtureLambda exponentialMixtureDensity
  rw [integral_sub hInv
    (integrable_exponentialMixtureDensityKernel hXmeas hXpos hInv t ht)]

/-- Exact finite density local-flatness bound:
`0 ≤ Lambda - rho(t) ≤ t L2`. -/
theorem exponentialMixtureDensity_finite_localFlatness
    {μ : Measure Ω} {X : Ω → ℝ} (hXmeas : Measurable X)
    (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    (hInv : Integrable (fun ω ↦ (X ω)⁻¹) μ)
    (hInv2 : Integrable (fun ω ↦ (X ω)⁻¹ ^ 2) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ exponentialMixtureLambda μ X - exponentialMixtureDensity μ X t ∧
      exponentialMixtureLambda μ X - exponentialMixtureDensity μ X t ≤
        t * exponentialMixtureSecondInverseMoment μ X := by
  rw [exponentialMixtureLambda_sub_density_eq_integral hXmeas hXpos hInv t ht]
  constructor
  · exact integral_nonneg_of_ae (by
      filter_upwards [hXpos] with ω hω
      exact exponentialMixtureDensityLoss_nonneg hω ht)
  · calc
      (∫ ω, ((X ω)⁻¹ - exponentialMixtureDensityKernel (X ω) t) ∂μ) ≤
          ∫ ω, t * (X ω)⁻¹ ^ 2 ∂μ := by
            apply integral_mono_ae
            · exact hInv.sub
                (integrable_exponentialMixtureDensityKernel hXmeas hXpos hInv t ht)
            · exact hInv2.const_mul t
            · filter_upwards [hXpos] with ω hω
              exact exponentialMixtureDensityLoss_le hω ht
      _ = t * exponentialMixtureSecondInverseMoment μ X := by
        rw [integral_const_mul]
        rfl

/-- Exact representation of the linearized CDF loss as one integral. -/
theorem exponentialMixtureLinear_sub_CDF_eq_integral
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hXmeas : Measurable X) (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    (hInv : Integrable (fun ω ↦ (X ω)⁻¹) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    t * exponentialMixtureLambda μ X - exponentialMixtureCDF μ X t =
      ∫ ω, (t * (X ω)⁻¹ - exponentialMixtureCDFKernel (X ω) t) ∂μ := by
  unfold exponentialMixtureLambda exponentialMixtureCDF
  rw [integral_sub (hInv.const_mul t)
    (integrable_exponentialMixtureCDFKernel hXmeas hXpos t ht),
    integral_const_mul]

/-- Exact finite CDF local-flatness bound:
`0 ≤ Lambda t - F(t) ≤ t² L2 / 2`. -/
theorem exponentialMixtureCDF_finite_localFlatness
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hXmeas : Measurable X) (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    (hInv : Integrable (fun ω ↦ (X ω)⁻¹) μ)
    (hInv2 : Integrable (fun ω ↦ (X ω)⁻¹ ^ 2) μ)
    {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ t * exponentialMixtureLambda μ X - exponentialMixtureCDF μ X t ∧
      t * exponentialMixtureLambda μ X - exponentialMixtureCDF μ X t ≤
        t ^ 2 * exponentialMixtureSecondInverseMoment μ X / 2 := by
  rw [exponentialMixtureLinear_sub_CDF_eq_integral hXmeas hXpos hInv t ht]
  constructor
  · exact integral_nonneg_of_ae (by
      filter_upwards [hXpos] with ω hω
      exact exponentialMixtureCDFLoss_nonneg hω ht)
  · calc
      (∫ ω, (t * (X ω)⁻¹ - exponentialMixtureCDFKernel (X ω) t) ∂μ) ≤
          ∫ ω, (t ^ 2 / 2) * (X ω)⁻¹ ^ 2 ∂μ := by
            apply integral_mono_ae
            · exact (hInv.const_mul t).sub
                (integrable_exponentialMixtureCDFKernel hXmeas hXpos t ht)
            · exact hInv2.const_mul (t ^ 2 / 2)
            · filter_upwards [hXpos] with ω hω
              have h := exponentialMixtureCDFLoss_le hω ht
              nlinarith
      _ = t ^ 2 * exponentialMixtureSecondInverseMoment μ X / 2 := by
        rw [integral_const_mul]
        unfold exponentialMixtureSecondInverseMoment
        ring

/-- A scale condition turns the density error bound into an explicit
fractional lower bound.  If `t L2 ≤ delta Lambda`, then
`rho(t) ≥ (1-delta) Lambda`. -/
theorem exponentialMixtureDensity_lowerBound_fraction
    {μ : Measure Ω} {X : Ω → ℝ} (hXmeas : Measurable X)
    (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    (hInv : Integrable (fun ω ↦ (X ω)⁻¹) μ)
    (hInv2 : Integrable (fun ω ↦ (X ω)⁻¹ ^ 2) μ)
    {t delta : ℝ} (ht : 0 ≤ t)
    (hscale : t * exponentialMixtureSecondInverseMoment μ X ≤
      delta * exponentialMixtureLambda μ X) :
    (1 - delta) * exponentialMixtureLambda μ X ≤
      exponentialMixtureDensity μ X t := by
  have h := (exponentialMixtureDensity_finite_localFlatness
    hXmeas hXpos hInv hInv2 ht).2
  linarith

/-- A scale condition turns the CDF error bound into an explicit
fractional small-ball lower bound.  If `t L2 ≤ delta Lambda`, then
`F(t) ≥ (1-delta/2) Lambda t`. -/
theorem exponentialMixtureCDF_lowerBound_fraction
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hXmeas : Measurable X) (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    (hInv : Integrable (fun ω ↦ (X ω)⁻¹) μ)
    (hInv2 : Integrable (fun ω ↦ (X ω)⁻¹ ^ 2) μ)
    {t delta : ℝ} (ht : 0 ≤ t)
    (hscale : t * exponentialMixtureSecondInverseMoment μ X ≤
      delta * exponentialMixtureLambda μ X) :
    (1 - delta / 2) *
        (exponentialMixtureLambda μ X * t) ≤
      exponentialMixtureCDF μ X t := by
  have herror := (exponentialMixtureCDF_finite_localFlatness
    hXmeas hXpos hInv hInv2 ht).2
  have hmul := mul_le_mul_of_nonneg_left hscale ht
  nlinarith

/-- Direct lower bound for the normalized amplitude ball.  Substituting
`t = r²` into the CDF estimate gives
`P(|H|/sigma ≤ r) ≥ Lambda r² - L2 r⁴ / 2`. -/
theorem exponentialMixtureAmplitudeRadius_lowerBound
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hXmeas : Measurable X) (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    (hInv : Integrable (fun ω ↦ (X ω)⁻¹) μ)
    (hInv2 : Integrable (fun ω ↦ (X ω)⁻¹ ^ 2) μ)
    (r : ℝ) :
    exponentialMixtureLambda μ X * r ^ 2 -
        r ^ 4 * exponentialMixtureSecondInverseMoment μ X / 2 ≤
      exponentialMixtureCDF μ X (r ^ 2) := by
  have h := (exponentialMixtureCDF_finite_localFlatness
    hXmeas hXpos hInv hInv2 (sq_nonneg r)).2
  nlinarith [sq_nonneg (r ^ 2)]

/-- Fractional amplitude-ball lower bound at any radius satisfying the
explicit correction-scale condition. -/
theorem exponentialMixtureAmplitudeRadius_lowerBound_fraction
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hXmeas : Measurable X) (hXpos : ∀ᵐ ω ∂μ, 0 < X ω)
    (hInv : Integrable (fun ω ↦ (X ω)⁻¹) μ)
    (hInv2 : Integrable (fun ω ↦ (X ω)⁻¹ ^ 2) μ)
    {r delta : ℝ}
    (hscale : r ^ 2 * exponentialMixtureSecondInverseMoment μ X ≤
      delta * exponentialMixtureLambda μ X) :
    (1 - delta / 2) *
        (exponentialMixtureLambda μ X * r ^ 2) ≤
      exponentialMixtureCDF μ X (r ^ 2) := by
  exact exponentialMixtureCDF_lowerBound_fraction
    hXmeas hXpos hInv hInv2 (sq_nonneg r) hscale

end

end LogdetLean.GramHafnian
