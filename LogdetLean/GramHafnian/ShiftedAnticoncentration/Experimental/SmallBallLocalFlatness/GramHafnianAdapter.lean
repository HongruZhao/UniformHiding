import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.SmallBallLocalFlatness.IntegralBounds
import LogdetLean.GramHafnian.LocalAnticoncentration.LocalSharpness

/-!
# Conditional adapter to the Gaussian Gram-hafnian model

This file connects the universal exponential-mixture inequality to the
literal variables in the matrix-law development.  The exact identification
of the normalized amplitude-ball probability with the scalar exponential
mixture is kept as an explicit hypothesis.  Thus this adapter does not hide
the remaining measure-transport lemma, and the only new moment hypothesis is
ordinary integrability of `V_n⁻²`.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-- The conditional variance normalized by the exact hafnian second moment. -/
def localAnticoncentrationNormalizedPastVariance
    {n k : ℕ} (hn : 1 ≤ n)
    (A : OddCofactorIndex n hn → (Fin k → ℂ)) : ℝ :=
  pastCofactorV hn A / gramHafnianSigma k n ^ 2

theorem measurable_localAnticoncentrationNormalizedPastVariance
    {n k : ℕ} (hn : 1 ≤ n) :
    Measurable (localAnticoncentrationNormalizedPastVariance (k := k) hn) := by
  unfold localAnticoncentrationNormalizedPastVariance
  fun_prop

/-- Positivity of the normalized variance in the paper dimension range. -/
theorem ae_localAnticoncentrationNormalizedPastVariance_pos
    {n k : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    ∀ᵐ A : OddCofactorIndex n hn → (Fin k → ℂ)
      ∂(Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k),
      0 < localAnticoncentrationNormalizedPastVariance (k := k) hn A := by
  have hkpos : 0 < k := by omega
  have hsigma : 0 < gramHafnianSigma k n :=
    gramHafnianSigma_pos k n hkpos
  filter_upwards [Wishart.ae_pastCofactorV_pos_paperRange hn hkn] with A hA
  exact div_pos hA (sq_pos_of_pos hsigma)

/-- The already-verified first inverse moment gives integrability after exact
second-moment normalization. -/
theorem integrable_inv_localAnticoncentrationNormalizedPastVariance
    {n k : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    Integrable
      (fun A : OddCofactorIndex n hn → (Fin k → ℂ) ↦
        (localAnticoncentrationNormalizedPastVariance (k := k) hn A)⁻¹)
      (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k) := by
  have hkpos : 0 < k := by omega
  have hsigma : 0 < gramHafnianSigma k n :=
    gramHafnianSigma_pos k n hkpos
  have hbase := (integrable_pastCofactorV_inv_localAnticoncentration hn hkn).const_mul
    (gramHafnianSigma k n ^ 2)
  apply hbase.congr
  filter_upwards [] with A
  unfold localAnticoncentrationNormalizedPastVariance
  field_simp [hsigma.ne']

/-- A second inverse moment for `V_n` transports exactly to the normalized
mixing variable.  This is a hypothesis, not a proved hafnian moment bound. -/
theorem integrable_inv_sq_localAnticoncentrationNormalizedPastVariance_of_past
    {n k : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k)
    (hInv2 : Integrable
      (fun A : OddCofactorIndex n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹ ^ 2)
      (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)) :
    Integrable
      (fun A : OddCofactorIndex n hn → (Fin k → ℂ) ↦
        (localAnticoncentrationNormalizedPastVariance (k := k) hn A)⁻¹ ^ 2)
      (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k) := by
  have hkpos : 0 < k := by omega
  have hsigma : 0 < gramHafnianSigma k n :=
    gramHafnianSigma_pos k n hkpos
  have hbase := hInv2.const_mul (gramHafnianSigma k n ^ 4)
  apply hbase.congr
  filter_upwards [] with A
  unfold localAnticoncentrationNormalizedPastVariance
  field_simp [hsigma.ne']

/-- Exact scaling identity for the first inverse moment. -/
theorem exponentialMixtureLambda_normalizedPastVariance_eq
    {n k : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    exponentialMixtureLambda
        (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)
        (localAnticoncentrationNormalizedPastVariance (k := k) hn) =
      gramHafnianSigma k n ^ 2 *
        ∫ A : OddCofactorIndex n hn → (Fin k → ℂ),
          (pastCofactorV hn A)⁻¹
          ∂(Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k) := by
  have hkpos : 0 < k := by omega
  have hsigma : 0 < gramHafnianSigma k n :=
    gramHafnianSigma_pos k n hkpos
  unfold exponentialMixtureLambda
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with A
  unfold localAnticoncentrationNormalizedPastVariance
  field_simp [hsigma.ne']

/-- Exact scaling identity for the second inverse moment. -/
theorem exponentialMixtureSecondInverseMoment_normalizedPastVariance_eq
    {n k : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k) :
    exponentialMixtureSecondInverseMoment
        (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)
        (localAnticoncentrationNormalizedPastVariance (k := k) hn) =
      gramHafnianSigma k n ^ 4 *
        ∫ A : OddCofactorIndex n hn → (Fin k → ℂ),
          (pastCofactorV hn A)⁻¹ ^ 2
          ∂(Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k) := by
  have hkpos : 0 < k := by omega
  have hsigma : 0 < gramHafnianSigma k n :=
    gramHafnianSigma_pos k n hkpos
  unfold exponentialMixtureSecondInverseMoment
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with A
  unfold localAnticoncentrationNormalizedPastVariance
  field_simp [hsigma.ne']

/-- Unconditional model-specific lower bound obtained by integrating the
mixture-density tangent bound over a centered disk.  It loses the factor
`1/2` from the exact exponential CDF identity, but requires no extra law
identification: only `V_n⁻²` integrability remains a hypothesis. -/
theorem gramHafnian_normalizedAmplitudeBall_lowerBound_of_secondInverseMoment
    {n k : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k)
    (hInv2 : Integrable
      (fun A : OddCofactorIndex n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹ ^ 2)
      (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k))
    {r : ℝ} (hr : 0 ≤ r) :
    exponentialMixtureLambda
          (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)
          (localAnticoncentrationNormalizedPastVariance (k := k) hn) * r ^ 2 -
        r ^ 4 *
          exponentialMixtureSecondInverseMoment
            (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)
            (localAnticoncentrationNormalizedPastVariance (k := k) hn) ≤
      (circularGaussianColumnMatrixMeasure n k).real
        {Y | ‖gramHafnianObservable n k Y‖ ≤
          r * gramHafnianSigma k n} := by
  let ν : Measure (OddCofactorIndex n hn → (Fin k → ℂ)) :=
    Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k
  let V : (OddCofactorIndex n hn → (Fin k → ℂ)) → ℝ := pastCofactorV hn
  let sigma : ℝ := gramHafnianSigma k n
  let R : ℝ := r * sigma
  let LambdaV : ℝ := exponentialMixtureLambda ν V
  let L2V : ℝ := exponentialMixtureSecondInverseMoment ν V
  let f : ℂ → ℝ := localAnticoncentrationGramHafnianDensity (k := k) hn
  have hkpos : 0 < k := by omega
  have hsigma : 0 < sigma := by
    exact gramHafnianSigma_pos k n hkpos
  have hR : 0 ≤ R := mul_nonneg hr hsigma.le
  have hVmeas : Measurable V := by
    exact measurable_pastCofactorV hn
  have hVpos : ∀ᵐ A ∂ν, 0 < V A := by
    simpa [ν, V] using Wishart.ae_pastCofactorV_pos_paperRange hn hkn
  have hInv : Integrable (fun A ↦ (V A)⁻¹) ν := by
    simpa [ν, V] using integrable_pastCofactorV_inv_localAnticoncentration hn hkn
  have hInv2' : Integrable (fun A ↦ (V A)⁻¹ ^ 2) ν := by
    simpa [ν, V] using hInv2
  have hL2nonneg : 0 ≤ L2V := by
    unfold L2V exponentialMixtureSecondInverseMoment
    exact integral_nonneg_of_ae (ae_of_all ν fun A ↦ sq_nonneg (V A)⁻¹)
  have hf_eq (w : ℂ) :
      f w = Real.pi⁻¹ * exponentialMixtureDensity ν V (‖w‖ ^ 2) := by
    unfold f localAnticoncentrationGramHafnianDensity
    unfold exponentialMixtureDensity localAnticoncentrationGramHafnianDensityIntegrand
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with A
    unfold exponentialMixtureDensityKernel
    ring
  have hpoint : ∀ w ∈ Metric.closedBall (0 : ℂ) R,
      Real.pi⁻¹ * (LambdaV - R ^ 2 * L2V) ≤ f w := by
    intro w hw
    have hnorm : ‖w‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hnormsq : ‖w‖ ^ 2 ≤ R ^ 2 := by nlinarith [norm_nonneg w]
    have hflat := (exponentialMixtureDensity_finite_localFlatness
      hVmeas hVpos hInv hInv2' (sq_nonneg ‖w‖)).2
    have hrho : LambdaV - R ^ 2 * L2V ≤
        exponentialMixtureDensity ν V (‖w‖ ^ 2) := by
      dsimp [LambdaV, L2V] at hflat ⊢
      nlinarith
    rw [hf_eq]
    exact mul_le_mul_of_nonneg_left hrho (inv_nonneg.mpr Real.pi_pos.le)
  have hset := setIntegral_ge_of_const_le_real
    (μ := (volume : Measure ℂ)) (s := Metric.closedBall (0 : ℂ) R)
    (f := f) measurableSet_closedBall
    (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
    hpoint (integrable_localAnticoncentrationGramHafnianDensity_volume hn hkn).integrableOn
  have hvolume :
      (volume : Measure ℂ).real (Metric.closedBall (0 : ℂ) R) =
        Real.pi * R ^ 2 :=
    volumeReal_complex_closedBall 0 R hR
  rw [hvolume] at hset
  have hset' : R ^ 2 * LambdaV - R ^ 4 * L2V ≤
      ∫ w in Metric.closedBall (0 : ℂ) R, f w ∂volume := by
    calc
      R ^ 2 * LambdaV - R ^ 4 * L2V =
          (Real.pi⁻¹ * (LambdaV - R ^ 2 * L2V)) *
            (Real.pi * R ^ 2) := by
              field_simp [Real.pi_ne_zero]
      _ ≤ ∫ w in Metric.closedBall (0 : ℂ) R, f w ∂volume := hset
  have hevent :
      {Y | ‖gramHafnianObservable n k Y‖ ≤ R} =
        gramHafnianObservable n k ⁻¹' Metric.closedBall (0 : ℂ) R := by
    ext Y
    simp [Metric.mem_closedBall, dist_eq_norm]
  have hprob :
      (circularGaussianColumnMatrixMeasure n k).real
          {Y | ‖gramHafnianObservable n k Y‖ ≤ R} =
        ∫ w in Metric.closedBall (0 : ℂ) R, f w ∂volume := by
    rw [hevent]
    rw [← MeasureTheory.map_measureReal_apply
      (measurable_gramHafnianObservable n k) measurableSet_closedBall]
    rw [map_gramHafnianObservable_eq_withDensity_real hn hkn]
    exact withDensity_ofReal_measureReal_eq_setIntegral f
      (integrable_localAnticoncentrationGramHafnianDensity_volume hn hkn)
      (fun w ↦ localAnticoncentrationGramHafnianDensity_nonneg hn w)
      (Metric.closedBall (0 : ℂ) R) measurableSet_closedBall
  rw [← hprob] at hset'
  rw [exponentialMixtureLambda_normalizedPastVariance_eq hn hkn,
    exponentialMixtureSecondInverseMoment_normalizedPastVariance_eq hn hkn]
  dsimp [ν, V, sigma, R, LambdaV, L2V] at hset' ⊢
  unfold exponentialMixtureLambda exponentialMixtureSecondInverseMoment at hset'
  convert hset' using 1 <;> ring

/-- Finite local-flatness form of the model-specific result.  Whenever the
radius obeys `r² L2 ≤ delta Lambda`, the normalized hafnian small ball keeps
at least the fraction `1-delta` of its zero-radius linear coefficient. -/
theorem gramHafnian_normalizedAmplitudeBall_lowerBound_fraction_of_secondInverseMoment
    {n k : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k)
    (hInv2 : Integrable
      (fun A : OddCofactorIndex n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹ ^ 2)
      (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k))
    {r delta : ℝ} (hr : 0 ≤ r)
    (hscale :
      r ^ 2 *
          exponentialMixtureSecondInverseMoment
            (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)
            (localAnticoncentrationNormalizedPastVariance (k := k) hn) ≤
        delta *
          exponentialMixtureLambda
            (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)
            (localAnticoncentrationNormalizedPastVariance (k := k) hn)) :
    (1 - delta) *
        (exponentialMixtureLambda
          (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)
          (localAnticoncentrationNormalizedPastVariance (k := k) hn) * r ^ 2) ≤
      (circularGaussianColumnMatrixMeasure n k).real
        {Y | ‖gramHafnianObservable n k Y‖ ≤
          r * gramHafnianSigma k n} := by
  have hmain := gramHafnian_normalizedAmplitudeBall_lowerBound_of_secondInverseMoment
    hn hkn hInv2 hr
  have hmul := mul_le_mul_of_nonneg_left hscale (sq_nonneg r)
  nlinarith

/-- Conditional finite small-ball lower bound for the literal normalized
Gram hafnian.  The hypothesis `hCDF` is precisely the remaining equality
between the amplitude-ball probability and the exponential mixture CDF. -/
theorem gramHafnian_normalizedAmplitudeBall_lowerBound_of_mixtureCDF
    {n k : ℕ} (hn : 1 ≤ n) (hkn : 4 * n ≤ k)
    (hInv2 : Integrable
      (fun A : OddCofactorIndex n hn → (Fin k → ℂ) ↦
        (pastCofactorV hn A)⁻¹ ^ 2)
      (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k))
    (r : ℝ)
    (hCDF :
      (circularGaussianColumnMatrixMeasure n k).real
          {Y | ‖gramHafnianObservable n k Y‖ ≤
            r * gramHafnianSigma k n} =
        exponentialMixtureCDF
          (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)
          (localAnticoncentrationNormalizedPastVariance (k := k) hn) (r ^ 2)) :
    exponentialMixtureLambda
          (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)
          (localAnticoncentrationNormalizedPastVariance (k := k) hn) * r ^ 2 -
        r ^ 4 *
          exponentialMixtureSecondInverseMoment
            (Measure.pi fun _ : OddCofactorIndex n hn ↦ circularGaussianVector k)
            (localAnticoncentrationNormalizedPastVariance (k := k) hn) / 2 ≤
      (circularGaussianColumnMatrixMeasure n k).real
        {Y | ‖gramHafnianObservable n k Y‖ ≤
          r * gramHafnianSigma k n} := by
  rw [hCDF]
  exact exponentialMixtureAmplitudeRadius_lowerBound
    (measurable_localAnticoncentrationNormalizedPastVariance hn)
    (ae_localAnticoncentrationNormalizedPastVariance_pos hn hkn)
    (integrable_inv_localAnticoncentrationNormalizedPastVariance hn hkn)
    (integrable_inv_sq_localAnticoncentrationNormalizedPastVariance_of_past hn hkn hInv2)
    r

end

end LogdetLean.GramHafnian
