import LogdetLean.GramHafnian.CurrentPRL.MixtureDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Shrinking disk limit for the current PRL

The proof is an every point continuity argument.  It does not invoke the
almost everywhere Lebesgue differentiation theorem.
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

namespace LogdetLean.GramHafnian

noncomputable section

/-- Real planar volume of a complex closed disk. -/
theorem volumeReal_complex_closedBall (z : ℂ) (rho : ℝ) (hrho : 0 ≤ rho) :
    (volume : Measure ℂ).real (closedBall z rho) = Real.pi * rho ^ 2 := by
  rw [measureReal_def, Complex.volume_closedBall,
    ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hrho]
  simp only [ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring

/-- A nonnegative real density has the expected real set integral under
`withDensity`. -/
theorem withDensity_ofReal_measureReal_eq_setIntegral
    (f : ℂ → ℝ) (hf : Integrable f (volume : Measure ℂ))
    (hnonneg : ∀ w, 0 ≤ f w) (s : Set ℂ) (hs : MeasurableSet s) :
    ((volume : Measure ℂ).withDensity (fun w ↦ ENNReal.ofReal (f w))).real s =
      ∫ w in s, f w ∂volume := by
  have hint : Integrable f ((volume : Measure ℂ).restrict s) := hf.integrableOn
  have hnonneg_ae : 0 ≤ᵐ[(volume : Measure ℂ).restrict s] f :=
    ae_of_all _ hnonneg
  have heq := ofReal_integral_eq_lintegral_ofReal hint hnonneg_ae
  rw [measureReal_def, withDensity_apply _ hs, ← heq,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg_ae)]

/-- Continuous density averaging over a shrinking complex disk. -/
theorem tendsto_setIntegral_complex_closedBall_div_sq
    (f : ℂ → ℝ) (hfcont : Continuous f)
    (hfint : Integrable f (volume : Measure ℂ)) (z : ℂ) :
    Tendsto
      (fun rho : ℝ ↦ (∫ w in closedBall z rho, f w ∂volume) / rho ^ 2)
      (𝓝[>] 0) (𝓝 (Real.pi * f z)) := by
  refine Metric.tendsto_nhds.2 fun eps heps ↦ ?_
  let C : ℝ := eps / (2 * Real.pi)
  have hC : 0 < C := div_pos heps (mul_pos (by norm_num) Real.pi_pos)
  have hlocal :=
    (Metric.tendsto_nhds.1
      (hfcont.continuousAt : ContinuousAt f z)) C hC
  rcases Metric.eventually_nhds_iff.1 hlocal with
    ⟨delta, hdelta, hnear⟩
  filter_upwards [Ioo_mem_nhdsGT hdelta] with rho hrho
  have hrhopos : 0 < rho := hrho.1
  have hrhole : 0 ≤ rho := hrhopos.le
  let s : Set ℂ := closedBall z rho
  have hscompact : IsCompact s := isCompact_closedBall z rho
  have hsfinite : (volume : Measure ℂ) s < ⊤ :=
    hscompact.measure_lt_top
  have hpoint : ∀ w ∈ s, ‖f w - f z‖ ≤ C := by
    intro w hw
    have hwdelta : dist w z < delta :=
      (mem_closedBall.1 hw).trans_lt hrho.2
    have hdist := hnear hwdelta
    simpa [Real.dist_eq] using hdist.le
  have hnorm :
      ‖∫ w in s, (f w - f z) ∂volume‖ ≤
        C * (volume : Measure ℂ).real s :=
    norm_setIntegral_le_of_norm_le_const hsfinite hpoint
  have hvol : (volume : Measure ℂ).real s = Real.pi * rho ^ 2 := by
    exact volumeReal_complex_closedBall z rho hrhole
  have hdiff :
      (∫ w in s, f w ∂volume) -
          (Real.pi * rho ^ 2) * f z =
        ∫ w in s, (f w - f z) ∂volume := by
    rw [integral_sub hfint.integrableOn integrableOn_const,
      setIntegral_const, hvol]
    simp [smul_eq_mul]
  rw [Real.dist_eq]
  have hrewrite :
      (∫ w in s, f w ∂volume) / rho ^ 2 - Real.pi * f z =
        (∫ w in s, (f w - f z) ∂volume) / rho ^ 2 := by
    rw [← hdiff]
    field_simp [hrhopos.ne']
  rw [hrewrite, abs_div, abs_of_pos (sq_pos_of_pos hrhopos)]
  calc
    |∫ w in s, (f w - f z) ∂volume| / rho ^ 2 ≤
        (C * (volume : Measure ℂ).real s) / rho ^ 2 := by
      exact div_le_div_of_nonneg_right (by simpa [Real.norm_eq_abs] using hnorm)
        (sq_nonneg rho)
    _ = C * Real.pi := by
      rw [hvol]
      field_simp [hrhopos.ne']
    _ = eps / 2 := by
      dsimp [C]
      field_simp [Real.pi_ne_zero]
    _ < eps := half_lt_self heps

/-- Shrinking disk limit for a measure with a continuous nonnegative real
density. -/
theorem tendsto_withDensity_complex_closedBall_div_sq
    (f : ℂ → ℝ) (hfcont : Continuous f)
    (hfint : Integrable f (volume : Measure ℂ))
    (hnonneg : ∀ w, 0 ≤ f w) (z : ℂ) :
    Tendsto
      (fun rho : ℝ ↦
        ((volume : Measure ℂ).withDensity
          (fun w ↦ ENNReal.ofReal (f w))).real (closedBall z rho) / rho ^ 2)
      (𝓝[>] 0) (𝓝 (Real.pi * f z)) := by
  apply (tendsto_setIntegral_complex_closedBall_div_sq f hfcont hfint z).congr'
  filter_upwards [] with rho
  rw [withDensity_ofReal_measureReal_eq_setIntegral f hfint hnonneg
    (closedBall z rho) measurableSet_closedBall]

/-! ## Application to the literal Gaussian Gram hafnian -/

/-- Equation (13) as an equality with the paper's real valued density. -/
theorem map_gramHafnianObservable_eq_withDensity_real
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    (circularGaussianColumnMatrixMeasure r k).map
        (gramHafnianObservable r k) =
      (volume : Measure ℂ).withDensity
        (fun w ↦ ENNReal.ofReal
          (currentPRLGramHafnianDensity (k := k) hr w)) := by
  rw [map_gramHafnianObservable_eq_withDensity_mixture hr hk]
  congr 1
  funext w
  exact currentPRLGramHafnianMixtureDensity_eq_ofReal hr hk w

/-- The real density integrates to one, hence is globally integrable. -/
theorem integrable_currentPRLGramHafnianDensity_volume
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) :
    Integrable (currentPRLGramHafnianDensity (k := k) hr)
      (volume : Measure ℂ) := by
  let f : ℂ → ℝ := currentPRLGramHafnianDensity (k := k) hr
  have hfmeas : AEStronglyMeasurable f (volume : Measure ℂ) :=
    (continuous_currentPRLGramHafnianDensity hr hk).aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[(volume : Measure ℂ)] f :=
    ae_of_all _ fun w ↦ currentPRLGramHafnianDensity_nonneg hr w
  apply (lintegral_ofReal_ne_top_iff_integrable hfmeas hnonneg).mp
  have hlaw := map_gramHafnianObservable_eq_withDensity_real hr hk
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

/-- Unnormalized every-center shrinking-disk limit for the literal Gram
hafnian law. -/
theorem gramHafnian_raw_shrinkingDisk_limit
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) (z : ℂ) :
    Tendsto
      (fun rho : ℝ ↦
        (circularGaussianColumnMatrixMeasure r k).real
            {X | ‖gramHafnianObservable r k X - z‖ ≤ rho} / rho ^ 2)
      (𝓝[>] 0)
      (𝓝 (Real.pi * currentPRLGramHafnianDensity (k := k) hr z)) := by
  let f : ℂ → ℝ := currentPRLGramHafnianDensity (k := k) hr
  have hbase := tendsto_withDensity_complex_closedBall_div_sq f
    (continuous_currentPRLGramHafnianDensity hr hk)
    (integrable_currentPRLGramHafnianDensity_volume hr hk)
    (fun w ↦ currentPRLGramHafnianDensity_nonneg hr w) z
  rw [← map_gramHafnianObservable_eq_withDensity_real hr hk] at hbase
  apply hbase.congr'
  filter_upwards [] with rho
  rw [MeasureTheory.map_measureReal_apply
    (measurable_gramHafnianObservable r k) measurableSet_closedBall]
  congr 2
  ext X
  simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_closedBall,
    dist_eq_norm]

/-- Equation (14), first in the exact density form. -/
theorem gramHafnian_normalized_shrinkingDisk_limit_density
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) (z : ℂ) :
    Tendsto
      (fun eps : ℝ ↦
        (circularGaussianColumnMatrixMeasure r k).real
            {X | ‖gramHafnianObservable r k X - z‖ ≤
              eps * gramHafnianSigma k r} / eps ^ 2)
      (𝓝[>] 0)
      (𝓝 (gramHafnianSigma k r ^ 2 *
        (Real.pi * currentPRLGramHafnianDensity (k := k) hr z))) := by
  have hkpos : 0 < k := by omega
  have hsigma : 0 < gramHafnianSigma k r :=
    gramHafnianSigma_pos k r hkpos
  have hscale : Tendsto
      (fun eps : ℝ ↦ eps * gramHafnianSigma k r)
      (𝓝[>] 0) (𝓝[>] 0) := by
    have hid : Tendsto (fun eps : ℝ ↦ eps) (𝓝[>] 0) (𝓝[>] 0) :=
      tendsto_id
    simpa using Filter.TendstoNhdsWithinIoi.mul_const hsigma hid
  have hraw := (gramHafnian_raw_shrinkingDisk_limit hr hk z).comp hscale
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
        (Real.pi * currentPRLGramHafnianDensity (k := k) hr z))) := by
    simpa [mul_comm] using hmul
  apply hmul'.congr'
  filter_upwards [self_mem_nhdsWithin] with eps heps
  have hepspos : 0 < eps := heps
  field_simp [hepspos.ne', hsigma.ne']

/-- The expectation on the right side of Equation (14), without the `π⁻¹`
appearing in the planar density. -/
def currentPRLLocalSharpnessCoefficient
    {r k : ℕ} (hr : 1 ≤ r) (z : ℂ) : ℝ :=
  ∫ A : OddCofactorIndex r hr → (Fin k → ℂ),
    (pastCofactorV hr A)⁻¹ *
      Real.exp (-‖z‖ ^ 2 / pastCofactorV hr A)
      ∂(Measure.pi fun _ : OddCofactorIndex r hr ↦ circularGaussianVector k)

/-- Equation (13) identifies `π f(z)` with the expectation used in
Equation (14). -/
theorem pi_mul_currentPRLGramHafnianDensity_eq_localSharpnessCoefficient
    {r k : ℕ} (hr : 1 ≤ r) (z : ℂ) :
    Real.pi * currentPRLGramHafnianDensity (k := k) hr z =
      currentPRLLocalSharpnessCoefficient (k := k) hr z := by
  rw [currentPRLGramHafnianDensity,
    currentPRLLocalSharpnessCoefficient, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with A
  unfold currentPRLGramHafnianDensityIntegrand
  field_simp [Real.pi_ne_zero]

/-- Equation (14) in the exact expectation notation printed in the PRL. -/
theorem gramHafnian_normalized_shrinkingDisk_limit
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) (z : ℂ) :
    Tendsto
      (fun eps : ℝ ↦
        (circularGaussianColumnMatrixMeasure r k).real
            {X | ‖gramHafnianObservable r k X - z‖ ≤
              eps * gramHafnianSigma k r} / eps ^ 2)
      (𝓝[>] 0)
      (𝓝 (gramHafnianSigma k r ^ 2 *
        currentPRLLocalSharpnessCoefficient (k := k) hr z)) := by
  simpa [pi_mul_currentPRLGramHafnianDensity_eq_localSharpnessCoefficient]
    using gramHafnian_normalized_shrinkingDisk_limit_density hr hk z

/-- The limiting coefficient in Equation (14) is strictly positive at every
fixed center. -/
theorem gramHafnian_normalized_shrinkingDisk_limit_coefficient_pos
    {r k : ℕ} (hr : 1 ≤ r) (hk : 4 * r ≤ k) (z : ℂ) :
    0 < gramHafnianSigma k r ^ 2 *
      currentPRLLocalSharpnessCoefficient (k := k) hr z := by
  have hkpos : 0 < k := by omega
  have hsigma : 0 < gramHafnianSigma k r :=
    gramHafnianSigma_pos k r hkpos
  have hfpos := currentPRLGramHafnianDensity_pos hr hk z
  rw [← pi_mul_currentPRLGramHafnianDensity_eq_localSharpnessCoefficient]
  exact mul_pos (sq_pos_of_pos hsigma) (mul_pos Real.pi_pos hfpos)

end

end LogdetLean.GramHafnian
