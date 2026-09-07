import LogdetLean.WishartActualGlobalLog
import LogdetLean.GeneralRAnalyticLogSmoothing
import LogdetLean.GeneralRStatistic
import LogdetLean.GeneralRFinalRateLimit
import LogdetLean.NormalScaleComparison
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Tactic

/-!
# Quantitative normal approximation for the actual general-R leading term

This module closes the model-specific analytic-log step.  It standardizes the
actual Gaussian/Wishart leading variable by its exact standard deviation,
instantiates the proved Fejer--Esseen analytic-log theorem, replaces the exact
scale by the paper's proxy scale, and finally combines this with the already
proved nonlinear-remainder estimate for the actual statistic.

No probability law is postulated: every measure below is a pushforward of the
original standard Gaussian data measure.  The transform formulas ultimately
follow Zhao, arXiv:2608.00565v1, Lemma 5.4; the smoothing theorem is the proved
Fejer version of Feller, Vol. II (1971), Lemma XVI.3.1, p. 537.
-/

namespace LogdetLean

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Topology

/-- Iterated derivatives commute with real scalar precomposition for a
complex-valued function.  This totalized-derivative identity requires no
differentiability hypothesis. -/
theorem iteratedDeriv_comp_mul_left_complex
    (r : ℕ) (c : ℝ) (f : ℝ → ℂ) (x : ℝ) :
    iteratedDeriv r (fun t ↦ f (c * t)) x =
      c ^ r • iteratedDeriv r f (c * x) := by
  induction r generalizing x with
  | zero => simp
  | succ r ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hfun : iteratedDeriv r (fun t ↦ f (c * t)) =
          fun t ↦ c ^ r • iteratedDeriv r f (c * t) := by
        funext t
        exact ih t
      rw [hfun, deriv_fun_const_smul_field, deriv_comp_mul_left]
      rw [pow_succ, mul_smul]

/-- Law of `M_R/w_R`, where `w_R` is the exact leading standard deviation. -/
def actualWishartLeadingStandardizedLaw {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) : Measure ℝ :=
  Measure.map
    (fun z ↦ GeneralRDecomposition.M_R m R z /
      generalRLeadingScale m R)
    (standardGaussianDataMeasure m p)

/-- The global additive logarithm after exact-variance normalization. -/
def actualWishartNormalizedGlobalLog {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) (t : ℝ) : ℂ :=
  actualWishartGlobalLog m R
    ((1 / generalRLeadingScale m R) * t)

/-- Exact normalized third-derivative envelope. -/
def generalRLeadingAnalyticBeta {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) : ℝ :=
  generalRLeadingThirdEnvelopeSpectral m R /
    generalRLeadingScale m R ^ 3

instance actualWishartLeadingStandardizedLaw_isProbabilityMeasure
    {p : ℕ} (m : ℕ) (R : CorrelationMatrix p) :
    IsProbabilityMeasure (actualWishartLeadingStandardizedLaw m R) := by
  unfold actualWishartLeadingStandardizedLaw
  exact Measure.isProbabilityMeasure_map
    ((GeneralRDecomposition.measurable_M_R m R).div_const _).aemeasurable

theorem charFun_actualWishartLeadingStandardizedLaw
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) (t : ℝ) :
    charFun (actualWishartLeadingStandardizedLaw m R) t =
      Complex.exp (actualWishartNormalizedGlobalLog m R t) := by
  have hm : 0 < m := by
    have hp := h.1
    have hpm := h.2
    omega
  unfold actualWishartLeadingStandardizedLaw
    actualWishartNormalizedGlobalLog
  rw [show (fun z ↦ GeneralRDecomposition.M_R m R z /
      generalRLeadingScale m R) =
      (fun z ↦ (1 / generalRLeadingScale m R) *
        GeneralRDecomposition.M_R m R z) by
    funext z
    ring]
  rw [charFun_map_mul_comp
    (GeneralRDecomposition.measurable_M_R m R).aemeasurable]
  rw [charFun_map_M_R hm h.2 R]
  symm
  simpa [actualWishartFrequencyCurve] using
    cexp_actualWishartGlobalLog_eq_frequencyCurve h R
      ((1 / generalRLeadingScale m R) * t)

theorem integrable_id_actualWishartLeadingStandardizedLaw
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    Integrable (fun x : ℝ ↦ x)
      (actualWishartLeadingStandardizedLaw m R) := by
  have hm : 0 < m := by
    have hp := h.1
    have hpm := h.2
    omega
  have hM := integrable_M_R_from_exact_transform hm h.2 R
  have hscaled : Integrable
      (fun z ↦ GeneralRDecomposition.M_R m R z /
        generalRLeadingScale m R)
      (standardGaussianDataMeasure m p) := by
    apply (hM.const_mul (1 / generalRLeadingScale m R)).congr
    filter_upwards [] with z
    ring
  unfold actualWishartLeadingStandardizedLaw
  apply (integrable_map_measure
    (g := fun x : ℝ ↦ x)
    (f := fun z ↦ GeneralRDecomposition.M_R m R z /
      generalRLeadingScale m R)
    (by fun_prop)
    ((GeneralRDecomposition.measurable_M_R m R).div_const _).aemeasurable).2
  change Integrable
    (fun z ↦ GeneralRDecomposition.M_R m R z /
      generalRLeadingScale m R)
    (standardGaussianDataMeasure m p)
  exact hscaled

/-- The (unstandardized) pushforward law of `M_R` has a finite second
moment.  This is the law-level form of the exponential-integrability
certificate proved from the exact transform. -/
theorem memLp_id_map_M_R_two
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    MemLp id 2
      (Measure.map (GeneralRDecomposition.M_R m R)
        (standardGaussianDataMeasure m p)) := by
  have hm : 0 < m := by
    have hp := h.1
    have hpm := h.2
    omega
  rw [memLp_map_measure_iff (by fun_prop)
    (GeneralRDecomposition.measurable_M_R m R).aemeasurable]
  simpa [Function.comp_def] using
    memLp_M_R_two_from_exact_transform hm h.2 R

/-- The second moment of the actual leading law is exactly the deterministic
quantity used to define `generalRLeadingScale`. -/
theorem integral_sq_map_M_R_eq_generalRLeadingVarianceSq
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    ∫ x, x ^ 2 ∂(Measure.map (GeneralRDecomposition.M_R m R)
      (standardGaussianDataMeasure m p)) =
        generalRLeadingVarianceSq m R := by
  let μ := Measure.map (GeneralRDecomposition.M_R m R)
    (standardGaussianDataMeasure m p)
  have hm : 0 < m := by
    have hp := h.1
    have hpm := h.2
    omega
  have hμ2 : MemLp id 2 μ := by
    dsimp [μ]
    exact memLp_id_map_M_R_two h R
  have hcurve : charFun μ = actualWishartFrequencyCurve m R := by
    funext t
    dsimp [μ]
    exact charFun_map_M_R hm h.2 R t
  have hderiv := iteratedDeriv_charFun_zero hμ2
  rw [hcurve, iteratedDeriv_two_actualWishartFrequencyCurve_zero h R] at hderiv
  apply Complex.ofReal_injective
  norm_num [pow_two, Complex.I_mul_I] at hderiv ⊢
  exact hderiv.symm

theorem contDiff_three_actualWishartNormalizedGlobalLog
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    ContDiff ℝ 3 (actualWishartNormalizedGlobalLog m R) := by
  unfold actualWishartNormalizedGlobalLog
  exact (contDiff_three_actualWishartGlobalLog h R).comp
    (by fun_prop)

@[simp]
theorem actualWishartNormalizedGlobalLog_zero
    {m p : ℕ} (R : CorrelationMatrix p) :
    actualWishartNormalizedGlobalLog m R 0 = 0 := by
  simp [actualWishartNormalizedGlobalLog]

theorem iteratedDeriv_one_actualWishartNormalizedGlobalLog_zero
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    iteratedDeriv 1 (actualWishartNormalizedGlobalLog m R) 0 = 0 := by
  unfold actualWishartNormalizedGlobalLog
  rw [iteratedDeriv_comp_mul_left_complex]
  rw [iteratedDeriv_one_actualWishartGlobalLog h R]
  simp [actualWishartFrequencyLogDerivative_zero h R]

theorem iteratedDeriv_two_actualWishartNormalizedGlobalLog_zero
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    iteratedDeriv 2 (actualWishartNormalizedGlobalLog m R) 0 = -1 := by
  have hw := generalRLeadingScale_pos h R
  unfold actualWishartNormalizedGlobalLog
  rw [iteratedDeriv_comp_mul_left_complex]
  rw [iteratedDeriv_two_actualWishartGlobalLog h R]
  simp only [mul_zero]
  rw [actualWishartFrequencyLogDerivativeOne_zero h R,
    ← generalRLeadingScale_sq h R]
  rw [show (1 / generalRLeadingScale m R) ^ 2 =
      1 / generalRLeadingScale m R ^ 2 by
    simp [one_div, inv_pow], Complex.real_smul]
  push_cast
  field_simp [hw.ne']

theorem generalRLeadingAnalyticBeta_nonneg
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    0 ≤ generalRLeadingAnalyticBeta m R := by
  have henv := norm_iteratedDeriv_three_actualWishartGlobalLog_le_spectral
    h R 0
  have henv0 : 0 ≤ generalRLeadingThirdEnvelopeSpectral m R :=
    (norm_nonneg _).trans henv
  unfold generalRLeadingAnalyticBeta
  exact div_nonneg henv0 (pow_nonneg (generalRLeadingScale_pos h R).le 3)

theorem norm_iteratedDeriv_three_actualWishartNormalizedGlobalLog_le
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) (t : ℝ) :
    ‖iteratedDeriv 3 (actualWishartNormalizedGlobalLog m R) t‖ ≤
      generalRLeadingAnalyticBeta m R := by
  have hw := generalRLeadingScale_pos h R
  unfold actualWishartNormalizedGlobalLog
  rw [iteratedDeriv_comp_mul_left_complex]
  rw [norm_smul, Real.norm_of_nonneg (by positivity :
    0 ≤ (1 / generalRLeadingScale m R) ^ 3)]
  calc
    (1 / generalRLeadingScale m R) ^ 3 *
        ‖iteratedDeriv 3 (actualWishartGlobalLog m R)
          ((1 / generalRLeadingScale m R) * t)‖ ≤
      (1 / generalRLeadingScale m R) ^ 3 *
        generalRLeadingThirdEnvelopeSpectral m R :=
      mul_le_mul_of_nonneg_left
        (norm_iteratedDeriv_three_actualWishartGlobalLog_le_spectral
          h R ((1 / generalRLeadingScale m R) * t)) (by positivity)
    _ = generalRLeadingAnalyticBeta m R := by
      unfold generalRLeadingAnalyticBeta
      field_simp [hw.ne']

/-- End-to-end leading-term Berry--Esseen inequality at the exact variance
scale. -/
theorem kolmogorovDistance_M_R_leadingScale_le
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    kolmogorovDistance
        (actualWishartLeadingStandardizedLaw m R)
        (gaussianReal 0 1) ≤
      analyticLogNormalApproximationConstant *
        min 1 (generalRLeadingAnalyticBeta m R) := by
  apply kolmogorovDistance_gaussian_le_of_contDiff_log
    (actualWishartLeadingStandardizedLaw m R)
    (integrable_id_actualWishartLeadingStandardizedLaw h R)
    (actualWishartNormalizedGlobalLog m R)
    (generalRLeadingAnalyticBeta_nonneg h R)
    (charFun_actualWishartLeadingStandardizedLaw h R)
    (contDiff_three_actualWishartNormalizedGlobalLog h R)
    (actualWishartNormalizedGlobalLog_zero R)
    (iteratedDeriv_one_actualWishartNormalizedGlobalLog_zero h R)
    (iteratedDeriv_two_actualWishartNormalizedGlobalLog_zero h R)
    (norm_iteratedDeriv_three_actualWishartNormalizedGlobalLog_le h R)

/-- The exact-scale leading error simplified to the three deterministic rate
parameters used in the paper. -/
theorem kolmogorovDistance_M_R_leadingScale_le_rate
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    kolmogorovDistance
        (actualWishartLeadingStandardizedLaw m R)
        (gaussianReal 0 1) ≤ generalRLeadingNormalRate m R := by
  have hlead := kolmogorovDistance_M_R_leadingScale_le h R
  have hbeta :=
    generalRLeadingThirdEnvelopeSpectral_div_leadingScale_cube_le h R
  have hC : 0 ≤ analyticLogNormalApproximationConstant :=
    analyticLogNormalApproximationConstant_ge_one.trans' (by norm_num)
  unfold generalRLeadingNormalRate generalRThirdDerivativeRate
  exact hlead.trans (mul_le_mul_of_nonneg_left
    ((min_le_right 1 _).trans hbeta) hC)

/-- Leading-term bound at the proxy scale `s_R`, including the explicit
exact-to-proxy scale replacement cost. -/
theorem kolmogorovDistance_M_R_proxyScale_le
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    kolmogorovDistance
        (Measure.map
          (fun z ↦ GeneralRDecomposition.M_R m R z /
            generalRProxyScale m R)
          (standardGaussianDataMeasure m p))
        (gaussianReal 0 1) ≤
      generalRLeadingNormalRate m R + generalRScaleMismatchRate p := by
  let w := generalRLeadingScale m R
  let s := generalRProxyScale m R
  let mu := actualWishartLeadingStandardizedLaw m R
  have hw : 0 < w := generalRLeadingScale_pos h R
  have hs : 0 < s := generalRProxyScale_pos h R
  have hscale := generalRScale_difference_bounds h R
  have hreplace :=
    kolmogorovDistance_scale_replacement_le_relative_sq_error
      mu hw hs hscale.1 hscale.2
  have hmap : mu.map (fun y ↦ (w / s) * y) =
      Measure.map
        (fun z ↦ GeneralRDecomposition.M_R m R z / s)
        (standardGaussianDataMeasure m p) := by
    unfold mu actualWishartLeadingStandardizedLaw
    rw [Measure.map_map (by fun_prop)
      ((GeneralRDecomposition.measurable_M_R m R).div_const _)]
    congr 1
    funext z
    simp only [Function.comp_apply]
    dsimp [w, s]
    have hw0 : generalRLeadingScale m R ≠ 0 :=
      (generalRLeadingScale_pos h R).ne'
    have hs0 : generalRProxyScale m R ≠ 0 :=
      (generalRProxyScale_pos h R).ne'
    field_simp [hw0, hs0]
  rw [hmap] at hreplace
  have hlead := kolmogorovDistance_M_R_leadingScale_le_rate h R
  unfold generalRScaleMismatchRate
  dsimp [mu, w, s] at hreplace ⊢
  linarith

/-- Complete finite-dimensional Berry--Esseen bound for the actual
standardized sample-correlation log determinant. -/
theorem kolmogorovDistance_ZRmpStatistic_le_finalRateEnvelope
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    kolmogorovDistance
        (Measure.map (ZRmpStatistic m R)
          (standardGaussianDataMeasure m p))
        (gaussianReal 0 1) ≤ generalRFinalRateEnvelope m R := by
  have hfull := kolmogorovDistance_ZRmpStatistic_le_leading_add_cubeRoot h R
  have hlead := kolmogorovDistance_M_R_proxyScale_le h R
  unfold generalRFinalRateEnvelope generalRNonlinearPerturbationRate
  linarith

/-- Sequential general-R CLT obtained by squeezing the actual Kolmogorov
distance with the proved vanishing finite-dimensional envelope. -/
theorem tendsto_kolmogorovDistance_ZRmpStatistic_zero
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦
      kolmogorovDistance
        (Measure.map (ZRmpStatistic (m p) (R p))
          (standardGaussianDataMeasure (m p) p))
        (gaussianReal 0 1)) atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun p ↦
      kolmogorovDistance_nonneg _ _
  · filter_upwards [hadm] with p hp
    exact kolmogorovDistance_ZRmpStatistic_le_finalRateEnvelope hp (R p)
  · exact tendsto_generalRFinalRateEnvelope_zero m R hadm

end

end LogdetLean
