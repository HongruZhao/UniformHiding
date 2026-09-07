import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic
import LogdetLean.ComplexExponentialPerturbation
import LogdetLean.FejerSmoothingFourier
import LogdetLean.GaussianAntiConcentration

/-!
# Normal approximation from a globally controlled logarithmic characteristic function

This module formalizes Appendix Lemma 3 in the general-correlation proof
audit.  It is deliberately split into two reusable layers.

* `norm_logRemainder_le_of_contDiff_three` is the calculus layer.  A global
  `C^3` bound and the three normalizing values at zero give a cubic Taylor
  remainder.  The factor `1/2` is the (slightly coarse) vector-valued Taylor
  bound used by Mathlib; the classical integral remainder would improve it
  to `1/6`, but no rate or application changes.
* `kolmogorovDistance_gaussian_le_analyticLogConstant_mul_min` is the
  probability layer.  It exponentiates the cubic remainder, integrates the
  resulting Gaussian-damped Esseen quotient, and invokes the proved
  Fejer--Esseen inequality.

The smoothing mechanism follows Feller, *An Introduction to Probability
Theory and Its Applications*, Vol. II, 2nd ed. (1971), Lemma XVI.3.1,
p. 537.  The actual formal theorem used here is the from-scratch Fejer
version `kolmogorovDistance_le_fejer_esseen`, whose constants are coarser
than Feller's optimized kernel constants.
-/

namespace LogdetLean

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Real Interval

noncomputable section

/-- The logarithmic error after subtracting the standardized Gaussian
quadratic exponent. -/
def gaussianLogRemainder (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  h t + ((t ^ 2 / 2 : ℝ) : ℂ)

/-- The integrable envelope that appears after division by the Fourier
frequency in Esseen's integral. -/
def analyticLogGaussianEnvelope (t : ℝ) : ℝ :=
  |t| ^ 2 * Real.exp (-(t ^ 2 / 3))

/-- A fully explicit universal constant for the analytic-log normal
approximation theorem.  We retain the elementary Gaussian integral in its
integral form; only its finiteness and nonnegativity are used. -/
def analyticLogNormalApproximationConstant : ℝ :=
  1 + (1 / (2 * Real.pi)) *
      (∫ t : ℝ, analyticLogGaussianEnvelope t) +
    192 * Real.pi / Real.sqrt (2 * Real.pi)

theorem integrable_analyticLogGaussianEnvelope :
    Integrable analyticLogGaussianEnvelope := by
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (b := (1 / 3 : ℝ)) (by norm_num) (s := (2 : ℝ)) (by norm_num)
  refine h.norm.congr (Filter.Eventually.of_forall fun t ↦ ?_)
  simp only [analyticLogGaussianEnvelope, Real.rpow_ofNat]
  rw [norm_mul, norm_pow, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  congr 2
  ring_nf

theorem analyticLogGaussianEnvelope_nonneg (t : ℝ) :
    0 ≤ analyticLogGaussianEnvelope t := by
  unfold analyticLogGaussianEnvelope
  positivity

theorem integral_analyticLogGaussianEnvelope_nonneg :
    0 ≤ ∫ t : ℝ, analyticLogGaussianEnvelope t :=
  integral_nonneg analyticLogGaussianEnvelope_nonneg

theorem analyticLogNormalApproximationConstant_ge_one :
    1 ≤ analyticLogNormalApproximationConstant := by
  unfold analyticLogNormalApproximationConstant
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hI := integral_analyticLogGaussianEnvelope_nonneg
  have hfirst : 0 ≤ (1 / (2 * Real.pi)) *
      (∫ t : ℝ, analyticLogGaussianEnvelope t) := by positivity
  have hsecond : 0 ≤ 192 * Real.pi / Real.sqrt (2 * Real.pi) := by
    positivity
  linarith

/-- The standard-normal CDF has the global density Lipschitz constant
`1 / sqrt (2*pi)`. -/
theorem standardGaussian_cdf_hasRealLipschitzBound :
    HasRealLipschitzBound (cdf (gaussianReal 0 1))
      (1 / Real.sqrt (2 * Real.pi)) := by
  intro x y
  wlog hxy : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x y]
    exact this y x (le_of_not_ge hxy)
  have hmono : cdf (gaussianReal 0 1) x ≤ cdf (gaussianReal 0 1) y :=
    monotone_cdf _ hxy
  have hinc := standardGaussian_cdf_increment_le x (y - x) (sub_nonneg.mpr hxy)
  rw [show x + (y - x) = y by ring_nf] at hinc
  rw [abs_of_nonpos (sub_nonpos.mpr hmono), abs_of_nonpos (sub_nonpos.mpr hxy)]
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hinc

/-- An exact cubic logarithmic remainder gives the Gaussian-damped local
characteristic-function estimate used in the smoothing proof. -/
theorem norm_charFun_sub_standardGaussian_le_of_logRemainder
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (h : ℝ → ℂ) {beta t : ℝ}
    (hcf : ∀ u, charFun mu u = Complex.exp (h u))
    (hrem : ∀ u, ‖gaussianLogRemainder h u‖ ≤ beta * |u| ^ 3 / 2)
    (hlocal : beta * |t| ≤ 1 / 3) (hbeta : 0 ≤ beta) :
    ‖charFun mu t - charFun (gaussianReal 0 1) t‖ ≤
      (beta * |t| ^ 3 / 2) * Real.exp (-(t ^ 2) / 3) := by
  let r : ℂ := gaussianLogRemainder h t
  have hr0 : 0 ≤ beta * |t| ^ 3 / 2 := by positivity
  have hr : ‖r‖ ≤ beta * |t| ^ 3 / 2 := hrem t
  have htSq : |t| ^ 2 = t ^ 2 := sq_abs t
  have hsmall : beta * |t| ^ 3 / 2 ≤ t ^ 2 / 6 := by
    rw [show |t| ^ 3 = |t| ^ 2 * |t| by ring_nf, htSq]
    nlinarith [sq_nonneg t]
  have hrSmall : ‖r‖ ≤ t ^ 2 / 6 := hr.trans hsmall
  have hhexp : h t = (((-(t ^ 2 / 2) : ℝ) : ℂ) + r) := by
    dsimp [r, gaussianLogRemainder]
    push_cast
    ring_nf
  have hgauss : charFun (gaussianReal 0 1) t =
      Complex.exp (((-(t ^ 2 / 2) : ℝ) : ℂ)) := by
    rw [charFun_gaussianReal]
    congr 1
    norm_num
  rw [hcf, hgauss]
  rw [hhexp]
  have hpert := norm_cexp_gaussian_add_sub_gaussian_le t r hrSmall
  exact hpert.trans (mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le)

/-- The Esseen quotient is dominated on the natural analytic-log cutoff by
`(beta/2) * |t|^2 exp(-t^2/3)`. -/
theorem fourierQuotientError_standardGaussian_le_of_logRemainder
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (h : ℝ → ℂ) {beta t : ℝ}
    (hcf : ∀ u, charFun mu u = Complex.exp (h u))
    (hrem : ∀ u, ‖gaussianLogRemainder h u‖ ≤ beta * |u| ^ 3 / 2)
    (hbeta : 0 ≤ beta) (hlocal : beta * |t| ≤ 1 / 3) :
    fourierQuotientError (charFun mu)
        (charFun (gaussianReal 0 1)) t ≤
      (beta / 2) * analyticLogGaussianEnvelope t := by
  by_cases ht : t = 0
  · subst t
    simp [fourierQuotientError, analyticLogGaussianEnvelope]
  · have habs : 0 < |t| := abs_pos.mpr ht
    have hpoint := norm_charFun_sub_standardGaussian_le_of_logRemainder
      mu h hcf hrem hlocal hbeta
    unfold fourierQuotientError analyticLogGaussianEnvelope
    rw [div_le_iff₀ habs]
    calc
      ‖charFun mu t - charFun (gaussianReal 0 1) t‖ ≤
          (beta * |t| ^ 3 / 2) * Real.exp (-(t ^ 2) / 3) := hpoint
      _ = ((beta / 2) * (|t| ^ 2 * Real.exp (-(t ^ 2 / 3)))) * |t| := by
        ring_nf

/-- Integrability of the local Esseen quotient follows from the explicit
Gaussian envelope, rather than being left as an assumption. -/
theorem integrableOn_fourierQuotientError_standardGaussian_of_logRemainder
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (h : ℝ → ℂ) {beta S : ℝ}
    (hcf : ∀ u, charFun mu u = Complex.exp (h u))
    (hrem : ∀ u, ‖gaussianLogRemainder h u‖ ≤ beta * |u| ^ 3 / 2)
    (hbeta : 0 ≤ beta) (_hS : 0 ≤ S)
    (hscale : beta * S ≤ 1 / 3) :
    IntegrableOn
      (fourierQuotientError (charFun mu)
        (charFun (gaussianReal 0 1))) (Icc (-S) S) := by
  have hmeas : AEStronglyMeasurable
      (fourierQuotientError (charFun mu)
        (charFun (gaussianReal 0 1))) := by
    have hcontMu : Continuous (charFun mu) := continuous_charFun
    have hcontGaussian : Continuous (charFun (gaussianReal 0 1)) :=
      continuous_charFun
    unfold fourierQuotientError
    exact ((hcontMu.sub hcontGaussian).norm.measurable.div
      continuous_abs.measurable).aestronglyMeasurable
  have hmajor : Integrable (fun t ↦
      (beta / 2) * analyticLogGaussianEnvelope t) :=
    integrable_analyticLogGaussianEnvelope.const_mul (beta / 2)
  apply hmajor.integrableOn.mono' hmeas.restrict
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [Real.norm_eq_abs,
    abs_of_nonneg (fourierQuotientError_nonneg _ _ t)]
  apply fourierQuotientError_standardGaussian_le_of_logRemainder
    mu h hcf hrem hbeta
  have habs : |t| ≤ S := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  exact (mul_le_mul_of_nonneg_left habs hbeta).trans hscale

/-- Integrated form of the preceding pointwise Gaussian envelope. -/
theorem truncatedCharFunDiscrepancy_standardGaussian_le_of_logRemainder
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (h : ℝ → ℂ) {beta S : ℝ}
    (hcf : ∀ u, charFun mu u = Complex.exp (h u))
    (hrem : ∀ u, ‖gaussianLogRemainder h u‖ ≤ beta * |u| ^ 3 / 2)
    (hbeta : 0 ≤ beta) (hS : 0 ≤ S)
    (hscale : beta * S ≤ 1 / 3) :
    truncatedCharFunDiscrepancy mu (gaussianReal 0 1) S ≤
      (beta / 2) * (∫ t : ℝ, analyticLogGaussianEnvelope t) := by
  have hquot := integrableOn_fourierQuotientError_standardGaussian_of_logRemainder
    mu h hcf hrem hbeta hS hscale
  have hmajor : Integrable (fun t ↦
      (beta / 2) * analyticLogGaussianEnvelope t) :=
    integrable_analyticLogGaussianEnvelope.const_mul (beta / 2)
  unfold truncatedCharFunDiscrepancy truncatedFourierDiscrepancy
  calc
    (∫ t in Icc (-S) S,
        fourierQuotientError (charFun mu)
          (charFun (gaussianReal 0 1)) t) ≤
        ∫ t in Icc (-S) S,
          (beta / 2) * analyticLogGaussianEnvelope t := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun t ↦
          fourierQuotientError_nonneg _ _ t
      · exact hmajor.integrableOn
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        apply fourierQuotientError_standardGaussian_le_of_logRemainder
          mu h hcf hrem hbeta
        have habs : |t| ≤ S := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
        exact (mul_le_mul_of_nonneg_left habs hbeta).trans hscale
    _ ≤ ∫ t : ℝ, (beta / 2) * analyticLogGaussianEnvelope t :=
      MeasureTheory.integral_mono_measure
        (Measure.restrict_le_self)
        (Filter.Eventually.of_forall fun t ↦ by
          exact mul_nonneg (by positivity) (analyticLogGaussianEnvelope_nonneg t))
        hmajor
    _ = (beta / 2) *
        (∫ t : ℝ, analyticLogGaussianEnvelope t) := by
      rw [integral_const_mul]

/-- The standard Gaussian has an integrable first absolute moment. -/
theorem integrable_id_standardGaussian :
    Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) := by
  change Integrable id (gaussianReal 0 1)
  exact (memLp_id_gaussianReal' (1 : ENNReal) (by simp)).integrable (by norm_num)

/-- Reusable analytic-log normal approximation theorem.  The logarithmic
remainder hypothesis is exact and is discharged from a global `C^3` bound by
`norm_logRemainder_le_of_contDiff_three` below.

The conclusion includes `beta = 0`: then the characteristic function is
exactly Gaussian, so uniqueness of characteristic functions gives equality
of the two laws. -/
theorem kolmogorovDistance_gaussian_le_analyticLogConstant_mul_min
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : Integrable (fun x : ℝ ↦ x) mu)
    (h : ℝ → ℂ) {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (hcf : ∀ t, charFun mu t = Complex.exp (h t))
    (hrem : ∀ t, ‖gaussianLogRemainder h t‖ ≤ beta * |t| ^ 3 / 2) :
    kolmogorovDistance mu (gaussianReal 0 1) ≤
      analyticLogNormalApproximationConstant * min 1 beta := by
  by_cases hb0 : beta = 0
  · have hchar : charFun mu = charFun (gaussianReal 0 1) := by
      funext t
      have hr0 : gaussianLogRemainder h t = 0 := by
        apply norm_eq_zero.mp
        have hr := hrem t
        have hrle : ‖gaussianLogRemainder h t‖ ≤ 0 := by
          simpa [hb0] using hr
        exact le_antisymm hrle (norm_nonneg _)
      have hhexp : h t = (((-(t ^ 2 / 2) : ℝ) : ℂ)) := by
        have hr0' : h t + ((t ^ 2 / 2 : ℝ) : ℂ) = 0 := by
          simpa [gaussianLogRemainder] using hr0
        calc
          h t = -((t ^ 2 / 2 : ℝ) : ℂ) :=
            eq_neg_of_add_eq_zero_left hr0'
          _ = (((-(t ^ 2 / 2) : ℝ) : ℂ)) := by push_cast; rfl
      rw [hcf, charFun_gaussianReal, hhexp]
      simp
    have hmeasure : mu = gaussianReal 0 1 := Measure.ext_of_charFun hchar
    rw [hmeasure, hb0]
    rw [min_eq_right (by norm_num : (0 : ℝ) ≤ 1), mul_zero]
    unfold kolmogorovDistance
    exact supDistance_le_of_bound (fun x ↦ by simp)
  · have hbpos : 0 < beta := lt_of_le_of_ne hbeta (Ne.symm hb0)
    by_cases hb1 : 1 ≤ beta
    · have hC := analyticLogNormalApproximationConstant_ge_one
      rw [min_eq_left hb1]
      exact (kolmogorovDistance_le_one mu (gaussianReal 0 1)).trans (by
        simpa using hC)
    · have hbsmall : beta < 1 := lt_of_not_ge hb1
      let S : ℝ := 1 / (3 * beta)
      have hS : 0 < S := by dsimp [S]; positivity
      have hscale : beta * S ≤ 1 / 3 := by
        dsimp [S]
        field_simp [ne_of_gt hbpos]
        norm_num
      have hint :=
        integrableOn_fourierQuotientError_standardGaussian_of_logRemainder
          mu h hcf hrem hbeta hS.le hscale
      have hfourier :=
        truncatedCharFunDiscrepancy_standardGaussian_le_of_logRemainder
          mu h hcf hrem hbeta hS.le hscale
      have hsmooth := kolmogorovDistance_le_fejer_esseen
        mu (gaussianReal 0 1) hmu integrable_id_standardGaussian
        hS (by positivity) standardGaussian_cdf_hasRealLipschitzBound hint
      rw [min_eq_right hbsmall.le]
      calc
        kolmogorovDistance mu (gaussianReal 0 1) ≤
            (1 / Real.pi) *
                truncatedCharFunDiscrepancy mu (gaussianReal 0 1) S +
              64 * Real.pi * (1 / Real.sqrt (2 * Real.pi)) / S := hsmooth
        _ ≤ (1 / Real.pi) *
              ((beta / 2) *
                (∫ t : ℝ, analyticLogGaussianEnvelope t)) +
              64 * Real.pi * (1 / Real.sqrt (2 * Real.pi)) / S := by
            gcongr
        _ = beta * ((1 / (2 * Real.pi)) *
                (∫ t : ℝ, analyticLogGaussianEnvelope t) +
              192 * Real.pi / Real.sqrt (2 * Real.pi)) := by
            dsimp [S]
            field_simp [ne_of_gt hbpos, ne_of_gt Real.pi_pos,
              ne_of_gt (show 0 < Real.sqrt (2 * Real.pi) by positivity)]
            ring_nf
        _ ≤ analyticLogNormalApproximationConstant * beta := by
            unfold analyticLogNormalApproximationConstant
            have hI := integral_analyticLogGaussianEnvelope_nonneg
            have hpi : 0 < Real.pi := Real.pi_pos
            have hsqrt : 0 < Real.sqrt (2 * Real.pi) := by positivity
            nlinarith

/-! ## The calculus certificate -/

/-- A global third-derivative bound gives a cubic remainder around zero.

We use Mathlib's vector-valued Taylor remainder estimate.  Its elementary
constant is `1/2`; this is three times the optimal integral-remainder
constant `1/6`, and is the reason for choosing cutoff `1/(3*beta)` above.
-/
theorem norm_logRemainder_le_of_contDiff_three
    (h : ℝ → ℂ) {beta : ℝ}
    (hsmooth : ContDiff ℝ 3 h)
    (hzero : h 0 = 0)
    (hfirst : iteratedDeriv 1 h 0 = 0)
    (hsecond : iteratedDeriv 2 h 0 = -1)
    (hthird : ∀ t, ‖iteratedDeriv 3 h t‖ ≤ beta) :
    ∀ t, ‖gaussianLogRemainder h t‖ ≤ beta * |t| ^ 3 / 2 := by
  intro t
  by_cases ht : t = 0
  · subst t
    simp [gaussianLogRemainder, hzero]
  · let J : Set ℝ := uIcc 0 t
    have hJ : J = uIcc 0 t := rfl
    have huniq : UniqueDiffOn ℝ J := by
      rw [hJ]
      exact uniqueDiffOn_uIcc (Ne.symm ht)
    have hzeroJ : (0 : ℝ) ∈ J := by
      rw [hJ]
      exact left_mem_uIcc
    have hcont0 : ContDiffAt ℝ 0 h 0 := hsmooth.contDiffAt.of_le (by norm_num)
    have hcont1 : ContDiffAt ℝ 1 h 0 := hsmooth.contDiffAt.of_le (by norm_num)
    have hcont2 : ContDiffAt ℝ 2 h 0 := hsmooth.contDiffAt.of_le (by norm_num)
    have hwithin0 : iteratedDerivWithin 0 h J 0 = iteratedDeriv 0 h 0 :=
      iteratedDerivWithin_eq_iteratedDeriv huniq hcont0 hzeroJ
    have hwithin1 : iteratedDerivWithin 1 h J 0 = iteratedDeriv 1 h 0 :=
      iteratedDerivWithin_eq_iteratedDeriv huniq hcont1 hzeroJ
    have hwithin2 : iteratedDerivWithin 2 h J 0 = iteratedDeriv 2 h 0 :=
      iteratedDerivWithin_eq_iteratedDeriv huniq hcont2 hzeroJ
    have hpoly : taylorWithinEval h 2 J 0 t =
        (((-(t ^ 2 / 2) : ℝ) : ℂ)) := by
      rw [taylor_within_apply]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero,
        hwithin0, hwithin1, hwithin2, hfirst, hsecond]
      rw [iteratedDeriv_zero]
      rw [hzero]
      norm_num
      ring_nf
    have hTaylor :
        h t - taylorWithinEval h 2 J 0 t =
          ∫ x in (0 : ℝ)..t,
            ((t - x) ^ 2 / 2 : ℝ) • iteratedDerivWithin 3 h J x := by
      simpa [J] using
        (taylor_integral_remainder (f := h) (x := t) (x₀ := 0) (n := 2)
          hsmooth.contDiffOn)
    let f : ℝ → ℂ := fun x ↦
      ((t - x) ^ 2 / 2 : ℝ) • iteratedDerivWithin 3 h J x
    have hremEq : gaussianLogRemainder h t = ∫ x in (0 : ℝ)..t, f x := by
      dsimp only [f]
      rw [hpoly] at hTaylor
      have hneg : (((-(t ^ 2 / 2) : ℝ) : ℂ)) =
          -((t ^ 2 / 2 : ℝ) : ℂ) := by push_cast; ring_nf
      rw [hneg, sub_neg_eq_add] at hTaylor
      simpa [gaussianLogRemainder] using hTaylor
    have hbeta : 0 ≤ beta :=
      (norm_nonneg (iteratedDeriv 3 h 0)).trans (hthird 0)
    have hbound : ∀ x ∈ Ι (0 : ℝ) t,
        ‖f x‖ ≤ (beta * t ^ 2 / 2) := by
      intro x hx
      have hxJ : x ∈ J := by
        rw [hJ]
        exact uIoc_subset_uIcc hx
      have hcont3 : ContDiffAt ℝ 3 h x := hsmooth.contDiffAt
      have hwithin3 : iteratedDerivWithin 3 h J x = iteratedDeriv 3 h x :=
        iteratedDerivWithin_eq_iteratedDeriv huniq hcont3 hxJ
      have hdist : |t - x| ≤ |t| := by
        simpa using abs_sub_right_of_mem_uIcc (uIoc_subset_uIcc hx)
      have hsq : (t - x) ^ 2 ≤ t ^ 2 := by
        rw [← sq_abs (t - x), ← sq_abs t]
        exact pow_le_pow_left₀ (abs_nonneg (t - x)) hdist 2
      dsimp only [f]
      rw [hwithin3, norm_smul, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : 0 ≤ (t - x) ^ 2 / 2)]
      calc
        ((t - x) ^ 2 / 2) * ‖iteratedDeriv 3 h x‖ ≤
            ((t - x) ^ 2 / 2) * beta := by
          gcongr
          exact hthird x
        _ ≤ (t ^ 2 / 2) * beta := by gcongr
        _ = beta * t ^ 2 / 2 := by ring_nf
    rw [hremEq]
    calc
      ‖∫ x in (0 : ℝ)..t, f x‖ ≤
          (beta * t ^ 2 / 2) * |t - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ = beta * |t| ^ 3 / 2 := by
        rw [sub_zero, ← sq_abs t]
        ring_nf

/-- User-facing `C^3` form of Appendix Lemma 3. -/
theorem kolmogorovDistance_gaussian_le_of_contDiff_log
    (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : Integrable (fun x : ℝ ↦ x) mu)
    (h : ℝ → ℂ) {beta : ℝ}
    (hbeta : 0 ≤ beta)
    (hcf : ∀ t, charFun mu t = Complex.exp (h t))
    (hsmooth : ContDiff ℝ 3 h)
    (hzero : h 0 = 0)
    (hfirst : iteratedDeriv 1 h 0 = 0)
    (hsecond : iteratedDeriv 2 h 0 = -1)
    (hthird : ∀ t, ‖iteratedDeriv 3 h t‖ ≤ beta) :
    kolmogorovDistance mu (gaussianReal 0 1) ≤
      analyticLogNormalApproximationConstant * min 1 beta := by
  apply kolmogorovDistance_gaussian_le_analyticLogConstant_mul_min
    mu hmu h hbeta hcf
  exact norm_logRemainder_le_of_contDiff_three
    h hsmooth hzero hfirst hsecond hthird

end

end LogdetLean
