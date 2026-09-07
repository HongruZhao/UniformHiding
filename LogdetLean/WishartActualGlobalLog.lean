import LogdetLean.WishartActualLogCurve
import LogdetLean.NonvanishingCurveLog
import LogdetLean.GeneralRLeadingRateSimplification
import Mathlib.Tactic

/-!
# The global branch-free logarithm of the actual Wishart transform

This module integrates the exact logarithmic derivative constructed in
`WishartActualLogCurve`.  The resulting real-frequency logarithm is global:
its exponential is the actual characteristic transform on every real
frequency, with no principal-log choice.  We also verify the `C^3` certificate
and retain the sharp spectral third-derivative envelope.

The construction is the elementary ODE identity `F' = g F`, `F(0)=1`,
formalized in `NonvanishingCurveLog`.  The identity and population derivative
formulas follow Zhao, arXiv:2608.00565v1, Lemma 5.4; all analytic details used
here are proved in the imported modules.
-/

namespace LogdetLean

noncomputable section

open Complex Filter Set
open scoped BigOperators Topology

private theorem continuous_complexNegPsiTwoSeries_axis
    {x : ℝ} (hx : 0 < x) :
    Continuous (fun u : ℝ ↦
      complexNegPsiTwoSeries ((x : ℂ) + (u : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hout : ContinuousAt complexNegPsiTwoSeries
      ((x : ℂ) + (u : ℂ) * Complex.I) :=
    (analyticOnNhd_complexNegPsiTwoSeries_rightHalfPlane
      ((x : ℂ) + (u : ℂ) * Complex.I)
      (by simpa [complexRightHalfPlane] using hx)).continuousAt
  have hinner : ContinuousAt
      (fun v : ℝ ↦ (x : ℂ) + (v : ℂ) * Complex.I) u := by
    fun_prop
  have hcomp := ContinuousAt.comp
    (f := fun v : ℝ ↦ (x : ℂ) + (v : ℂ) * Complex.I)
    hout hinner
  simpa only [Function.comp_def] using hcomp

private theorem continuous_wishartIdentityLogDerivativeTwo_axis
    {m p : ℕ} (h : Admissible m p) :
    Continuous (fun u : ℝ ↦
      wishartIdentityLogDerivativeTwo m p
        ((u : ℂ) * Complex.I)) := by
  have hM : 0 < betaShapeTotal m := betaShapeTotal_pos h
  unfold wishartIdentityLogDerivativeTwo
  apply Continuous.add
  · apply continuous_finsetSum
    intro j hj
    exact (continuous_complexNegPsiTwoSeries_axis
      (betaShapeA_pos_of_mem_Icc h.2 hj)).neg.add
        (continuous_complexNegPsiTwoSeries_axis hM)
  · apply Continuous.mul
    · fun_prop
    · apply Continuous.add
      · exact (continuous_complexNegPsiTwoSeries_axis hM).neg
      · have hinner : Continuous (fun u : ℝ ↦
            (betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) := by
          fun_prop
        have hnonzero : ∀ u : ℝ,
            (betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
          intro u hzero
          have hre := congrArg Complex.re hzero
          simp at hre
          linarith
        exact (hinner.inv₀ hnonzero).pow 2

private theorem continuous_wishartScalarLogTermThree_axis
    {alpha r : ℝ} (halpha : 0 < alpha) (_hr : 0 < r) :
    Continuous (fun u : ℝ ↦
      wishartScalarLogTermThree alpha r
        ((u : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hden : (alpha : ℂ) + ((u : ℂ) * Complex.I) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hnum : (alpha : ℂ) + (r : ℂ) *
      ((u : ℂ) * Complex.I) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hcast : ContinuousAt (fun v : ℝ ↦ (v : ℂ)) u :=
    Complex.continuous_ofReal.continuousAt
  have him : ContinuousAt (fun v : ℝ ↦ (v : ℂ) * Complex.I) u :=
    hcast.mul continuousAt_const
  have hdenCont : ContinuousAt
      (fun v : ℝ ↦ (alpha : ℂ) + (v : ℂ) * Complex.I) u :=
    continuousAt_const.add him
  have hnumCont : ContinuousAt
      (fun v : ℝ ↦ (alpha : ℂ) + (r : ℂ) *
        ((v : ℂ) * Complex.I)) u :=
    continuousAt_const.add (continuousAt_const.mul him)
  have hdiffTwo : ContinuousAt (fun v : ℝ ↦
      wishartScalarLogDiffTwo alpha r ((v : ℂ) * Complex.I)) u := by
    have hleft : ContinuousAt (fun v : ℝ ↦
        (-((r : ℂ) ^ 2)) *
          (((alpha : ℂ) + (r : ℂ) * ((v : ℂ) * Complex.I))⁻¹) ^ 2) u :=
      ((hnumCont.inv₀ hnum).pow 2).const_mul (-((r : ℂ) ^ 2))
    have hright : ContinuousAt (fun v : ℝ ↦
        (((alpha : ℂ) + (v : ℂ) * Complex.I)⁻¹) ^ 2) u :=
      (hdenCont.inv₀ hden).pow 2
    unfold wishartScalarLogDiffTwo
    convert hleft.add hright using 1
    funext v
    simp only [Pi.add_apply, div_eq_mul_inv, inv_pow, one_mul]
  have hdiffThree : ContinuousAt (fun v : ℝ ↦
      wishartScalarLogDiffThree alpha r ((v : ℂ) * Complex.I)) u := by
    have hleft : ContinuousAt (fun v : ℝ ↦
        (2 * (r : ℂ) ^ 3) *
          (((alpha : ℂ) + (r : ℂ) * ((v : ℂ) * Complex.I))⁻¹) ^ 3) u :=
      ((hnumCont.inv₀ hnum).pow 3).const_mul (2 * (r : ℂ) ^ 3)
    have hright : ContinuousAt (fun v : ℝ ↦
        2 * (((alpha : ℂ) + (v : ℂ) * Complex.I)⁻¹) ^ 3) u :=
      ((hdenCont.inv₀ hden).pow 3).const_mul 2
    unfold wishartScalarLogDiffThree
    convert hleft.sub hright using 1
    funext v
    simp only [Pi.sub_apply, div_eq_mul_inv, inv_pow]
  unfold wishartScalarLogTermThree
  exact ((hdiffTwo.const_mul 3).add
    (hdenCont.mul hdiffThree)).neg

private theorem continuous_wishartPopulationCorrectionThree_axis
    {m p : ℕ} (hm : 0 < m) (R : CorrelationMatrix p) :
    Continuous (fun u : ℝ ↦
      wishartPopulationCorrectionThree R (m : ℝ)
        ((u : ℂ) * Complex.I)) := by
  unfold wishartPopulationCorrectionThree
  apply continuous_finsetSum
  intro i _hi
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  exact continuous_wishartScalarLogTermThree_axis
    (show (0 : ℝ) < (m : ℝ) / 2 by positivity)
    (R.one_add_deviationEigenvalue_pos i)

/-- The actual third real-frequency logarithmic derivative is continuous.
This is the final regularity input needed for the global `C^3` logarithm. -/
theorem continuous_actualWishartFrequencyLogDerivativeTwo
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    Continuous (actualWishartFrequencyLogDerivativeTwo m R) := by
  have hm : 0 < m := by
    have hp := h.1
    have hpm := h.2
    omega
  unfold actualWishartFrequencyLogDerivativeTwo
    actualWishartComplexLogDerivativeTwo
  exact continuous_const.mul
    ((continuous_wishartIdentityLogDerivativeTwo_axis h).add
      (continuous_wishartPopulationCorrectionThree_axis hm R))

/-- The real-frequency logarithmic derivative is twice continuously
differentiable. -/
theorem contDiff_two_actualWishartFrequencyLogDerivative
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    ContDiff ℝ 2 (actualWishartFrequencyLogDerivative m R) := by
  have hdiff0 : Differentiable ℝ
      (actualWishartFrequencyLogDerivative m R) := fun u ↦
    (hasDerivAt_actualWishartFrequencyLogDerivative h R u).differentiableAt
  have hderiv0 : deriv (actualWishartFrequencyLogDerivative m R) =
      actualWishartFrequencyLogDerivativeOne m R := by
    funext u
    exact (hasDerivAt_actualWishartFrequencyLogDerivative h R u).deriv
  have hdiff1 : Differentiable ℝ
      (actualWishartFrequencyLogDerivativeOne m R) := fun u ↦
    (hasDerivAt_actualWishartFrequencyLogDerivativeOne h R u).differentiableAt
  have hderiv1 : deriv (actualWishartFrequencyLogDerivativeOne m R) =
      actualWishartFrequencyLogDerivativeTwo m R := by
    funext u
    exact (hasDerivAt_actualWishartFrequencyLogDerivativeOne h R u).deriv
  have hcont1 : ContDiff ℝ 1
      (actualWishartFrequencyLogDerivativeOne m R) := by
    apply (contDiff_succ_iff_deriv (n := 0)).2
    refine ⟨hdiff1, by simp, ?_⟩
    rw [hderiv1]
    exact (contDiff_zero (𝕜 := ℝ)).2
      (continuous_actualWishartFrequencyLogDerivativeTwo h R)
  apply (contDiff_succ_iff_deriv (n := 1)).2
  exact ⟨hdiff0, by simp, by simpa [hderiv0] using hcont1⟩

/-- Global branch-free additive logarithm of the actual frequency curve. -/
def actualWishartGlobalLog {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) : ℝ → ℂ :=
  curveLogIntegral (actualWishartFrequencyLogDerivative m R)

theorem contDiff_three_actualWishartGlobalLog
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    ContDiff ℝ 3 (actualWishartGlobalLog m R) :=
  contDiff_three_curveLogIntegral
    (contDiff_two_actualWishartFrequencyLogDerivative h R)

/-- The additive logarithm exponentiates to the actual finite transform at
every real frequency. -/
theorem cexp_actualWishartGlobalLog_eq_frequencyCurve
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) (t : ℝ) :
    Complex.exp (actualWishartGlobalLog m R t) =
      actualWishartFrequencyCurve m R t := by
  have hm : 0 < m := by
    have hp := h.1
    have hpm := h.2
    omega
  apply cexp_curveLogIntegral_eq
    (contDiff_two_actualWishartFrequencyLogDerivative h R).continuous
    (hasDerivAt_actualWishartFrequencyCurve hm h.2 R)
  simpa [actualWishartFrequencyCurve] using
    actualWishartComplexTransform_zero hm h.2 R

/-- The second derivative of the actual characteristic-frequency curve at
zero is minus the exact leading variance expression. -/
theorem iteratedDeriv_two_actualWishartFrequencyCurve_zero
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    iteratedDeriv 2 (actualWishartFrequencyCurve m R) 0 =
      ((-generalRLeadingVarianceSq m R : ℝ) : ℂ) := by
  have hm : 0 < m := by
    have hp := h.1
    have hpm := h.2
    omega
  have hderiv : deriv (actualWishartFrequencyCurve m R) =
      fun t ↦ actualWishartFrequencyLogDerivative m R t *
        actualWishartFrequencyCurve m R t := by
    funext t
    exact (hasDerivAt_actualWishartFrequencyCurve hm h.2 R t).deriv
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hderiv]
  have hprod :=
    (hasDerivAt_actualWishartFrequencyLogDerivative h R 0).mul
      (hasDerivAt_actualWishartFrequencyCurve hm h.2 R 0)
  change deriv
      (actualWishartFrequencyLogDerivative m R *
        actualWishartFrequencyCurve m R) 0 =
    ((-generalRLeadingVarianceSq m R : ℝ) : ℂ)
  rw [hprod.deriv]
  simp [actualWishartFrequencyLogDerivative_zero h R,
    actualWishartFrequencyLogDerivativeOne_zero h R,
    actualWishartFrequencyCurve,
    actualWishartComplexTransform_zero hm h.2 R]

@[simp]
theorem actualWishartGlobalLog_zero
    {m p : ℕ} (R : CorrelationMatrix p) :
    actualWishartGlobalLog m R 0 = 0 := by
  simp [actualWishartGlobalLog, curveLogIntegral]

theorem iteratedDeriv_one_actualWishartGlobalLog
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) (t : ℝ) :
    iteratedDeriv 1 (actualWishartGlobalLog m R) t =
      actualWishartFrequencyLogDerivative m R t := by
  rw [iteratedDeriv_one]
  exact (hasDerivAt_curveLogIntegral
    (contDiff_two_actualWishartFrequencyLogDerivative h R).continuous t).deriv

theorem iteratedDeriv_two_actualWishartGlobalLog
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) (t : ℝ) :
    iteratedDeriv 2 (actualWishartGlobalLog m R) t =
      actualWishartFrequencyLogDerivativeOne m R t := by
  rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ,
    funext (iteratedDeriv_one_actualWishartGlobalLog h R)]
  exact (hasDerivAt_actualWishartFrequencyLogDerivative h R t).deriv

theorem iteratedDeriv_three_actualWishartGlobalLog
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) (t : ℝ) :
    iteratedDeriv 3 (actualWishartGlobalLog m R) t =
      actualWishartFrequencyLogDerivativeTwo m R t := by
  rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ,
    funext (iteratedDeriv_two_actualWishartGlobalLog h R)]
  exact (hasDerivAt_actualWishartFrequencyLogDerivativeOne h R t).deriv

theorem norm_iteratedDeriv_three_actualWishartGlobalLog_le_spectral
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) (t : ℝ) :
    ‖iteratedDeriv 3 (actualWishartGlobalLog m R) t‖ ≤
      generalRLeadingThirdEnvelopeSpectral m R := by
  rw [iteratedDeriv_three_actualWishartGlobalLog h R]
  unfold actualWishartFrequencyLogDerivativeTwo
    actualWishartComplexLogDerivativeTwo
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul,
    wishartIdentityLogDerivativeTwo_axis]
  exact norm_wishartLeadingThirdAxis_le_spectral h R t

end

end LogdetLean
