import LogdetLean.GeneralRLeadingRateSimplification
import LogdetLean.GeneralRAnalyticLogSmoothing
import Mathlib.Tactic

/-!
# Vanishing of the complete general-correlation rate envelope

This file is intentionally deterministic.  It does not assume that a
Kolmogorov distance is bounded by the displayed rate.  Instead it packages
the already verified finite-dimensional rate terms and proves that their
sum tends to zero along every eventually admissible dimension array and
every array of positive-definite correlation matrices.

Once the finite Berry--Esseen inequality is proved, the qualitative CLT is
therefore a direct squeeze argument.
-/

namespace LogdetLean

noncomputable section

open Filter

/-- The normalized global third-derivative rate. -/
def generalRThirdDerivativeRate {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  nullLambdaSeries m p + 38 / ((p : ℝ) - 1) +
    8 * generalRSpectralCubicRate m R

/-- The leading normal-approximation cost supplied by the proved generic
analytic-log smoothing theorem.  The smoothing theorem actually contains
`min 1 beta`; replacing it by `beta` gives this simpler upper envelope. -/
def generalRLeadingNormalRate {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  analyticLogNormalApproximationConstant *
    generalRThirdDerivativeRate m R

/-- Cost of replacing the exact leading scale `w_R` by the proxy scale
`s_R`, using the relative squared-scale discrepancy `4/(p-1)`. -/
def generalRScaleMismatchRate (p : ℕ) : ℝ :=
  (4 / ((p : ℝ) - 1)) / Real.sqrt (2 * Real.pi)

/-- Optimized nonlinear-remainder perturbation cost, including Gaussian
anti-concentration. -/
def generalRNonlinearPerturbationRate {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  generalRNonlinearCubeRootRate m R +
    generalRNonlinearCubeRootRate m R / Real.sqrt (2 * Real.pi)

/-- The complete deterministic envelope expected on the right-hand side of
the final general-`R` Berry--Esseen theorem. -/
def generalRFinalRateEnvelope {p : ℕ} (m : ℕ)
    (R : CorrelationMatrix p) : ℝ :=
  generalRLeadingNormalRate m R + generalRScaleMismatchRate p +
    generalRNonlinearPerturbationRate m R

/-- Every fixed numerator divided by `p-1` tends to zero. -/
theorem tendsto_const_div_nat_pred_zero (c : ℝ) :
    Tendsto (fun p : ℕ ↦ c / ((p : ℝ) - 1)) atTop (nhds 0) := by
  have hden : Tendsto (fun p : ℕ ↦ (p : ℝ) - 1) atTop atTop := by
    simpa [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-1 : ℝ)
        tendsto_natCast_atTop_atTop)
  exact tendsto_const_nhds.div_atTop hden

/-- The sharp spectral third-derivative rate vanishes uniformly over
arbitrary correlation-matrix arrays. -/
theorem tendsto_generalRThirdDerivativeRate_zero
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ generalRThirdDerivativeRate (m p) (R p))
      atTop (nhds 0) := by
  have hlambda :=
    tendsto_nullLambdaSeries_zero_of_eventually_admissible m hadm
  have hpred := tendsto_const_div_nat_pred_zero 38
  have hrho := (tendsto_generalRSpectralCubicRate_zero m R hadm).const_mul 8
  unfold generalRThirdDerivativeRate
  simpa using (hlambda.add hpred).add hrho

/-- The leading analytic-log normal-approximation envelope tends to zero. -/
theorem tendsto_generalRLeadingNormalRate_zero
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ generalRLeadingNormalRate (m p) (R p))
      atTop (nhds 0) := by
  have hthird := tendsto_generalRThirdDerivativeRate_zero m R hadm
  unfold generalRLeadingNormalRate
  simpa using hthird.const_mul analyticLogNormalApproximationConstant

/-- The exact-to-proxy scale replacement cost tends to zero. -/
theorem tendsto_generalRScaleMismatchRate_zero :
    Tendsto generalRScaleMismatchRate atTop (nhds 0) := by
  have hpred := tendsto_const_div_nat_pred_zero 4
  unfold generalRScaleMismatchRate
  simpa using hpred.div_const (Real.sqrt (2 * Real.pi))

/-- The nonlinear perturbation and its Gaussian anti-concentration cost
vanish uniformly over arbitrary correlation arrays. -/
theorem tendsto_generalRNonlinearPerturbationRate_zero
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ generalRNonlinearPerturbationRate (m p) (R p))
      atTop (nhds 0) := by
  have hcube := tendsto_generalRNonlinearCubeRootRate_zero m R hadm
  unfold generalRNonlinearPerturbationRate
  simpa using hcube.add (hcube.div_const (Real.sqrt (2 * Real.pi)))

/-- Main qualitative rate statement: the complete proposed finite bound is
`o(1)` for every eventually admissible dimension sequence and every
correlation-matrix array. -/
theorem tendsto_generalRFinalRateEnvelope_zero
    (m : ℕ → ℕ) (R : (p : ℕ) → CorrelationMatrix p)
    (hadm : ∀ᶠ p in atTop, Admissible (m p) p) :
    Tendsto (fun p ↦ generalRFinalRateEnvelope (m p) (R p))
      atTop (nhds 0) := by
  have hleading := tendsto_generalRLeadingNormalRate_zero m R hadm
  have hscale := tendsto_generalRScaleMismatchRate_zero
  have hnonlinear :=
    tendsto_generalRNonlinearPerturbationRate_zero m R hadm
  unfold generalRFinalRateEnvelope
  simpa using (hleading.add hscale).add hnonlinear

end

end LogdetLean
