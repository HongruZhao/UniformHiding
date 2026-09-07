import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_RadialBetaPrimeClosureConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteScaledCOECornerProbability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLogScoreOneSquareTwoDerived
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# CONDITIONAL H14 integration through projective cancellation

This module combines the proved centered `ell₂` representation and the
proved fixed-matrix projective cancellation with the radial beta-prime
envelope.  Cancellation is performed before absolute values.  The only
probability inputs are exact H6 trace-law transport, almost-everywhere COE
support, and the explicit normalized fourth-radial remainder contract.

The literal H14 endpoint statement is preserved verbatim as the conclusion;
it is not invoked.  The false raw `O(N²)` trace-two mean majorant is absent.
The fourth-radial contract is a non-endpoint producer intended to be supplied
from the approved Matsumoto A4 atom after its separate paper-variable to
project-variable substitution theorem is available.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

private abbrev h14ProjectiveCancellationMatrixLaw (N K : ℕ) :
    Measure (ConcreteMatrixState N) :=
  concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K

private abbrev h14ProjectiveCancellationSphereLaw (N : ℕ) :
    Measure (ComplexUnitSphere N) :=
  complexUnitSphereProbabilityMeasure N

/-- The positive fixed-matrix cancellation envelope is pointwise
nonnegative. -/
theorem h14ProjectiveCancellationEnvelope_nonneg
    (N K : ℕ) (A : ConcreteMatrixState N) :
    0 ≤ h14ProjectiveCancellationEnvelope N K A := by
  unfold h14ProjectiveCancellationEnvelope
  positivity

/-- **CONDITIONAL, non-endpoint transport.**  Exact H6 transports the
already assembled beta-prime radial package to the literal scaled-COE matrix
law.  The substitution is a separate theorem; no literature atom is stated
in project variables here. -/
theorem h14ProjectiveCancellationEnvelope_momentPackage_of_H6_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K)
    (Hfourth :
      H14BetaPrimeNormalizedFourthRemainderExpectationContract N K) :
    Integrable (h14ProjectiveCancellationEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h14ProjectiveCancellationEnvelope N K A
            ∂(concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K)) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  let mu : Measure (ConcreteMatrixState N) :=
    h14ProjectiveCancellationMatrixLaw N K
  let f : ConcreteMatrixState N → Fin 4 → ℝ :=
    concreteCOETracePowerVector 4 N K
  let b : (Fin 4 → ℝ) → ℝ :=
    h14BetaPrimeProjectiveCancellationEnvelope N K
  have hBeta :=
    h14_betaPrimeProjectiveCancellationEnvelope_momentPackage_conditional
      hN hgap Hfourth
  have hf : AEMeasurable f mu := by
    simpa only [f, mu, h14ProjectiveCancellationMatrixLaw] using
      (measurable_concreteCOETracePowerVector_internal 4 N K).aemeasurable
  have hmap : Measure.map f mu = betaPrimeTraceFourLaw N K := by
    simpa only [f, mu, h14ProjectiveCancellationMatrixLaw] using hH6
  have hbMap : AEStronglyMeasurable b (Measure.map f mu) := by
    rw [hmap]
    simpa only [b] using hBeta.1.aestronglyMeasurable
  have hPullInt : Integrable (b ∘ f) mu := by
    apply (integrable_map_measure hbMap hf).1
    simpa only [hmap, b] using hBeta.1
  have hPullIntegral :
      (∫ A, (b ∘ f) A ∂mu) =
        ∫ u, b u ∂(betaPrimeTraceFourLaw N K) := by
    calc
      (∫ A, (b ∘ f) A ∂mu) =
          ∫ u, b u ∂(Measure.map f mu) :=
        (integral_map hf hbMap).symm
      _ = ∫ u, b u ∂(betaPrimeTraceFourLaw N K) := by rw [hmap]
  have hfun : b ∘ f = h14ProjectiveCancellationEnvelope N K := by
    funext A
    exact h14_betaPrimeProjectiveCancellationEnvelope_comp_traceFour_internal
      N K A
  constructor
  · rw [← hfun]
    exact hPullInt
  · intro hdense
    rw [← hfun, hPullIntegral]
    simpa only [b] using hBeta.2 hdense

/-- **CONDITIONAL exact H14 bridge.**  The conclusion is the unchanged
literal H14 endpoint.  All centered-score algebra, projective fourth-order
cancellation, fixed-matrix integrability, Fubini, H6 pullback, and final
constant arithmetic are internal.  The only unresolved radial input is
`H14BetaPrimeNormalizedFourthRemainderExpectationContract`. -/
theorem centeredLogScore_twoSquare_momentPackage_projectiveCancellation_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K)
    (hSupport : ∀ᵐ A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K),
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A))
    (Hfourth :
      H14BetaPrimeNormalizedFourthRemainderExpectationContract N K) :
    MemLp (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  let mu : Measure (ConcreteMatrixState N) :=
    h14ProjectiveCancellationMatrixLaw N K
  let sphere : Measure (ComplexUnitSphere N) :=
    h14ProjectiveCancellationSphereLaw N
  let f : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 2 N K p ^ 2
  let envelope : ConcreteMatrixState N → ℝ :=
    h14ProjectiveCancellationEnvelope N K
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hfMeas : AEStronglyMeasurable f (mu.prod sphere) := by
    exact (measurable_concreteCenteredEll_two (N := N) (K := K) hN).pow_const 2
      |>.aestronglyMeasurable
  have hSlices : ∀ᵐ A ∂mu,
      Integrable (fun v ↦ f (A, v)) sphere ∧
        (∫ v, ‖f (A, v)‖ ∂sphere) ≤ envelope A := by
    filter_upwards [hSupport] with A hA
    have hPA := h14_fixedMatrix_projectiveCancellation_package_internal
      hN hgap A hA.1 hA.2
    have heq : (fun v ↦ f (A, v)) =
        h14CenteredSandwichSecondSquare N K A := by
      funext v
      simp only [f]
      exact
        concreteCenteredEll_two_square_eq_projectiveSandwichSquare_h14_internal
          hN hgap A v hA.1 hA.2
    have hnormeq : (fun v ↦ ‖f (A, v)‖) =
        fun v ↦ ‖h14CenteredSandwichSecondSquare N K A v‖ := by
      funext v
      exact congrArg norm (congrFun heq v)
    constructor
    · rw [heq]
      exact hPA.1
    · rw [hnormeq]
      simpa only [mu, sphere, envelope,
        h14ProjectiveCancellationMatrixLaw,
        h14ProjectiveCancellationSphereLaw] using hPA.2
  have hEnvelope :=
    h14ProjectiveCancellationEnvelope_momentPackage_of_H6_conditional
      hN hgap hH6 Hfourth
  have hEnvelopeInt : Integrable envelope mu := by
    simpa only [envelope, mu, h14ProjectiveCancellationMatrixLaw] using
      hEnvelope.1
  have hInnerMeas : AEStronglyMeasurable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) mu :=
    hfMeas.norm.integral_prod_right'
  have hInnerInt : Integrable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) mu := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [hSlices] with A hA
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hA.2
    · exact h14ProjectiveCancellationEnvelope_nonneg N K A
  have hfInt : Integrable f (mu.prod sphere) := by
    apply (integrable_prod_iff hfMeas).2
    constructor
    · filter_upwards [hSlices] with A hA
      exact hA.1
    · exact hInnerInt
  constructor
  · have hfMem : MemLp f 1 (mu.prod sphere) :=
      memLp_one_iff_integrable.mpr hfInt
    simpa only [f, mu, sphere, h14ProjectiveCancellationMatrixLaw,
      h14ProjectiveCancellationSphereLaw, concreteCenteredScoreProductLaw]
      using hfMem
  · intro hdense
    have hbound : lpNorm f 1 (mu.prod sphere) ≤
        centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
      calc
        lpNorm f 1 (mu.prod sphere) =
          ∫ A, ∫ v, ‖f (A, v)‖ ∂sphere ∂mu := by
          rw [lpNorm_one_eq_integral_norm hfMeas]
          exact integral_prod (fun p ↦ ‖f p‖) hfInt.norm
        _ ≤ ∫ A, envelope A ∂mu := by
          apply integral_mono_ae hInnerInt hEnvelopeInt
          filter_upwards [hSlices] with A hA
          exact hA.2
        _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
          simpa only [envelope, mu, h14ProjectiveCancellationMatrixLaw] using
            hEnvelope.2 hdense
    simpa only [f, mu, sphere, h14ProjectiveCancellationMatrixLaw,
      h14ProjectiveCancellationSphereLaw, concreteCenteredScoreProductLaw]
      using hbound

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
