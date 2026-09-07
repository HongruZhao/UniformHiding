import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_ExactMomentClosure
import Mathlib.Tactic

/-!
# Numerically sharpened H14 projective-envelope bound

The public fourth-score monomial endpoints deliberately share the extremely
generous constant `denseClassicalMomentConstant ^ 4`.  The proved H14 radial
calculation is far smaller: its lower part costs the explicit H14 lower
constant and its normalized fourth remainder costs only `4096` times the
basic classical moment constant.

This file exposes that already-present arithmetic without changing any public
endpoint.  The stronger number is useful when the four lower Bell terms are
added in the H11 normalization route.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration
open U08

/-- The actual constant produced by the H14 radial proof before it is relaxed
to the common public fourth-moment constant. -/
def h14StrongProjectiveEnvelopeConstant : ℝ :=
  h14BetaPrimeProjectiveLowerMomentConstant +
    4096 * denseClassicalMomentConstant

/-- Strong form of the beta-prime radial calculation already used by H14. -/
theorem h14_betaPrimeProjectiveCancellationEnvelope_momentPackage_strong
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hfourth :
      H14BetaPrimeNormalizedFourthRemainderExpectationContract N K) :
    Integrable (h14BetaPrimeProjectiveCancellationEnvelope N K)
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        (∫ u, h14BetaPrimeProjectiveCancellationEnvelope N K u
          ∂(betaPrimeTraceFourLaw N K)) ≤
          h14StrongProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  have hlower := integrable_h14BetaPrimeProjectiveLowerEnvelope_internal hgap
  have hfourthScaled := Hfourth.integrable.const_mul (4096 : ℝ)
  have hfull :
      Integrable (h14BetaPrimeProjectiveCancellationEnvelope N K)
        (betaPrimeTraceFourLaw N K) := by
    change Integrable (fun u ↦
      h14BetaPrimeProjectiveLowerEnvelope N K u +
        4096 * h14BetaPrimeNormalizedFourthRemainder N K u)
      (betaPrimeTraceFourLaw N K)
    exact hlower.add hfourthScaled
  refine ⟨hfull, ?_⟩
  intro hdense
  have hlowerBound := integral_h14BetaPrimeProjectiveLowerEnvelope_le_internal
    hN hgap hdense
  have hfourthBound := Hfourth.integral_le_dense hdense
  have hscaled := mul_le_mul_of_nonneg_left hfourthBound
    (show (0 : ℝ) ≤ 4096 by norm_num)
  change
    (∫ u, h14BetaPrimeProjectiveLowerEnvelope N K u +
        4096 * h14BetaPrimeNormalizedFourthRemainder N K u
      ∂(betaPrimeTraceFourLaw N K)) ≤
      h14StrongProjectiveEnvelopeConstant * (N : ℝ) ^ 2
  rw [integral_add hlower hfourthScaled, integral_const_mul]
  calc
    (∫ u, h14BetaPrimeProjectiveLowerEnvelope N K u
        ∂(betaPrimeTraceFourLaw N K)) +
        4096 *
          (∫ u, h14BetaPrimeNormalizedFourthRemainder N K u
            ∂(betaPrimeTraceFourLaw N K)) ≤
      h14BetaPrimeProjectiveLowerMomentConstant * (N : ℝ) ^ 2 +
        4096 * (denseClassicalMomentConstant * (N : ℝ) ^ 2) := by
          exact add_le_add hlowerBound hscaled
    _ = h14StrongProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
      unfold h14StrongProjectiveEnvelopeConstant
      ring

/-- Exact H6 transports the sharpened beta-prime estimate to the concrete
scaled-COE matrix law. -/
theorem h14ProjectiveCancellationEnvelope_momentPackage_of_H6_strong
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
          h14StrongProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) :=
    concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K
  let f : ConcreteMatrixState N → Fin 4 → ℝ :=
    concreteCOETracePowerVector 4 N K
  let b : (Fin 4 → ℝ) → ℝ :=
    h14BetaPrimeProjectiveCancellationEnvelope N K
  have hBeta :=
    h14_betaPrimeProjectiveCancellationEnvelope_momentPackage_strong
      hN hgap Hfourth
  have hf : AEMeasurable f μ := by
    simpa only [f, μ] using
      (measurable_concreteCOETracePowerVector_internal 4 N K).aemeasurable
  have hmap : Measure.map f μ = betaPrimeTraceFourLaw N K := by
    simpa only [f, μ] using hH6
  have hbMap : AEStronglyMeasurable b (Measure.map f μ) := by
    rw [hmap]
    simpa only [b] using hBeta.1.aestronglyMeasurable
  have hPullInt : Integrable (b ∘ f) μ := by
    apply (integrable_map_measure hbMap hf).1
    simpa only [hmap, b] using hBeta.1
  have hPullIntegral :
      (∫ A, (b ∘ f) A ∂μ) =
        ∫ u, b u ∂(betaPrimeTraceFourLaw N K) := by
    calc
      (∫ A, (b ∘ f) A ∂μ) = ∫ u, b u ∂(Measure.map f μ) :=
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

/-- Approved A2--A3 transport plus the internal inverse-Wishart recursion
supplies the sharpened concrete envelope with no H11 or H13 input. -/
theorem h14ProjectiveCancellationEnvelope_momentPackage_strong_A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h14ProjectiveCancellationEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h14ProjectiveCancellationEnvelope N K A
            ∂(concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K)) ≤
          h14StrongProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  have hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K := by
    simpa only [betaPrimeTraceFourLaw] using
      (coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
        (r := 4) hN (by omega : 2 * N ≤ K))
  have hFourth :
      H14BetaPrimeNormalizedFourthRemainderExpectationContract N K :=
    h14BetaPrimeNormalizedFourthRemainderExpectationContract_conditional
      hN hgap
      (h14FiniteGaussianFourthWickFormula_internal N K)
      (h14DenominatorFourthTracePolynomialBounds_internal N K)
  exact h14ProjectiveCancellationEnvelope_momentPackage_of_H6_strong
    hN hgap hH6 hFourth

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
