import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeTraceWordHomogeneity
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11H13_ProjectiveFirstReduction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_ExactMomentClosure
import Mathlib.Tactic

/-!
# H13 reduction to one total-degree-four projective contraction

The literal `ell_1 ell_3` product has already been identified with the
derivative-free ledger.  This module connects that exact identity to the
projective-first endpoint and reuses the proved H14/A4 matrix envelope.

Consequently the only premise below is a fixed-matrix sphere integral for the
displayed quartic ledger.  It contains no score derivative, beta-prime law,
matrix-law transport, or endpoint assertion.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL
open U08

/-- The exact irreducible H13 projective calculation after all matrix-path
derivatives have been removed.  The integrand is the literal quartic ledger
proved in `H13_OneThreeTraceWordLedger`; its total degree four is certified in
`H13_OneThreeTraceWordHomogeneity`.

The target is the already-closed H14 radial envelope, whose matrix expectation
is available from the approved low-order beta-prime machinery. -/
def H13OneThreeTraceWordProjectiveContractionContract
    (N K : ℕ) : Prop :=
  ∀ (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)),
    let C := unscaleCOECorner K A
    let Y := concreteCOEY N K A
    let ledger : ComplexUnitSphere N → ℝ := fun v =>
      -8 * concreteCOEExponent N K *
        h13OneThreeTraceWordLedger
          (concreteCenteredOrbitalDirection N v) C Y
    Integrable ledger (higherScoreSphereLaw N) ∧
      (∫ v, ‖ledger v‖ ∂(higherScoreSphereLaw N)) ≤
        h14ProjectiveCancellationEnvelope N K A

/-- The quartic trace-word contraction supplies the generic projective-first
H13 interface with the concrete H14/A4 radial envelope. -/
theorem h13HigherScoreProjectiveFirstEnvelope_of_traceWordContract
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hcontract : H13OneThreeTraceWordProjectiveContractionContract N K) :
    H13HigherScoreProjectiveFirstEnvelope N K
      (h14ProjectiveCancellationEnvelope N K) := by
  refine
    { measurable_score :=
        (measurable_concreteCenteredEll_one hN).mul
          (measurable_concreteCenteredEll_three hN)
      envelope_nonneg := h14ProjectiveCancellationEnvelope_nonneg N K
      fixedMatrix_package := ?_ }
  intro A hsymm hsupport
  let C := unscaleCOECorner K A
  let Y := concreteCOEY N K A
  let ledger : ComplexUnitSphere N → ℝ := fun v =>
    -8 * concreteCOEExponent N K *
      h13OneThreeTraceWordLedger
        (concreteCenteredOrbitalDirection N v) C Y
  have H := Hcontract hN hgap A hsymm hsupport
  dsimp only at H
  have heq : (fun v : ComplexUnitSphere N =>
      concreteCenteredEll 1 N K (A, v) *
        concreteCenteredEll 3 N K (A, v)) = ledger := by
    funext v
    simpa only [ledger, C, Y] using
      concreteCenteredEll_one_mul_three_eq_traceWordLedger_h13_internal
        hN hgap A v hsymm hsupport
  have heq_apply (v : ComplexUnitSphere N) :
      concreteCenteredEll 1 N K (A, v) *
        concreteCenteredEll 3 N K (A, v) = ledger v :=
    congrFun heq v
  constructor
  · simpa only [heq_apply] using H.1
  · simpa only [heq_apply] using H.2

/-- Approved A1--A4 machinery already supplies the matrix-law package for the
same radial envelope.  No H13 statement is used in this construction. -/
theorem h13TraceEnvelopeL1Package_h14_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    HigherScoreTraceEnvelopeL1Package N K
      (h14ProjectiveCancellationEnvelope N K) := by
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
  have H := h14ProjectiveCancellationEnvelope_momentPackage_of_H6_conditional
    hN hgap hH6 hFourth
  exact
    { integrable := H.1
      integral_le := H.2 }

/-- Literal all-dimensional H13 endpoint, reduced to the single explicit
quartic fixed-matrix projective contraction above.  Every probability and
matrix-expectation input is already discharged by approved A1--A4 machinery. -/
theorem centeredLogScore_oneThree_momentPackage_of_traceWordProjective_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hcontract : H13OneThreeTraceWordProjectiveContractionContract N K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) :=
  centeredLogScore_oneThree_momentPackage_of_projectiveFirst
    hN hgap (h14ProjectiveCancellationEnvelope N K)
    (h13HigherScoreProjectiveFirstEnvelope_of_traceWordContract
      hN hgap Hcontract)
    (h13TraceEnvelopeL1Package_h14_A1A2A3A4 hN hgap)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
