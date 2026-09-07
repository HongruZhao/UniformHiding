import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_FiniteGaussianFourthWickFormulaClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_FourthRadialProducerConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_DenominatorFourthTraceContraction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_CenteredEllTwoRadialIntegrationConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A2Prime_A1TraceTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import Mathlib.Tactic

/-!
# Exact H14 centered-second-score moment closure

The finite 105-pairing Gaussian Wick contraction and the denominator trace
bounds are now internal.  Exact H6 transports the resulting radial estimate
to the scaled COE corner, while approved A1 supplies its almost-everywhere
matrix-ball support.  This proves the unchanged literal H14 moment package
from the already approved A1--A3 boundary.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL
open U08

/-- Literal H14 endpoint, proved from approved A1--A3 and Lean foundations. -/
theorem centeredLogScore_twoSquare_momentPackage_proved_A1A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K := by
    simpa only [betaPrimeTraceFourLaw] using
      (coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
        (r := 4) hN (by omega : 2 * N ≤ K))
  have hSupport : ∀ᵐ A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K),
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) :=
    friedmanMello1985_scaledCOECorner_ae_support_from_density
      hN (by omega : 2 * N ≤ K)
  have hFourth :
      H14BetaPrimeNormalizedFourthRemainderExpectationContract N K :=
    h14BetaPrimeNormalizedFourthRemainderExpectationContract_conditional
      hN hgap
      (h14FiniteGaussianFourthWickFormula_internal N K)
      (h14DenominatorFourthTracePolynomialBounds_internal N K)
  exact centeredLogScore_twoSquare_momentPackage_projectiveCancellation_conditional
    hN hgap hH6 hSupport hFourth

theorem centeredLogScore_twoSquare_memLp_one_proved_A1A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
      (concreteCenteredScoreProductLaw N K) :=
  (centeredLogScore_twoSquare_momentPackage_proved_A1A2A3 hN hgap).1

theorem centeredLogScore_twoSquare_lpNorm_one_le_proved_A1A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
        (concreteCenteredScoreProductLaw N K) ≤
      centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 :=
  (centeredLogScore_twoSquare_momentPackage_proved_A1A2A3
    hN (by omega)).2 hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
