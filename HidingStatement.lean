import LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding
import LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison

open MeasureTheory
open LogdetLean.GramHafnian LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison

namespace UniformHiding
noncomputable section

/-- The normalized matrix-law assertion of manuscript Theorem 2.1. -/
def Theorem21 : Prop :=
  ∀ (H : UnitaryHaarProbabilityFamily) (M N K : ℕ),
    1 ≤ N → N ≤ K → K ≤ M →
    probabilityTotalVariationLE
      (normalizedHaarTransposeGramLaw H M N K)
      (normalizedGaussianTransposeGramLaw N K)
      (min 1 (615172 * ultimateSquaredHidingRate M N))

/-- Exact capped hiding remainder, in the probability-TV convention. -/
def deltaOne (M n : ℕ) : ℝ :=
  min 1 (615172 * ultimateSquaredHidingRate M (2 * n))

/-- E1(tau) from Theorem 3.2, with gamma(tau) the actual additive failure. -/
def routeOneBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (deltaP : Ω → ℝ) (r : ℝ) (M K n : ℕ)
    (rho tau : ℝ) : ℝ :=
  min 1 (μ.real (absoluteAdditiveFailureEvent deltaP tau) +
    paperBkn K n * (tau / (rho * gbsGaussianReferenceProbability r M K n)) +
    deltaOne M n)

/-- The infimum is over all nonnegative physical additive thresholds. -/
def optimizedRouteOneBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (deltaP : Ω → ℝ) (r : ℝ) (M K n : ℕ) (rho : ℝ) : ℝ :=
  ⨅ tau : {t : ℝ // 0 ≤ t}, routeOneBound μ deltaP r M K n rho tau

end
end UniformHiding
