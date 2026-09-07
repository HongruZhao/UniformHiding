import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreFubini
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16LowerScoreProductIntegrability
import Mathlib.Tactic

/-!
# Exact third-order centered-score Fubini

The literal third centered density score belongs to product `L¹` by the
internally proved compact lower-jet envelope.  The event-indicator Fubini
equality is then an instance of the general internal product-Fubini lemma.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Exact third-order event-indicator Fubini, derived from the internal
product-`L¹` theorem.  The historical name is retained for import stability. -/
theorem coeCorner_centeredDensityScore_three_fubini_external_derived
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    (∫ v : ComplexUnitSphere N,
      ∫ A, event.indicator (concreteCenteredDensityScore 3 N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K)
      ∂(complexUnitSphereProbabilityMeasure N)) =
    ∫ A, event.indicator (fun A ↦
      ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 3 N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) A
      ∂(concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
          N K) := by
  exact coeCorner_centeredDensityScore_fubini_of_memLp hN (by omega)
    event hevent (by
      simpa only [concreteCenteredScoreProductLaw] using
        concreteCenteredDensityScoreThreeProduct_memLp_one_internal hN hboundary)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
