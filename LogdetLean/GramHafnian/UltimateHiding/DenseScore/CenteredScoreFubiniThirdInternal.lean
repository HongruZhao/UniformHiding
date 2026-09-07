import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredCOERawExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16LowerScoreProductIntegrability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthSecantIntegralVanishingFromPointwiseFTC

/-!
# Internal third-score Fubini route

The order-three product integrability premise is discharged by exact H5/A1
and the compact lower-jet envelope.  The only remaining dependencies of the
projective derivative formula are the separately audited fixed-direction and
projective derivative-interchange interfaces.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Exact third-order event-indicator Fubini with no standalone third-score
scientific input. -/
theorem coeCorner_centeredDensityScore_three_fubini_internal
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    (∫ v : ComplexUnitSphere N,
      ∫ A, event.indicator (concreteCenteredDensityScore 3 N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K)
      ∂(complexUnitSphereProbabilityMeasure N)) =
    ∫ A, event.indicator (fun A ↦
      ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 3 N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) A
      ∂(concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
          N K) := by
  exact coeCorner_centeredDensityScore_fubini_of_memLp hN (by omega)
    event hevent (by
      simpa only [concreteCenteredScoreProductLaw] using
        concreteCenteredDensityScoreThreeProduct_memLp_one_internal
          hN hboundary)

/-- The literal projective order-three derivative formula, retaining only
the actual derivative/interchange boundaries and using internal Fubini. -/
theorem coeCorner_centeredProjective_eventPath_derivative_literal_three_internal
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv 3
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 =
      ∫ A, event.indicator (fun A ↦
        ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 3 N K v A
          ∂(complexUnitSphereProbabilityMeasure N)) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) := by
  rw [coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_proved_from_A1
    (r := 3) hN hboundary (by omega) event hevent 0]
  simp_rw [coeCorner_centeredFixedDirection_eventPath_derivative_H16_proved_from_A1
    (r := 3) hN hboundary (by omega) _ event hevent]
  exact coeCorner_centeredDensityScore_three_fubini_internal
    hN hboundary event hevent

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
