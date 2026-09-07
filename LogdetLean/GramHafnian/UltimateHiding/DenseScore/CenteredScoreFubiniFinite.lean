import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreFubiniLow
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreFubiniFourth
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreFubiniThirdExternal
import Mathlib.Tactic

/-!
# Centered-score Fubini through order four

The former all-orders-up-to-four external interface is reconstructed here by
finite cases.  Orders zero, one, two, and four are the internally proved
Fubini theorems.  The third-order equality is also derived internally, from
the sole remaining product-`L¹` input for the literal third score.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Exact Fubini for every centered density score through order four.  All
five equalities are theorems; the order-three branch rests only on the narrow
product-`L¹` input in `CenteredScoreFubiniThirdExternal`. -/
theorem coeCorner_centeredDensityScore_fubini_external_derived
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    (∫ v : ComplexUnitSphere N,
      ∫ A, event.indicator (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K)
      ∂(complexUnitSphereProbabilityMeasure N)) =
    ∫ A, event.indicator (fun A ↦
      ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore r N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) A
      ∂(concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
          N K) := by
  interval_cases r
  · exact coeCorner_centeredDensityScore_zero_fubini hN (by omega) event hevent
  · exact coeCorner_centeredDensityScore_one_fubini hN hboundary event hevent
  · exact coeCorner_centeredDensityScore_two_fubini hN hboundary event hevent
  · exact
      coeCorner_centeredDensityScore_three_fubini_external_derived
        hN hboundary event hevent
  · exact coeCorner_centeredDensityScore_four_fubini hN hboundary event hevent

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
