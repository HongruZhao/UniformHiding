import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16ScalarTestTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CoordinateTestSeparation

/-!
# Exact H16 and downstream compact-L1 outputs from corrected weak facts

The cutoff/Gauss--Green layer is represented only by the event-free corrected
weak-facts package.  This module proves the formerly missing scalar-to-
Bochner specialization, the genuine fixed-direction `C^4` curve, the literal
H16 event derivative, and the four inputs consumed by U07.  Exact H5 remains
an explicit upstream parameter.
-/

open MeasureTheory
open scoped ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The corrected weak facts themselves now imply the shifted Bochner
interval chain; no additional analytic or separation premise remains. -/
theorem h16CenteredShiftedBochnerIntervalChain_proved
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary) :
    H16CenteredShiftedBochnerIntervalChain W :=
  h16CenteredShiftedBochnerIntervalChain_of_testPair
    (h16CenteredCoordinateTestPairingSeparates_proved N) W
    (h16CenteredShiftedTestPairIntervalChain_proved W)

/-- `CONDITIONAL`: the literal H16 conclusion, with every original endpoint
quantifier unchanged, follows from exact H5 and one event-free corrected
weak-facts package. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_from_weakFacts_exactH5
    (hH5 : H16ExactH5Family)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K) :=
  coeCorner_centeredFixedDirection_eventPath_derivative_of_bochner
    hH5 hN hboundary hr v W
      (h16CenteredShiftedBochnerIntervalChain_proved W) event hevent

/-- The same corrected weak facts give genuine fixed-direction `C^4` for
every measurable event path, closing the totalized-derivative gap. -/
theorem coeCorner_centeredFixedDirection_eventPath_contDiff_four_from_weakFacts_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4 (concreteCenteredRankOneCOEEventPath K v event) :=
  coeCorner_centeredFixedDirection_eventPath_contDiff_four_of_bochner
    hH5 W (h16CenteredShiftedBochnerIntervalChain_proved W) v event hevent

/-- A universally quantified corrected weak-facts family now discharges
exactly U07's four compact-`L1` scientific inputs. -/
theorem h16DownstreamCompactL1ScientificInputs_from_weakFacts_exactH5
    (hH5 : H16ExactH5Family) (W : H16CenteredWeakFactsFamily) :
    H16DownstreamCompactL1ScientificInputs := by
  apply h16DownstreamCompactL1ScientificInputs_of_bochner_exactH5 hH5 W
  intro N K hN hboundary
  exact h16CenteredShiftedBochnerIntervalChain_proved (W hN hboundary)

/-- The precise determinant-local family still required to instantiate the
corrected weak facts for every admissible dimension. -/
abbrev H16CenteredWeakFactsScientificInputsFamily : Type :=
  ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K),
    H16CenteredWeakFactsScientificInputs N K hN hboundary

/-- `CONDITIONAL`: exact H5 plus the strictly determinant-local scientific
inputs construct the exact literal H16 endpoint. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_from_scientificInputs_exactH5
    (hH5 : H16ExactH5Family)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (H : H16CenteredWeakFactsScientificInputs N K hN hboundary)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K) :=
  coeCorner_centeredFixedDirection_eventPath_derivative_from_weakFacts_exactH5
    hH5 hN hboundary hr v
      (h16CenteredOrderFourWeakGeneratorFacts_of_exactH5 hH5 H)
      event hevent

/-- `CONDITIONAL`: the determinant-local family also supplies all four U07
inputs after the newly proved scalar-to-Bochner transport. -/
theorem h16DownstreamCompactL1ScientificInputs_from_scientificInputs_exactH5
    (hH5 : H16ExactH5Family)
    (H : H16CenteredWeakFactsScientificInputsFamily) :
    H16DownstreamCompactL1ScientificInputs := by
  let W : H16CenteredWeakFactsFamily := fun hN hboundary ↦
    h16CenteredOrderFourWeakGeneratorFacts_of_exactH5 hH5 (H hN hboundary)
  exact h16DownstreamCompactL1ScientificInputs_from_weakFacts_exactH5 hH5 W

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
