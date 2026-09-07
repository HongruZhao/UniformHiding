import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthSecantL1VanishingReduction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H17H18_A1ScientificInputs_Proof

/-!
# H16--H18 from the exact local fourth-secant `L1` limit

This module propagates the scalar, event-free local remainder limit through
the existing direct-`L1` handoff.  All literal H16--H18 quantifiers remain
unchanged.  The limit stays an explicit ordinary premise and is not declared
as an axiom.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Universally quantified form of the exact local `L1` remainder limit. -/
abbrev H16CenteredFourthLocalSecantIntegralVanishingFamily : Prop :=
  ∀ {N K : ℕ} (_hN : 1 ≤ N) (_hboundary : 2 * N + 8 ≤ K),
    H16CenteredFourthLocalSecantIntegralVanishing N K

/-- The local remainder family supplies every direct time-zero derivative
chain. -/
theorem h16CenteredDirectL1DerivativeAtZeroFamily_of_fourthSecantIntegralVanishing_exactH5
    (hH5 : H16ExactH5Family)
    (hvanish : H16CenteredFourthLocalSecantIntegralVanishingFamily) :
    H16CenteredDirectL1DerivativeAtZeroFamily hH5 := by
  intro N K hN hboundary
  exact
    h16CenteredDirectL1DerivativeAtZeroChain_of_secantIntegralVanishing_exactH5
      hH5 hN hboundary (hvanish hN hboundary)

/-- The same local limit supplies the compact-`L1` package consumed by the
checked H17/H18 proofs. -/
theorem h16DownstreamCompactL1ScientificInputs_of_fourthSecantIntegralVanishing_exactH5
    (hH5 : H16ExactH5Family)
    (hvanish : H16CenteredFourthLocalSecantIntegralVanishingFamily) :
    H16DownstreamCompactL1ScientificInputs :=
  h16DownstreamCompactL1ScientificInputs_of_directL1_exactH5 hH5
    (h16CenteredDirectL1DerivativeAtZeroFamily_of_fourthSecantIntegralVanishing_exactH5
      hH5 hvanish)

/-- Literal fixed-direction H16 from exact H5 and the local remainder limit. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_H16_of_fourthSecantIntegralVanishing_exactH5
    (hH5 : H16ExactH5Family)
    (hvanish : H16CenteredFourthLocalSecantIntegralVanishingFamily)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) := by
  exact
    coeCorner_centeredFixedDirection_eventPath_derivative_from_directL1_exactH5
      hH5 hN hboundary hr v
      ((h16CenteredDirectL1DerivativeAtZeroFamily_of_fourthSecantIntegralVanishing_exactH5
        hH5 hvanish) hN hboundary)
      event hevent

/-- Literal projective `C⁴` endpoint H17 from the local remainder limit. -/
theorem coeCorner_centeredProjective_eventPath_contDiff_four_H17_of_fourthSecantIntegralVanishing_exactH5
    (hH5 : H16ExactH5Family)
    (hvanish : H16CenteredFourthLocalSecantIntegralVanishingFamily)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4
      (concreteProjectiveAveragedCenteredCOEEventPath N K event) := by
  let I :=
    h16DownstreamCompactL1ScientificInputs_of_fourthSecantIntegralVanishing_exactH5
      hH5 hvanish
  exact
    coeCorner_centeredProjective_eventPath_contDiff_four_H17_compactL1_support_conditional
      (coeCornerCenteredFixedDirectionH16Contract_of_h16Downstream I)
      (coeCornerCenteredFixedDirectionC4Contract_of_h16Downstream I)
      (coeCornerCenteredScaledCOESupportContract_of_h16Downstream I)
      (coeCornerCenteredCompactZeroExtL1EnvelopeContract_of_h16Downstream I)
      hN hboundary event hevent

/-- Literal derivative-interchange endpoint H18 from the local remainder
limit. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_of_fourthSecantIntegralVanishing_exactH5
    (hH5 : H16ExactH5Family)
    (hvanish : H16CenteredFourthLocalSecantIntegralVanishingFamily)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y =
      ∫ v : ComplexUnitSphere N,
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y
          ∂(complexUnitSphereProbabilityMeasure N) := by
  let I :=
    h16DownstreamCompactL1ScientificInputs_of_fourthSecantIntegralVanishing_exactH5
      hH5 hvanish
  exact
    coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_compactL1_support_conditional
      (coeCornerCenteredFixedDirectionH16Contract_of_h16Downstream I)
      (coeCornerCenteredFixedDirectionC4Contract_of_h16Downstream I)
      (coeCornerCenteredScaledCOESupportContract_of_h16Downstream I)
      (coeCornerCenteredCompactZeroExtL1EnvelopeContract_of_h16Downstream I)
      hN hboundary hr event hevent y

/-! ## Approved-A1 wrappers -/

/-- Literal H16 from approved A1 and the explicit local remainder premise. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_H16_from_A1_fourthSecantIntegralVanishing
    (hvanish : H16CenteredFourthLocalSecantIntegralVanishingFamily)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) :=
  coeCorner_centeredFixedDirection_eventPath_derivative_H16_of_fourthSecantIntegralVanishing_exactH5
    h16ExactH5Family_from_friedmanMello1985_A1 hvanish
      hN hboundary hr v event hevent

/-- Literal H17 from approved A1 and the explicit local remainder premise. -/
theorem coeCorner_centeredProjective_eventPath_contDiff_four_H17_from_A1_fourthSecantIntegralVanishing
    (hvanish : H16CenteredFourthLocalSecantIntegralVanishingFamily)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4
      (concreteProjectiveAveragedCenteredCOEEventPath N K event) :=
  coeCorner_centeredProjective_eventPath_contDiff_four_H17_of_fourthSecantIntegralVanishing_exactH5
    h16ExactH5Family_from_friedmanMello1985_A1 hvanish
      hN hboundary event hevent

/-- Literal H18 from approved A1 and the explicit local remainder premise. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_from_A1_fourthSecantIntegralVanishing
    (hvanish : H16CenteredFourthLocalSecantIntegralVanishingFamily)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y =
      ∫ v : ComplexUnitSphere N,
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y
          ∂(complexUnitSphereProbabilityMeasure N) :=
  coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_of_fourthSecantIntegralVanishing_exactH5
    h16ExactH5Family_from_friedmanMello1985_A1 hvanish
      hN hboundary hr event hevent y

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
