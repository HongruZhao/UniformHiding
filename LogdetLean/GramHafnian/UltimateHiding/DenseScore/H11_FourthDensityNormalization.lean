import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_DensityFourthIntegrabilityFromH16
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthSecantIntegralVanishingFromPointwiseFTC
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.QuadraticCenteringFromMass
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import Mathlib.Tactic

/-!
# Fourth density-score normalization for H11

The proved H16 endpoint identifies the fourth derivative of every fixed-
direction event path with the integral of the literal fourth density score.
For the full event the path is identically one, so that integral vanishes.

Together with the direct H16 `L¹` construction, this gives both integrability
and signed normalization before the fourth logarithmic score is known to be
integrable.  This is the acyclic input needed to solve the fourth Bell identity
for H11.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Every positive-order derivative of the full-event centered path vanishes;
the order-four specialization is the normalization used below. -/
theorem concreteCenteredRankOneCOEEventPath_univ_iteratedDeriv_four_eq_zero
    {N K : ℕ} (hNK : N ≤ K) (v : ComplexUnitSphere N) :
    iteratedDeriv 4
        (concreteCenteredRankOneCOEEventPath K v Set.univ) 0 = 0 := by
  have hfun : concreteCenteredRankOneCOEEventPath K v Set.univ =
      fun _ : ℝ ↦ 1 := by
    funext t
    exact concreteCenteredRankOneCOEEventPath_univ_eq_one hNK v t
  rw [hfun]
  simpa using
    (iteratedDeriv_const (n := 4) (c := (1 : ℝ)) (x := (0 : ℝ)))

/-- On the actual scaled COE law, the globally zero-extended H16 score and
the literal fourth density score agree almost everywhere. -/
theorem h16ZeroExtendedConcreteCenteredDensityScore_four_ae_eq_literal_from_A1
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) :
    h16ZeroExtendedConcreteCenteredDensityScore 4 N K v =ᵐ[
      concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K]
      concreteCenteredDensityScore 4 N K v := by
  have hsupport :=
    friedmanMello1985_scaledCOECorner_ae_support_from_density
      hN (by omega : 2 * N ≤ K)
  filter_upwards [hsupport] with A hA
  simp only [h16ZeroExtendedConcreteCenteredDensityScore]
  rw [Set.indicator_of_mem]
  exact hA

/-- The literal fixed-direction fourth density score is integrable using only
approved A1 and the completed H16 coordinate argument. -/
theorem integrable_concreteCenteredDensityScore_four_fixedDirection_literal_from_A1
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) :
    Integrable (concreteCenteredDensityScore 4 N K v)
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  exact (integrable_congr
    (h16ZeroExtendedConcreteCenteredDensityScore_four_ae_eq_literal_from_A1
      hN hboundary v)).mp
    (integrable_concreteCenteredDensityScore_four_fixedDirection_from_A1
      hN hboundary v)

/-- Total-mass normalization: the literal fourth density score has zero
signed integral in every fixed projective direction. -/
theorem integral_concreteCenteredDensityScore_four_fixedDirection_eq_zero_from_A1
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) :
    (∫ A, concreteCenteredDensityScore 4 N K v A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)) = 0 := by
  have hH16 :=
    coeCorner_centeredFixedDirection_eventPath_derivative_H16_proved_from_A1
      (r := 4) hN hboundary (by omega) v Set.univ MeasurableSet.univ
  rw [concreteCenteredRankOneCOEEventPath_univ_iteratedDeriv_four_eq_zero
    (by omega : N ≤ K) v] at hH16
  simpa using hH16.symm

/-- Equivalent zero-extended normalization, convenient for an entirely
global Bell-polynomial statement. -/
theorem integral_h16ZeroExtendedConcreteCenteredDensityScore_four_eq_zero_from_A1
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) :
    (∫ A, h16ZeroExtendedConcreteCenteredDensityScore 4 N K v A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)) = 0 := by
  rw [integral_congr_ae
    (h16ZeroExtendedConcreteCenteredDensityScore_four_ae_eq_literal_from_A1
      hN hboundary v)]
  exact integral_concreteCenteredDensityScore_four_fixedDirection_eq_zero_from_A1
    hN hboundary v

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
