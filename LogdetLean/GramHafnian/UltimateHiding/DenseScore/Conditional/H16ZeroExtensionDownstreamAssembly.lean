import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16ScoreJointMeasurability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredTransportL1Interface
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DownstreamCompactL1Inputs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# H16 corrected zero extension supplies the four U07 scientific inputs

This module stays on the moving-support-safe route.  It first transports the
normalized coordinate determinant density as a measure, then represents every
measurable event path by a fixed-set continuous linear functional of the
coordinate `L1` curve.  Thus genuine fixed-direction `C^4` and the exact H16
origin identity follow directly from `COECenteredOrderFourZeroExtensionFacts`.

Together with exact H5, the same family supplies scaled-law support and the
compact-time globally zero-extended score envelope already proved in
`H16ScoreJointMeasurability`.  No pointwise fourth boundary derivative or
fixed ambient pointwise fourth-jet dominator occurs.
-/

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-- The normalized coordinate density after inverse centered pullback. -/
def h16CenteredCoordinateProbabilityWeight
    {N : ℕ} (K : ℕ) (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) : ℝ≥0 :=
  h16COECoordinateProbabilityWeight N K
    (h16CenteredCoordinateFlow v (-t) x)

theorem measurable_h16CenteredCoordinateProbabilityWeight
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (v : ComplexUnitSphere N) (t : ℝ) :
    Measurable (h16CenteredCoordinateProbabilityWeight K v t) :=
  (measurable_h16COECoordinateProbabilityWeight N K).comp
    (W.coordinate_measurePreserving v (-t)).measurable

/-- Coordinate change of variables for the normalized determinant density. -/
theorem h16_map_coordinateProbabilityDensity_centered_of_weakFacts
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (v : ComplexUnitSphere N) (t : ℝ) :
    Measure.map (h16CenteredCoordinateFlow v t)
        ((complexSymmetricCoordinateVolume N).withDensity
          (fun x ↦ (h16COECoordinateProbabilityWeight N K x : ℝ≥0∞))) =
      (complexSymmetricCoordinateVolume N).withDensity
        (fun x ↦
          (h16CenteredCoordinateProbabilityWeight K v t x : ℝ≥0∞)) := by
  convert h16_map_withDensity_inverse_of_map_eq
      (complexSymmetricCoordinateVolume N)
      (h16CenteredCoordinateFlow v t)
      (h16CenteredCoordinateFlow v (-t))
      (W.coordinate_measurePreserving v t).measurable
      (W.coordinate_measurePreserving v (-t)).measurable
      (h16CenteredCoordinateFlow_neg_left v t)
      (W.coordinate_measurePreserving v t).map_eq
      (fun x ↦ (h16COECoordinateProbabilityWeight N K x : ℝ≥0∞))
      (measurable_coe_nnreal_ennreal.comp
        (measurable_h16COECoordinateProbabilityWeight N K)) using 1 <;>
    rfl

/-- The actual centered pushforward law is the scaled embedding of the moving
normalized coordinate density. -/
theorem h16_map_scaledLaw_eq_map_coordinateMovingProbability_of_zeroExtension
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : COECenteredOrderFourZeroExtensionFacts N K hN hboundary)
    (v : ComplexUnitSphere N) (t : ℝ) :
    Measure.map
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      Measure.map (h16ScaledSymmetricCoordinateEmbedding N K)
        ((complexSymmetricCoordinateVolume N).withDensity
          (fun x ↦
            (h16CenteredCoordinateProbabilityWeight K v t x : ℝ≥0∞))) := by
  let W := H.weak
  have hmatrixFlow : Measurable
      (transposeCongruenceFlow
        (concreteCenteredOrbitalDirection N v) t) := by
    unfold transposeCongruenceFlow
    exact measurable_transposeCongruence _
  rw [h16_scaledLaw_eq_map_coordinateProbabilityDensity_of_exactH5
    hH5 hN (by omega : 2 * N ≤ K)]
  rw [Measure.map_map
    hmatrixFlow
    (measurable_h16ScaledSymmetricCoordinateEmbedding N K)]
  have hintertwine :
      transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t ∘
          h16ScaledSymmetricCoordinateEmbedding N K =
        h16ScaledSymmetricCoordinateEmbedding N K ∘
          h16CenteredCoordinateFlow v t := by
    funext x
    exact h16_centeredFlow_scaledCoordinateEmbedding v t x
  rw [hintertwine]
  rw [← Measure.map_map
    (measurable_h16ScaledSymmetricCoordinateEmbedding N K)
    (W.coordinate_measurePreserving v t).measurable]
  rw [h16_map_coordinateProbabilityDensity_centered_of_weakFacts W v t]

/-- Fixed coordinate set corresponding to a measurable matrix event. -/
def h16CenteredCoordinateEvent (N K : ℕ)
    (event : Set (ConcreteMatrixState N)) :
    Set (ComplexSymmetricCoordinates N) :=
  h16ScaledSymmetricCoordinateEmbedding N K ⁻¹' event

theorem measurableSet_h16CenteredCoordinateEvent
    {N K : ℕ} {event : Set (ConcreteMatrixState N)}
    (hevent : MeasurableSet event) :
    MeasurableSet (h16CenteredCoordinateEvent N K event) :=
  hevent.preimage (measurable_h16ScaledSymmetricCoordinateEmbedding N K)

/-- Every event path is a fixed-set integral of the corrected coordinate
`L1` density curve. -/
theorem h16_fixedDirection_eventPath_eq_coordinateSetIntegral
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : COECenteredOrderFourZeroExtensionFacts N K hN hboundary)
    (v : ComplexUnitSphere N) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (t : ℝ) :
    concreteCenteredRankOneCOEEventPath K v event t =
      ∫ x in h16CenteredCoordinateEvent N K event,
        H.jetLp 0 v t x ∂(complexSymmetricCoordinateVolume N) := by
  unfold concreteCenteredRankOneCOEEventPath
  rw [h16_map_scaledLaw_eq_map_coordinateMovingProbability_of_zeroExtension
    hH5 H v t]
  change
    (Measure.map (h16ScaledSymmetricCoordinateEmbedding N K)
      ((complexSymmetricCoordinateVolume N).withDensity
        (fun x ↦
          (h16CenteredCoordinateProbabilityWeight K v t x : ℝ≥0∞)))
      event).toReal = _
  rw [Measure.map_apply
    (measurable_h16ScaledSymmetricCoordinateEmbedding N K) hevent]
  change
    ((complexSymmetricCoordinateVolume N).withDensity
      (fun x ↦
        (h16CenteredCoordinateProbabilityWeight K v t x : ℝ≥0∞))).real
      (h16CenteredCoordinateEvent N K event) = _
  rw [← setIntegral_one_eq_measureReal]
  rw [setIntegral_withDensity_eq_setIntegral_smul
    (measurable_h16CenteredCoordinateProbabilityWeight H.weak v t)
    (fun _ ↦ (1 : ℝ))
    (measurableSet_h16CenteredCoordinateEvent hevent)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (H.jetLp_coeFn_ae 0 v t)] with x hx
  rw [hx, H.weak.density_zero_eq_probabilityDensity v t x]
  simp only [h16CenteredCoordinateProbabilityWeight,
    NNReal.smul_def, h16COECoordinateProbabilityWeight_coe_real,
    smul_eq_mul, mul_one]

/-- The base coordinate jet equals the unextended literal score times the
normalized coordinate density at every point.  Outside open support both
sides vanish; no boundary derivative is asserted. -/
theorem h16CenteredTransportJet_zero_eq_score_mul_probabilityDensity
    {N K : ℕ} (hN : 1 ≤ N) (hK : 0 < K)
    (r : Fin 5) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredTransportJet N K r v 0 x =
      concreteCenteredDensityScore (r : ℕ) N K v
          (h16ScaledSymmetricCoordinateEmbedding N K x) *
        h16COECoordinateProbabilityDensity N K x := by
  by_cases hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)
  · rw [h16CenteredTransportJet_zero_eq_score_mul_density_pointwise
      hN hK r v x hx]
    rw [h16CenteredTransportJet_zero_eq_probabilityDensity
      (N := N) (K := K) v 0 x]
    simp only [neg_zero, h16CenteredCoordinateFlow_zero]
    rw [show h16ZeroExtendedConcreteCenteredDensityScore
        (r : ℕ) N K v (h16ScaledSymmetricCoordinateEmbedding N K x) =
          concreteCenteredDensityScore (r : ℕ) N K v
            (h16ScaledSymmetricCoordinateEmbedding N K x) by
      exact Set.indicator_of_mem
        (h16ScaledEmbedding_mem_openSupport hK x hx) _]
  · have houtside : x ∉ h16CenteredTransportSupport v 0 := by
      simpa [h16CenteredTransportSupport] using hx
    have hrzero := h16CenteredTransportJet_zero_off_support
      (K := K) r v 0 x houtside
    have hzerozero := h16CenteredTransportJet_zero_off_support
      (K := K) (0 : Fin 5) v 0 x houtside
    have hprob := h16CenteredTransportJet_zero_eq_probabilityDensity
      (N := N) (K := K) v 0 x
    simp only [neg_zero, h16CenteredCoordinateFlow_zero] at hprob
    rw [hrzero, ← hprob, hzerozero]
    simp

/-- Coordinate representation of the original H16 score integral. -/
theorem h16_integral_indicator_score_scaledLaw_eq_setIntegral_centeredJet
    (hH5 : H16ExactH5Family)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    (∫ A, event.indicator
        (concreteCenteredDensityScore (r : ℕ) N K v) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) =
      ∫ x in h16CenteredCoordinateEvent N K event,
        h16CenteredTransportJet N K r v 0 x
        ∂(complexSymmetricCoordinateVolume N) := by
  have hK : 0 < K := by omega
  rw [h16_scaledLaw_eq_map_coordinateProbabilityDensity_of_exactH5
    hH5 hN (by omega : 2 * N ≤ K)]
  rw [(measurableEmbedding_h16ScaledSymmetricCoordinateEmbedding hK).integral_map]
  rw [integral_withDensity_eq_integral_smul
    (measurable_h16COECoordinateProbabilityWeight N K)]
  rw [← integral_indicator (measurableSet_h16CenteredCoordinateEvent hevent)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : h16ScaledSymmetricCoordinateEmbedding N K x ∈ event
  · simp only [h16CenteredCoordinateEvent, Set.mem_preimage, hx,
      Set.indicator_of_mem]
    simp only [NNReal.smul_def,
      h16COECoordinateProbabilityWeight_coe_real]
    rw [h16CenteredTransportJet_zero_eq_score_mul_probabilityDensity
      hN hK r v x]
    ring
  · simp [h16CenteredCoordinateEvent, hx]

/-- Corrected zero-extension facts imply the exact fixed-direction H16
identity, with every endpoint quantifier unchanged. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_of_zeroExtension
    (hH5 : H16ExactH5Family)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (H : COECenteredOrderFourZeroExtensionFacts N K hN hboundary)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
  let rf : Fin 5 := ⟨r, by omega⟩
  have hpath : concreteCenteredRankOneCOEEventPath K v event =
      fun t ↦ ∫ x in h16CenteredCoordinateEvent N K event,
        H.jetLp 0 v t x ∂(complexSymmetricCoordinateVolume N) := by
    funext t
    exact h16_fixedDirection_eventPath_eq_coordinateSetIntegral
      hH5 H v event hevent t
  rw [hpath]
  calc
    iteratedDeriv r
        (fun t ↦ ∫ x in h16CenteredCoordinateEvent N K event,
          H.jetLp 0 v t x ∂(complexSymmetricCoordinateVolume N)) 0 =
      ∫ x in h16CenteredCoordinateEvent N K event,
        iteratedDeriv r (fun t ↦ H.jetLp 0 v t) 0 x
        ∂(complexSymmetricCoordinateVolume N) :=
      h16_iteratedDeriv_setIntegral_of_contDiff_L1
        (complexSymmetricCoordinateVolume N)
        (h16CenteredCoordinateEvent N K event)
        (H.densityLp_contDiff_four v) hr 0
    _ = ∫ x in h16CenteredCoordinateEvent N K event,
        H.jetLp rf v 0 x ∂(complexSymmetricCoordinateVolume N) := by
      rw [H.iteratedDeriv_densityLp rf v 0]
    _ = ∫ x in h16CenteredCoordinateEvent N K event,
        h16CenteredTransportJet N K rf v 0 x
        ∂(complexSymmetricCoordinateVolume N) := by
      exact integral_congr_ae
        (ae_restrict_of_ae (H.jetLp_coeFn_ae rf v 0))
    _ = ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
      simpa only [rf] using
        (h16_integral_indicator_score_scaledLaw_eq_setIntegral_centeredJet
          hH5 hN hboundary rf v event hevent).symm

/-- Corrected zero-extension facts also give genuine fixed-direction `C^4`
for every measurable event, independently of totalized derivatives. -/
theorem coeCorner_centeredFixedDirection_eventPath_contDiff_four_of_zeroExtension
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : COECenteredOrderFourZeroExtensionFacts N K hN hboundary)
    (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4 (concreteCenteredRankOneCOEEventPath K v event) := by
  have hpath : concreteCenteredRankOneCOEEventPath K v event =
      fun t ↦ h16SetIntegralL1CLM
        (complexSymmetricCoordinateVolume N)
        (h16CenteredCoordinateEvent N K event) (H.jetLp 0 v t) := by
    funext t
    rw [h16_fixedDirection_eventPath_eq_coordinateSetIntegral
      hH5 H v event hevent t]
    exact (h16SetIntegralL1CLM_apply
      (complexSymmetricCoordinateVolume N)
      (h16CenteredCoordinateEvent N K event) (H.jetLp 0 v t)).symm
  rw [hpath]
  exact (h16SetIntegralL1CLM
    (complexSymmetricCoordinateVolume N)
    (h16CenteredCoordinateEvent N K event)).contDiff.fun_comp
      (H.densityLp_contDiff_four v)

/-- Universally quantified corrected zero-extension family. -/
abbrev H16OrderFourZeroExtensionFamily : Type :=
  ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K),
    COECenteredOrderFourZeroExtensionFacts N K hN hboundary

theorem h16DownstreamFixedDirectionH16_of_zeroExtension
    (hH5 : H16ExactH5Family) (H : H16OrderFourZeroExtensionFamily) :
    H16DownstreamFixedDirectionH16Contract := by
  intro N K r hN hboundary hr v event hevent
  exact coeCorner_centeredFixedDirection_eventPath_derivative_of_zeroExtension
    hH5 hN hboundary hr v (H hN hboundary) event hevent

theorem h16DownstreamFixedDirectionC4_of_zeroExtension
    (hH5 : H16ExactH5Family) (H : H16OrderFourZeroExtensionFamily) :
    H16DownstreamFixedDirectionC4Contract := by
  intro N K hN hboundary v event hevent
  exact coeCorner_centeredFixedDirection_eventPath_contDiff_four_of_zeroExtension
    hH5 (H hN hboundary) v event hevent

/-- The exact four scientific contracts consumed by U07's clean conditional
H17/H18 compact-`L1` assembly. -/
structure H16DownstreamCompactL1ScientificInputs : Prop where
  fixedDirectionH16 : H16DownstreamFixedDirectionH16Contract
  fixedDirectionC4 : H16DownstreamFixedDirectionC4Contract
  scaledCOESupport : H16DownstreamScaledCOESupportContract
  compactZeroExtL1Envelope : H16DownstreamCompactZeroExtL1EnvelopeContract

/-- Exact H5 plus one corrected zero-extension family discharge all four U07
scientific inputs.  This remains CONDITIONAL until that family is constructed
from determinant-specific Gauss--Green data. -/
theorem h16DownstreamCompactL1ScientificInputs_of_zeroExtension_exactH5
    (hH5 : H16ExactH5Family) (H : H16OrderFourZeroExtensionFamily) :
    H16DownstreamCompactL1ScientificInputs where
  fixedDirectionH16 :=
    h16DownstreamFixedDirectionH16_of_zeroExtension hH5 H
  fixedDirectionC4 :=
    h16DownstreamFixedDirectionC4_of_zeroExtension hH5 H
  scaledCOESupport := h16DownstreamScaledCOESupport_of_exactH5 hH5
  compactZeroExtL1Envelope :=
    h16DownstreamCompactZeroExtL1Envelope_of_weakFacts_exactH5 hH5
      (fun hN hboundary ↦ (H hN hboundary).weak)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
