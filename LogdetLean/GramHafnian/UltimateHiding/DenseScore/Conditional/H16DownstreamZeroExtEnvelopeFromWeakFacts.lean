import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DownstreamCompactL1Inputs
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16ScaledScoreL1FromWeakFacts
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFlowGeometry
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# U07's compact zero-extension envelope from corrected weak facts

This module mirrors the event-free content of U07's compact-`L1` contract,
using U06-prefixed names so the two independently developed modules can be
imported together.  The theorem proves all event restriction, product-`L1`,
section-`L1`, and common direction-envelope conclusions.  Its only extra
input beyond exact H5 and the corrected weak facts is joint a.e. strong
measurability of the literal zero-extended score on matrix-direction space.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

def h16DownstreamConcreteCenteredZeroExtShiftedEvent
    (N : ℕ) (t : ℝ) (event : Set (ConcreteMatrixState N)) :
    Set (ConcreteMatrixState N × ComplexUnitSphere N) :=
  {Av | transposeCongruenceFlow
      (concreteCenteredOrbitalDirection N Av.2) t Av.1 ∈ event}

def h16DownstreamConcreteCenteredZeroExtEventDerivativeIntegrand
    (r N K : ℕ) (event : Set (ConcreteMatrixState N)) (t : ℝ) :
    ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
  (h16DownstreamConcreteCenteredZeroExtShiftedEvent N t event).indicator
    (fun Av ↦ h16ZeroExtendedConcreteCenteredDensityScore r N K Av.2 Av.1)

/-- Exact body of U07's compact-time zero-extended `L1` envelope contract,
with the preceding U06-prefixed but definitionally identical objects. -/
abbrev H16DownstreamCompactZeroExtL1EnvelopeContract : Prop :=
  ∀ {N K r : ℕ}, (1 ≤ N) → (2 * N + 8 ≤ K) → (r ≤ 4) →
    (event : Set (ConcreteMatrixState N)) → MeasurableSet event →
    (R : ℝ) → (0 < R) →
    ∃ B : ComplexUnitSphere N → ℝ,
      Integrable B (complexUnitSphereProbabilityMeasure N) ∧
      (∀ t ∈ Set.Icc (-R) R,
        Integrable
          (h16DownstreamConcreteCenteredZeroExtEventDerivativeIntegrand
            r N K event t)
          ((concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K).prod
            (complexUnitSphereProbabilityMeasure N))) ∧
      (∀ᵐ v ∂(complexUnitSphereProbabilityMeasure N),
        ∀ t ∈ Set.Icc (-R) R,
          Integrable
            (fun A : ConcreteMatrixState N ↦
              h16DownstreamConcreteCenteredZeroExtEventDerivativeIntegrand
                r N K event t (A, v))
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) ∧
          (∫ A : ConcreteMatrixState N,
              ‖h16DownstreamConcreteCenteredZeroExtEventDerivativeIntegrand
                r N K event t (A, v)‖
              ∂(concreteScaledCOECornerLaw
                canonicalUnitaryHaarProbabilityFamily N K)) ≤ B v)

/-- Joint measurability is isolated as a source-level family; it contains no
event, time interval, derivative interchange, or projective conclusion. -/
abbrev H16ZeroExtendedScoreJointAEStrongMeasurabilityFamily : Prop :=
  ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 5),
    AEStronglyMeasurable
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        h16ZeroExtendedConcreteCenteredDensityScore
          (r : ℕ) N K Av.2 Av.1)
      ((concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K).prod
        (complexUnitSphereProbabilityMeasure N))

theorem measurableSet_h16DownstreamZeroExtShiftedEvent
    {N : ℕ} (hN : 1 ≤ N) (t : ℝ)
    {event : Set (ConcreteMatrixState N)} (hevent : MeasurableSet event) :
    MeasurableSet
      (h16DownstreamConcreteCenteredZeroExtShiftedEvent N t event) := by
  have heq :
      h16DownstreamConcreteCenteredZeroExtShiftedEvent N t event =
        (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
          concreteOrbitalMatrixUpdate N t Av.2 Av.1) ⁻¹' event := by
    ext Av
    simp only [h16DownstreamConcreteCenteredZeroExtShiftedEvent,
      Set.mem_setOf_eq, Set.mem_preimage]
    rw [transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate
      hN t Av.2 Av.1]
  rw [heq]
  exact measurable_concreteOrbitalMatrixUpdate N t hevent

/-- Exact H5, corrected weak facts, and joint score measurability discharge
the entire U07-facing compact zero-extension envelope.  The bound is in fact
independent of time and the section statement holds for every direction. -/
theorem h16DownstreamCompactZeroExtL1Envelope_of_weakFacts
    (hH5 : H16ExactH5Family)
    (W : ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K),
      COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (hjoint : H16ZeroExtendedScoreJointAEStrongMeasurabilityFamily) :
    H16DownstreamCompactZeroExtL1EnvelopeContract := by
  intro N K r hN hboundary hr event hevent R hR
  let rf : Fin 5 := ⟨r, by omega⟩
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ h16ZeroExtendedConcreteCenteredDensityScore r N K Av.2 Av.1
  let B : ComplexUnitSphere N → ℝ :=
    fun v ↦ ∫ A : ConcreteMatrixState N, ‖score (A, v)‖ ∂mu
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega : N ≤ K)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hbase : Integrable score (mu.prod sphere) := by
    exact integrable_h16ZeroExtendedScore_product_of_weakFacts
      hH5 (W hN hboundary) rf (hjoint hN hboundary rf)
  have hB : Integrable B sphere := by
    simpa only [B, score] using hbase.integral_norm_prod_right
  refine ⟨B, hB, ?_, ?_⟩
  · intro t ht
    have hset := measurableSet_h16DownstreamZeroExtShiftedEvent
      hN t hevent
    simpa only [h16DownstreamConcreteCenteredZeroExtEventDerivativeIntegrand,
      score, mu, sphere] using hbase.indicator hset
  · filter_upwards [] with v
    intro t ht
    let shifted : Set (ConcreteMatrixState N) :=
      (transposeCongruenceFlow
        (concreteCenteredOrbitalDirection N v) t) ⁻¹' event
    have hshifted : MeasurableSet shifted := by
      exact ((by
        unfold transposeCongruenceFlow
        exact measurable_transposeCongruence _ : Measurable
          (transposeCongruenceFlow
            (concreteCenteredOrbitalDirection N v) t)) hevent)
    have hsection : Integrable
        (h16ZeroExtendedConcreteCenteredDensityScore r N K v) mu := by
      simpa only [rf] using
        integrable_h16ZeroExtendedConcreteCenteredDensityScore_of_weakFacts
          hH5 (W hN hboundary) rf v
    have heventSection : Integrable
        (shifted.indicator
          (h16ZeroExtendedConcreteCenteredDensityScore r N K v)) mu :=
      hsection.indicator hshifted
    constructor
    · change Integrable
        (shifted.indicator
          (h16ZeroExtendedConcreteCenteredDensityScore r N K v)) mu
      exact heventSection
    · change
        (∫ A : ConcreteMatrixState N,
          ‖shifted.indicator
            (h16ZeroExtendedConcreteCenteredDensityScore r N K v) A‖ ∂mu) ≤
          B v
      change _ ≤ ∫ A : ConcreteMatrixState N,
        ‖h16ZeroExtendedConcreteCenteredDensityScore r N K v A‖ ∂mu
      apply integral_mono_ae heventSection.norm hsection.norm
      filter_upwards [] with A
      exact norm_indicator_le_norm_self
        (h16ZeroExtendedConcreteCenteredDensityScore r N K v) A

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
