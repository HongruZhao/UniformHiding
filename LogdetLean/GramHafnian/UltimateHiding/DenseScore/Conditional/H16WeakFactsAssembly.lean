import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantExhaustionLimit
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthRadialIntegrabilityFromExactH5
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16LowerJetEnvelope
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16ScorePointwiseIdentification
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredJetTransport
import Mathlib.Tactic

/-!
# Assembly of the corrected H16 weak-generator package

This file fills every bookkeeping, normalization, integrability, and
transport field of `COECenteredOrderFourWeakGeneratorFacts`.  The remaining
inputs are strictly determinant-local: the independent centered-coordinate
Jacobian, joint measurability and lower-jet continuity, the sharp fourth-jet
radial estimate, and finite-domain Gauss--Green certificates.  Exact H5 is
kept explicit and is used only to normalize the determinant density and to
integrate the shifted fourth-order radial kernel.

There is no pointwise fourth boundary derivative and no time-uniform
pointwise fourth-jet majorant.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The determinant-local inputs that remain after all generic weak-facts
assembly has been discharged.  This is below H16: it contains no `L1` curve,
Banach derivative, event, iterated derivative, projective integral, or
compact-time score conclusion. -/
structure H16CenteredWeakFactsScientificInputs
    (N K : ℕ) (_hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) : Type where
  complexJacobian : H16CenteredCoordinateComplexJacobianFamily N
  jet_joint_measurable :
    ∀ r : Fin 5,
      Measurable (fun p :
          (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
        h16CenteredTransportJet N K r p.1.1 p.1.2 p.2)
  continuous_through_three :
    ∀ r : Fin 4,
      Continuous (fun p :
          (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
        h16CenteredTransportJet N K r.castSucc p.1.1 p.1.2 p.2)
  fourthJet_radialEstimate : H16CenteredFourthJetRadialEstimate N K
  finiteGaussGreen : H16CenteredFiniteGaussGreenFacts N K hboundary

/-- Generic input record for the bookkeeping part of the weak-facts
assembly.  Unlike `H16CenteredWeakFactsScientificInputs`, it asks directly
for the global weak-generator chain and is therefore independent of how that
chain was obtained.  In particular, the sequential A5-good-level
Gauss--Green route can inhabit this record without reconstructing the
strictly stronger all-small-real-level certificate. -/
structure H16CenteredWeakFactsAssemblyInputs
    (N K : ℕ) (_hN : 1 ≤ N) (_hboundary : 2 * N + 8 ≤ K) : Type where
  complexJacobian : H16CenteredCoordinateComplexJacobianFamily N
  jet_joint_measurable :
    ∀ r : Fin 5,
      Measurable (fun p :
          (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
        h16CenteredTransportJet N K r p.1.1 p.1.2 p.2)
  continuous_through_three :
    ∀ r : Fin 4,
      Continuous (fun p :
          (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
        h16CenteredTransportJet N K r.castSucc p.1.1 p.1.2 p.2)
  fourthJet_radialEstimate : H16CenteredFourthJetRadialEstimate N K
  weakGenerator_chain : H16CenteredWeakGeneratorChain N K

/-- The original finite-Gauss--Green scientific inputs feed the generic
assembler through the already proved exhaustion theorem. -/
noncomputable def H16CenteredWeakFactsScientificInputs.toAssemblyInputs
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : H16CenteredWeakFactsScientificInputs N K hN hboundary) :
    H16CenteredWeakFactsAssemblyInputs N K hN hboundary where
  complexJacobian := H.complexJacobian
  jet_joint_measurable := H.jet_joint_measurable
  continuous_through_three := H.continuous_through_three
  fourthJet_radialEstimate := H.fourthJet_radialEstimate
  weakGenerator_chain :=
    h16CenteredWeakGeneratorChain_of_finiteGaussGreen H.finiteGaussGreen

private theorem h16_baseJet_aestronglyMeasurable_of_joint
    {N K : ℕ}
    (hjoint : ∀ r : Fin 5,
      Measurable (fun p :
          (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
        h16CenteredTransportJet N K r p.1.1 p.1.2 p.2))
    (r : Fin 5) (v : ComplexUnitSphere N) :
    AEStronglyMeasurable (h16CenteredTransportJet N K r v 0)
      (complexSymmetricCoordinateVolume N) := by
  have hparam : Measurable
      (fun x : ComplexSymmetricCoordinates N ↦ ((v, (0 : ℝ)), x)) :=
    measurable_const.prodMk measurable_id
  exact ((hjoint r).comp hparam).aestronglyMeasurable

private theorem h16_exists_baseJet_envelope_of_scientificInputs
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : H16CenteredWeakFactsAssemblyInputs N K hN hboundary)
    (r : Fin 5) :
    ∃ b : ComplexSymmetricCoordinates N → ℝ,
      (∀ x, 0 ≤ b x) ∧
      Integrable b (complexSymmetricCoordinateVolume N) ∧
      ∀ v : ComplexUnitSphere N,
        ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
          ‖h16CenteredTransportJet N K r v 0 x‖ ≤ b x := by
  by_cases hr : (r : ℕ) < 4
  · let s : Fin 4 := ⟨r, hr⟩
    have hrs : s.castSucc = r := Fin.ext rfl
    obtain ⟨b, hbnonneg, hbint, hbound⟩ :=
      exists_h16CenteredBaseJetLowerEnvelope_of_continuous
        H.continuous_through_three
        (fun q v t x hx ↦ h16CenteredTransportJet_zero_off_support q v t x hx)
        s
    refine ⟨b, hbnonneg, hbint, ?_⟩
    intro v
    exact ae_of_all _ fun x ↦ by simpa only [hrs] using hbound v x
  · have hr4 : r = (4 : Fin 5) := Fin.ext (by omega)
    subst r
    let b : ComplexSymmetricCoordinates N → ℝ := fun x ↦
      H.fourthJet_radialEstimate.constant *
        h16COEFourthRadialKernel N K x
    refine ⟨b, ?_, ?_, ?_⟩
    · exact fun x ↦ h16CenteredFourthJetRadialMajorant_nonnegative
        H.fourthJet_radialEstimate x
    · exact integrable_h16CenteredFourthJetRadialMajorant
        (h16COEFourthRadialIntegrability_of_exactH5 hH5 hN hboundary)
        H.fourthJet_radialEstimate
    · exact H.fourthJet_radialEstimate.jet_norm_le

private theorem h16_baseJet_integrable_of_scientificInputs
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : H16CenteredWeakFactsAssemblyInputs N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) :
    Integrable (h16CenteredTransportJet N K r v 0)
      (complexSymmetricCoordinateVolume N) := by
  obtain ⟨b, hbnonneg, hbint, hbound⟩ :=
    h16_exists_baseJet_envelope_of_scientificInputs hH5 H r
  exact hbint.mono'
    (h16_baseJet_aestronglyMeasurable_of_joint H.jet_joint_measurable r v)
    (by
      filter_upwards [hbound v] with x hx
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hbnonneg x)] using hx)

set_option maxHeartbeats 900000 in
private theorem h16_jet_integrable_of_scientificInputs
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : H16CenteredWeakFactsAssemblyInputs N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ) :
    Integrable (h16CenteredTransportJet N K r v t)
      (complexSymmetricCoordinateVolume N) := by
  have hbase := h16_baseJet_integrable_of_scientificInputs hH5 H r v
  have hcomp : Integrable
      (h16CenteredTransportJet N K r v 0 ∘
        h16CenteredCoordinateFlow v (-t))
      (complexSymmetricCoordinateVolume N) :=
    (h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
      v (-t) (H.complexJacobian v (-t))).integrable_comp_of_integrable hbase
  apply hcomp.congr
  exact ae_of_all _ fun x ↦
    (h16CenteredTransportJet_eq_zero_pullback r v t x).symm

private theorem h16_jet_at_zero_score_global
    {N K : ℕ} (hN : 1 ≤ N) (hK : 0 < K)
    (r : Fin 5) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredTransportJet N K r v 0 x =
      h16ZeroExtendedConcreteCenteredDensityScore
          (r : ℕ) N K v
          (h16ScaledSymmetricCoordinateEmbedding N K x) *
        h16CenteredTransportJet N K 0 v 0 x := by
  by_cases hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)
  · exact h16CenteredTransportJet_zero_eq_score_mul_density_pointwise
      hN hK r v x hx
  · have hout : x ∉ h16CenteredTransportSupport v 0 := by
      simpa [h16CenteredTransportSupport] using hx
    rw [h16CenteredTransportJet_zero_off_support r v 0 x hout]
    rw [h16CenteredTransportJet_zero_off_support (0 : Fin 5) v 0 x hout]
    simp

/-- Exact H5 and the generic analytic/weak-generator inputs construct every
field of the corrected weak-generator package.  In particular, all-time
`L1` integrability and the fixed pulled-back envelope are derived rather than
assumed.  The source of the weak-generator chain is deliberately abstracted
so both the original and sequential Gauss--Green routes can use the same
kernel-checked assembly. -/
noncomputable def h16CenteredOrderFourWeakGeneratorFacts_of_assemblyInputs_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : H16CenteredWeakFactsAssemblyInputs N K hN hboundary) :
    COECenteredOrderFourWeakGeneratorFacts N K hN hboundary := by
  classical
  have hexists : ∀ r : Fin 5,
      ∃ b : ComplexSymmetricCoordinates N → ℝ,
        (∀ x, 0 ≤ b x) ∧
        Integrable b (complexSymmetricCoordinateVolume N) ∧
        ∀ v : ComplexUnitSphere N,
          ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
            ‖h16CenteredTransportJet N K r v 0 x‖ ≤ b x :=
    fun r ↦ h16_exists_baseJet_envelope_of_scientificInputs hH5 H r
  let b : Fin 5 → ComplexSymmetricCoordinates N → ℝ :=
    fun r ↦ Classical.choose (hexists r)
  have hb := fun r ↦ Classical.choose_spec (hexists r)
  refine
    { scalar := coeBoundaryExponentFourFacts hboundary
      coordinate_measurePreserving := fun v t ↦
        h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
          v t (H.complexJacobian v t)
      density_zero_eq_probabilityDensity :=
        h16CenteredTransportJet_zero_eq_probabilityDensity
      jet_joint_measurable := H.jet_joint_measurable
      jet_integrable := fun r v t ↦
        h16_jet_integrable_of_scientificInputs hH5 H r v t
      zero_off_support := fun r v t x hx ↦
        h16CenteredTransportJet_zero_off_support r v t x hx
      continuous_through_three := H.continuous_through_three
      baseJetMajorantFour := fun x ↦
        H.fourthJet_radialEstimate.constant *
          h16COEFourthRadialKernel N K x
      baseJetMajorantFour_nonnegative := fun x ↦
        h16CenteredFourthJetRadialMajorant_nonnegative
          H.fourthJet_radialEstimate x
      baseJetMajorantFour_integrable :=
        integrable_h16CenteredFourthJetRadialMajorant
          (h16COEFourthRadialIntegrability_of_exactH5 hH5 hN hboundary)
          H.fourthJet_radialEstimate
      baseJet_four_le := H.fourthJet_radialEstimate.jet_norm_le
      weak_generator_chain := H.weakGenerator_chain
      pulledBack_L1_envelope := ?_
      jet_at_zero_score := ?_ }
  · refine ⟨b, ?_, ?_⟩
    · intro r
      exact ⟨(hb r).1, (hb r).2.1⟩
    · intro r v t
      filter_upwards [(hb r).2.2 v] with y hy
      calc
        ‖h16CenteredTransportJet N K r v t
            (h16CenteredCoordinateFlow v t y)‖ =
            ‖h16CenteredTransportJet N K r v 0 y‖ := by
          rw [h16CenteredTransportJet_eq_zero_pullback]
          rw [h16CenteredCoordinateFlow_neg_left]
        _ ≤ b r y := hy
  · intro r v
    exact ae_of_all _ fun x ↦ h16_jet_at_zero_score_global
      hN (by omega) r v x

/-- Backward-compatible finite-Gauss--Green entry point.  Its declaration
type is unchanged; only its implementation now factors through the generic
assembler above. -/
noncomputable def h16CenteredOrderFourWeakGeneratorFacts_of_exactH5
    (hH5 : H16ExactH5Family)
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : H16CenteredWeakFactsScientificInputs N K hN hboundary) :
    COECenteredOrderFourWeakGeneratorFacts N K hN hboundary :=
  h16CenteredOrderFourWeakGeneratorFacts_of_assemblyInputs_exactH5
    hH5 H.toAssemblyInputs

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
