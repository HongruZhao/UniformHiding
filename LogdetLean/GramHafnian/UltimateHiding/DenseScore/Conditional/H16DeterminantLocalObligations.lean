import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16WeakFactsProof

/-!
# Minimal determinant-local obligations for literal H16

SOURCE-ONLY / NO-BUILD CHECKPOINT under host occupancy protection.

This interface removes two redundant measurability obligations from
`H16CenteredWeakFactsScientificInputs`: lower-jet measurability follows from
the already required continuity through order three, and the per-direction
base-fourth-jet measurability inside the radial estimate follows from one
joint fourth-jet measurability field.

Exact H5 is deliberately absent from this determinant-local structure.  The
approved A1 adapter supplies it separately to the checked endpoint theorem.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Smallest currently isolated determinant-local data sufficient to build
the corrected weak facts.  It contains no normalization theorem, radial
integrability premise, `L1` curve, Bochner derivative, event, H16 endpoint,
projective integral, or H17/H18 conclusion. -/
structure H16CenteredDeterminantLocalObligations
    (N K : ℕ) (_hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) : Type where
  complexJacobian : H16CenteredCoordinateComplexJacobianFamily N
  continuous_through_three :
    ∀ r : Fin 4,
      Continuous (fun p :
          (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
        h16CenteredTransportJet N K r.castSucc p.1.1 p.1.2 p.2)
  fourthJet_joint_measurable :
    Measurable (fun p :
        (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
      h16CenteredTransportJet N K 4 p.1.1 p.1.2 p.2)
  fourthJet_radialConstant : ℝ
  fourthJet_radialConstant_nonnegative :
    0 ≤ fourthJet_radialConstant
  fourthJet_radial_bound :
    ∀ v : ComplexUnitSphere N,
      ∀ᵐ x ∂(complexSymmetricCoordinateVolume N),
        ‖h16CenteredTransportJet N K 4 v 0 x‖ ≤
          fourthJet_radialConstant * h16COEFourthRadialKernel N K x
  finiteGaussGreen : H16CenteredFiniteGaussGreenFacts N K hboundary

/-- Source-level adapter to the older scientific-input record.  The removed
measurability fields are derived formally from the smaller obligations. -/
noncomputable def H16CenteredDeterminantLocalObligations.toScientificInputs
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (H : H16CenteredDeterminantLocalObligations N K hN hboundary) :
    H16CenteredWeakFactsScientificInputs N K hN hboundary where
  complexJacobian := H.complexJacobian
  jet_joint_measurable := by
    intro r
    by_cases hr : (r : ℕ) < 4
    · let s : Fin 4 := ⟨r, hr⟩
      have hrs : s.castSucc = r := Fin.ext rfl
      simpa only [hrs] using (H.continuous_through_three s).measurable
    · have hr4 : r = (4 : Fin 5) := Fin.ext (by omega)
      simpa only [hr4] using H.fourthJet_joint_measurable
  continuous_through_three := H.continuous_through_three
  fourthJet_radialEstimate :=
    { constant := H.fourthJet_radialConstant
      constant_nonnegative := H.fourthJet_radialConstant_nonnegative
      jet_aestronglyMeasurable := by
        intro v
        have hparam : Measurable
            (fun x : ComplexSymmetricCoordinates N ↦
              (((v, (0 : ℝ))), x)) :=
          measurable_const.prodMk measurable_id
        exact (H.fourthJet_joint_measurable.comp hparam).aestronglyMeasurable
      jet_norm_le := H.fourthJet_radial_bound }
  finiteGaussGreen := H.finiteGaussGreen

/-- Universally quantified minimal determinant-local family. -/
abbrev H16CenteredDeterminantLocalObligationsFamily : Type :=
  ∀ {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K),
    H16CenteredDeterminantLocalObligations N K hN hboundary

/-- Source-level family adapter consumed by the already checked conditional
H16 and U07 handoff theorems. -/
noncomputable def H16CenteredDeterminantLocalObligationsFamily.toScientificInputs
    (H : H16CenteredDeterminantLocalObligationsFamily) :
    H16CenteredWeakFactsScientificInputsFamily :=
  fun hN hboundary ↦ (H hN hboundary).toScientificInputs

/-- `CONDITIONAL / SOURCE-ONLY`: literal H16 from exact H5 (now supplied by
approved A1) and only the minimal determinant-local obligations above. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_from_determinantLocal_exactH5
    (hH5 : H16ExactH5Family)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (H : H16CenteredDeterminantLocalObligations N K hN hboundary)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K) :=
  coeCorner_centeredFixedDirection_eventPath_derivative_from_scientificInputs_exactH5
    hH5 hN hboundary hr v H.toScientificInputs event hevent

/-- `CONDITIONAL / SOURCE-ONLY`: minimal determinant-local family supplies
the exact four-field compact-`L1` handoff already consumed by U07. -/
theorem h16DownstreamCompactL1ScientificInputs_from_determinantLocal_exactH5
    (hH5 : H16ExactH5Family)
    (H : H16CenteredDeterminantLocalObligationsFamily) :
    H16DownstreamCompactL1ScientificInputs :=
  h16DownstreamCompactL1ScientificInputs_from_scientificInputs_exactH5
    hH5 H.toScientificInputs

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
