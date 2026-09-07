import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16WeakFactsProof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H18_CompactL1_Proof

/-!
# CONDITIONAL H18 adapter from U06's checked downstream handoff

This module consumes only
`h16DownstreamCompactL1ScientificInputs_from_scientificInputs_exactH5` from
U06 as its scientific handoff.  Exact H5 and the determinant-local scientific
input family remain explicit theorem parameters, so this is a reduced
conditional endpoint, not an unconditional proof of H18.

The four small adapter lemmas below only reconcile U06-prefixed definitions
with the definitionally identical U07 compact-`L1` contracts.  In particular,
every helper retains `1 ≤ N` and `2 * N + 8 ≤ K` through the packaged fields.
-/

open TopologicalSpace MeasureTheory Set Filter
open scoped Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Pure adapter from U06's packaged literal H16 field to U07's contract. -/
theorem coeCornerCenteredFixedDirectionH16Contract_of_h16Downstream
    (I : H16DownstreamCompactL1ScientificInputs) :
    CoeCornerCenteredFixedDirectionH16Contract := by
  change H16DownstreamFixedDirectionH16Contract
  exact I.fixedDirectionH16

/-- Pure adapter from U06's packaged genuine fixed-direction `C^4` field. -/
theorem coeCornerCenteredFixedDirectionC4Contract_of_h16Downstream
    (I : H16DownstreamCompactL1ScientificInputs) :
    CoeCornerCenteredFixedDirectionC4Contract := by
  change H16DownstreamFixedDirectionC4Contract
  exact I.fixedDirectionC4

/-- Pure adapter from U06's packaged scaled-COE support field. -/
theorem coeCornerCenteredScaledCOESupportContract_of_h16Downstream
    (I : H16DownstreamCompactL1ScientificInputs) :
    CoeCornerCenteredScaledCOESupportContract := by
  change H16DownstreamScaledCOESupportContract
  exact I.scaledCOESupport

/-- Pure adapter from U06's prefixed zero-extension envelope to U07's
definitionally identical compact-time envelope contract. -/
theorem coeCornerCenteredCompactZeroExtL1EnvelopeContract_of_h16Downstream
    (I : H16DownstreamCompactL1ScientificInputs) :
    CoeCornerCenteredCompactZeroExtL1EnvelopeContract := by
  change H16DownstreamCompactZeroExtL1EnvelopeContract
  exact I.compactZeroExtL1Envelope

/-- `CONDITIONAL` / `REDUCED`: literal H18 with its exact endpoint
quantifiers, derived from U06's checked four-field handoff.  The two remaining
scientific assumptions are explicit and contain no H17/H18 projective
conclusion. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_from_U06_scientificInputs_exactH5
    (hH5 : H16ExactH5Family)
    (H : H16CenteredWeakFactsScientificInputsFamily)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y =
      ∫ v : ComplexUnitSphere N,
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y
          ∂(complexUnitSphereProbabilityMeasure N) := by
  let I : H16DownstreamCompactL1ScientificInputs :=
    h16DownstreamCompactL1ScientificInputs_from_scientificInputs_exactH5 hH5 H
  exact
    coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_compactL1_support_conditional
      (coeCornerCenteredFixedDirectionH16Contract_of_h16Downstream I)
      (coeCornerCenteredFixedDirectionC4Contract_of_h16Downstream I)
      (coeCornerCenteredScaledCOESupportContract_of_h16Downstream I)
      (coeCornerCenteredCompactZeroExtL1EnvelopeContract_of_h16Downstream I)
      hN hboundary hr event hevent y

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
