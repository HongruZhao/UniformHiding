import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H18_U06ScientificInputs_Proof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H17_CompactL1_Proof

/-!
# CONDITIONAL H17 adapter from U06's checked downstream handoff

This is the literal projective `C^4` adapter.  It consumes the same single U06
handoff theorem as the H18 adapter and leaves exact H5 plus
`H16CenteredWeakFactsScientificInputsFamily` explicit.  Consequently its
status is `REDUCED`, never unconditional `PROVED`.
-/

open TopologicalSpace MeasureTheory Set Filter
open scoped Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- `CONDITIONAL` / `REDUCED`: literal H17 with its exact endpoint
quantifiers, derived from U06's checked four-field handoff. -/
theorem coeCorner_centeredProjective_eventPath_contDiff_four_H17_from_U06_scientificInputs_exactH5
    (hH5 : H16ExactH5Family)
    (H : H16CenteredWeakFactsScientificInputsFamily)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4
      (concreteProjectiveAveragedCenteredCOEEventPath N K event) := by
  let I : H16DownstreamCompactL1ScientificInputs :=
    h16DownstreamCompactL1ScientificInputs_from_scientificInputs_exactH5 hH5 H
  exact
    coeCorner_centeredProjective_eventPath_contDiff_four_H17_compactL1_support_conditional
      (coeCornerCenteredFixedDirectionH16Contract_of_h16Downstream I)
      (coeCornerCenteredFixedDirectionC4Contract_of_h16Downstream I)
      (coeCornerCenteredScaledCOESupportContract_of_h16Downstream I)
      (coeCornerCenteredCompactZeroExtL1EnvelopeContract_of_h16Downstream I)
      hN hboundary event hevent

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
