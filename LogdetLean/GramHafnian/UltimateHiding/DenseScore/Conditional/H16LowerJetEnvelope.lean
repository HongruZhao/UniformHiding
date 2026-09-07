import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CoordinateSupportCompact
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
# Fixed integrable envelopes for the lower centered jets

For orders zero through three, global continuity and literal zero extension
already imply a fixed integrable base-coordinate envelope.  The reason is
purely geometric: the projective sphere times the closed unit coordinate ball
is compact, and the open COE support lies in that ball.

This removes lower-order envelope construction from the direct order-four
analytic blocker.  The fourth jet remains governed only by its sharp `L1`
radial estimate.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 900000 in
theorem exists_h16CenteredBaseJetLowerEnvelope_of_continuous
    {N K : ℕ}
    (hcontinuous : ∀ r : Fin 4,
      Continuous (fun p :
          (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
        h16CenteredTransportJet N K r.castSucc p.1.1 p.1.2 p.2))
    (hzero : ∀ (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ)
      (x : ComplexSymmetricCoordinates N),
      x ∉ h16CenteredTransportSupport v t →
        h16CenteredTransportJet N K r v t x = 0)
    (r : Fin 4) :
    ∃ b : ComplexSymmetricCoordinates N → ℝ,
      (∀ x, 0 ≤ b x) ∧
      Integrable b (complexSymmetricCoordinateVolume N) ∧
      ∀ (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N),
        ‖h16CenteredTransportJet N K r.castSucc v 0 x‖ ≤ b x := by
  let ball : Set (ComplexSymmetricCoordinates N) := Metric.closedBall 0 1
  let F : ComplexUnitSphere N × ball → ℝ := fun p ↦
    ‖h16CenteredTransportJet N K r.castSucc p.1 0 p.2.1‖
  have hF : Continuous F := by
    let param : ComplexUnitSphere N × ball →
        (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N :=
      fun p ↦ ((p.1, (0 : ℝ)), p.2.1)
    have hparam : Continuous param := by
      unfold param
      fun_prop
    have hcomp := (hcontinuous r).comp hparam
    simpa only [F, param, Function.comp_apply] using hcomp.norm
  obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image hF.continuousOn
  let b : ComplexSymmetricCoordinates N → ℝ :=
    ball.indicator (fun _ ↦ max C 0)
  have hballCompact : IsCompact ball := by
    exact isCompact_h16COECoordinateSupport_closedBall N
  have hbint : Integrable b (complexSymmetricCoordinateVolume N) := by
    have hvol : complexSymmetricCoordinateVolume N =
        (volume : Measure (ComplexSymmetricCoordinates N)) := by
      unfold complexSymmetricCoordinateVolume
      exact MeasureTheory.volume_pi.symm
    rw [hvol]
    unfold b
    exact IntegrableOn.integrable_indicator
      (integrableOn_const hballCompact.measure_ne_top)
      hballCompact.measurableSet
  refine ⟨b, ?_, hbint, ?_⟩
  · intro x
    by_cases hx : x ∈ ball
    · simp [b, hx]
    · simp [b, hx]
  · intro v x
    by_cases hx : x ∈ ball
    · have hp : (v, ⟨x, hx⟩) ∈ (Set.univ : Set (ComplexUnitSphere N × ball)) :=
        Set.mem_univ _
      have hFC : F (v, ⟨x, hx⟩) ≤ C :=
        hC (Set.mem_image_of_mem F hp)
      exact hFC.trans (le_max_left C 0) |>.trans_eq (by simp [b, hx])
    · have hnotSupport : x ∉ h16CenteredTransportSupport v 0 := by
        intro hsupp
        have hbase : coeCornerSupport
            (complexSymmetricMatrixOfCoordinates x) := by
          simpa [h16CenteredTransportSupport] using hsupp
        exact hx (h16COECoordinateSupport_subset_closedBall hbase)
      rw [hzero r.castSucc v 0 x hnotSupport]
      simp [b, hx]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
