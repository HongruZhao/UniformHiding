import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantLocalLowerJetContinuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-!
# One local integrable envelope for the lower H16 jets

For times in `[-1,1]`, every moving determinant support is contained in one
compact coordinate carrier: the image of the projective sphere, the compact
time interval, and the closed unit base-support ball under the centered flow.
Joint continuity then bounds each order-zero through order-three literal jet
on that carrier.  Extending the bound by zero gives a single integrable
envelope, uniform in both projective direction and local time.

This is the domination input for lifting pointwise lower-jet derivatives to
the canonical `L1` classes.  It uses no H5, weak-generator, finite-perimeter,
or Gauss--Green input.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 3600000

/-- Compact ambient parameter set whose flow image contains every moving
support for time in `[-1,1]`. -/
def h16CenteredLocalFlowSource (N : ℕ) : Set
    ((ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N) :=
  ((Set.univ : Set (ComplexUnitSphere N)) ×ˢ Set.Icc (-1 : ℝ) 1) ×ˢ
    Metric.closedBall (0 : ComplexSymmetricCoordinates N) 1

/-- Joint continuity of the centered flow in direction, time, and coordinate. -/
theorem continuous_h16CenteredCoordinateFlow_allParameters
    {N : ℕ} (hN : 1 ≤ N) :
    Continuous (fun p :
        (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
      h16CenteredCoordinateFlow p.1.1 p.1.2 p.2) := by
  unfold h16CenteredCoordinateFlow transposeCongruenceFlowCoordinates
  simp_rw [transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate hN]
  apply continuous_pi
  intro ij
  simp only [complexSymmetricCoordinatesOfMatrix,
    concreteOrbitalMatrixUpdate, concreteOrbitalFactor,
    complexSymmetricMatrixOfCoordinates, complexRankOneProjection,
    Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.one_apply]
  apply continuous_finsetSum
  intro j hj
  apply Continuous.mul
  · apply continuous_finsetSum
    intro j' hj'
    apply Continuous.mul
    · fun_prop
    · split <;> fun_prop
  · fun_prop

/-- The common local coordinate carrier for all projective directions and
times in `[-1,1]`. -/
def h16CenteredLocalFlowCarrier (N : ℕ) :
    Set (ComplexSymmetricCoordinates N) :=
  (fun p : (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
    h16CenteredCoordinateFlow p.1.1 p.1.2 p.2) ''
      h16CenteredLocalFlowSource N

theorem isCompact_h16CenteredLocalFlowCarrier
    {N : ℕ} (hN : 1 ≤ N) :
    IsCompact (h16CenteredLocalFlowCarrier N) := by
  have hsource : IsCompact (h16CenteredLocalFlowSource N) := by
    unfold h16CenteredLocalFlowSource
    exact (isCompact_univ.prod isCompact_Icc).prod
      (isCompact_closedBall (0 : ComplexSymmetricCoordinates N) 1)
  exact hsource.image (continuous_h16CenteredCoordinateFlow_allParameters hN)

/-- Every moving support at local time lies in the common compact carrier. -/
theorem h16CenteredTransportSupport_subset_localFlowCarrier
    {N : ℕ} (v : ComplexUnitSphere N) {t : ℝ}
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    h16CenteredTransportSupport v t ⊆ h16CenteredLocalFlowCarrier N := by
  intro x hx
  let y := h16CenteredCoordinateFlow v (-t) x
  have hySupport : y ∈ h16CenteredTransportSupport v 0 :=
    (h16CenteredTransportSupport_iff_pullback_zero v t x).1 hx
  have hyCOE : coeCornerSupport (complexSymmetricMatrixOfCoordinates y) := by
    simpa [h16CenteredTransportSupport] using hySupport
  have hyBall : y ∈ Metric.closedBall
      (0 : ComplexSymmetricCoordinates N) 1 :=
    h16COECoordinateSupport_subset_closedBall hyCOE
  refine ⟨((v, t), y), ?_, ?_⟩
  · exact ⟨⟨Set.mem_univ v, ht⟩, hyBall⟩
  · exact h16CenteredCoordinateFlow_neg_right v t x

/-- A fixed compactly supported integrable envelope controls one chosen lower
jet uniformly in direction and in all times `[-1,1]`. -/
theorem exists_h16CenteredLocalJetLowerEnvelope
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) :
    ∃ b : ComplexSymmetricCoordinates N → ℝ,
      (∀ x, 0 ≤ b x) ∧
      Integrable b (complexSymmetricCoordinateVolume N) ∧
      ∀ (v : ComplexUnitSphere N) (t : ℝ)
        (_ht : t ∈ Set.Icc (-1 : ℝ) 1)
        (x : ComplexSymmetricCoordinates N),
        ‖h16CenteredTransportJet N K r.castSucc v t x‖ ≤ b x := by
  let carrier : Set (ComplexSymmetricCoordinates N) :=
    h16CenteredLocalFlowCarrier N
  let F : ((ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N) → ℝ :=
    fun p ↦ ‖h16CenteredTransportJet N K r.castSucc p.1.1 p.1.2 p.2‖
  have hF : Continuous F := by
    simpa only [F] using
      (continuous_h16CenteredTransportJet_through_three hN hboundary r).norm
  let parameterSet : Set
      ((ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N) :=
    ((Set.univ : Set (ComplexUnitSphere N)) ×ˢ Set.Icc (-1 : ℝ) 1) ×ˢ carrier
  have hparameterCompact : IsCompact parameterSet := by
    unfold parameterSet
    exact (isCompact_univ.prod isCompact_Icc).prod
      (isCompact_h16CenteredLocalFlowCarrier hN)
  obtain ⟨C, hC⟩ := hparameterCompact.bddAbove_image hF.continuousOn
  let b : ComplexSymmetricCoordinates N → ℝ :=
    carrier.indicator (fun _ ↦ max C 0)
  have hcarrierCompact : IsCompact carrier := by
    simpa only [carrier] using isCompact_h16CenteredLocalFlowCarrier hN
  have hbint : Integrable b (complexSymmetricCoordinateVolume N) := by
    have hvol : complexSymmetricCoordinateVolume N =
        (volume : Measure (ComplexSymmetricCoordinates N)) := by
      unfold complexSymmetricCoordinateVolume
      exact MeasureTheory.volume_pi.symm
    rw [hvol]
    unfold b
    exact IntegrableOn.integrable_indicator
      (integrableOn_const hcarrierCompact.measure_ne_top)
      hcarrierCompact.measurableSet
  refine ⟨b, ?_, hbint, ?_⟩
  · intro x
    by_cases hx : x ∈ carrier <;> simp [b, hx]
  · intro v t ht x
    by_cases hx : x ∈ carrier
    · let p : (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N :=
        ((v, t), x)
      have hp : p ∈ parameterSet := ⟨⟨Set.mem_univ v, ht⟩, hx⟩
      have hFC : F p ≤ C := hC (Set.mem_image_of_mem F hp)
      have hFC' : ‖h16CenteredTransportJet N K r.castSucc v t x‖ ≤ C := by
        simpa only [F, p] using hFC
      exact hFC'.trans (le_max_left C 0) |>.trans_eq (by simp [b, hx])
    · have hnotSupport : x ∉ h16CenteredTransportSupport v t := by
        intro hsupp
        exact hx (h16CenteredTransportSupport_subset_localFlowCarrier v ht hsupp)
      rw [h16CenteredTransportJet_zero_off_support r.castSucc v t x hnotSupport]
      simp [b, hx]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
