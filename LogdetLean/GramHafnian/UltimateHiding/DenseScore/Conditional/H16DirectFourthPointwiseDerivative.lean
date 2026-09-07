import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CoordinateSupportBoundaryNull
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16LowerJetLocalEnvelope
import Mathlib.Tactic

/-!
# The sharp pointwise `3 -> 4` H16 derivative away from a null frontier

The fourth zero-extended determinant jet need not be continuous at the
support boundary.  Nevertheless, away from that boundary the order-three
literal jet has the order-four literal jet as its time derivative.  Convexity
of the exact matrix ball makes the exceptional coordinate frontier null.

This is the pointwise/a.e. half of the remaining direct `L1` derivative.
-/

open Filter MeasureTheory Set
open scoped ContDiff Topology Matrix.Norms.L2Operator

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.H3H4Central

set_option maxHeartbeats 3600000

private theorem h16CenteredGap_time_contDiff_fourth_pointwise
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    ContDiff ℝ ∞ (fun u : ℝ ↦
      h16CenteredTransportGapDeterminant v u x) := by
  have heq : (fun u : ℝ ↦ h16CenteredTransportGapDeterminant v u x) =
      fun u : ℝ ↦ h16AmbientTransportGap N ((v.1, x), u) := by
    funext u
    exact h16CenteredTransportGap_eq_ambient hN v u x
  rw [heq]
  exact (contDiff_h16AmbientTransportGap N).comp
    (contDiff_const.prodMk contDiff_id)

/-- At an interior time, the third interior jet has the fourth interior jet
as derivative.  Only local smoothness of the real power at a positive gap is
used. -/
private theorem h16CenteredTransportInteriorJet_three_hasDerivAt
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) (t : ℝ)
    (hgap : 0 < h16CenteredTransportGapDeterminant v t x) :
    HasDerivAt
      (fun u : ℝ ↦ iteratedDeriv 3
        (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) u)
      (iteratedDeriv 4
        (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) t) t := by
  let q : ℝ → ℝ := fun u ↦
    h16CenteredTransportGapDeterminant v u x
  let f : ℝ → ℝ := fun u ↦
    h16CenteredTransportInteriorDensity N K v u x
  have hq : ContDiffAt ℝ 4 q t :=
    (h16CenteredGap_time_contDiff_fourth_pointwise hN v x).contDiffAt.of_le
      (WithTop.coe_le_coe.2 (show (4 : ℕ∞) ≤ ⊤ from le_top))
  have hpow : ContDiffAt ℝ 4
      (fun z : ℝ ↦ z ^ coeCornerDensityExponent N K) (q t) :=
    Real.contDiffAt_rpow_const_of_ne hgap.ne'
  have hf : ContDiffAt ℝ 4 f t := by
    unfold f h16CenteredTransportInteriorDensity
    exact contDiffAt_const.mul (hpow.comp t hq)
  have hdiff : DifferentiableAt ℝ (iteratedDeriv 3 f) t := by
    rw [← differentiableWithinAt_univ]
    rw [← iteratedDerivWithin_univ]
    exact hf.differentiableWithinAt_iteratedDerivWithin
      (by norm_num) (by simpa using (uniqueDiffOn_univ : UniqueDiffOn ℝ (Set.univ : Set ℝ)))
  have hd : HasDerivAt (iteratedDeriv 3 f)
      (deriv (iteratedDeriv 3 f) t) t := hdiff.hasDerivAt
  simpa only [f, iteratedDeriv_succ] using hd

private theorem h16CenteredTransportGapDeterminant_pos_of_support_fourth
    {N : ℕ} {v : ComplexUnitSphere N} {t : ℝ}
    {x : ComplexSymmetricCoordinates N}
    (hx : x ∈ h16CenteredTransportSupport v t) :
    0 < h16CenteredTransportGapDeterminant v t x := by
  apply h16COECoordinateGapDeterminant_pos
  simpa [h16CenteredTransportSupport] using hx

/-- Away from the base coordinate-support frontier, the sharp pointwise
`3 -> 4` derivative holds at time zero. -/
theorem h16CenteredTransportJet_three_hasDerivAt_zero_of_not_frontier
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N)
    (hxfrontier : x ∉ frontier
      {y : ComplexSymmetricCoordinates N |
        coeCornerSupport (complexSymmetricMatrixOfCoordinates y)}) :
    HasDerivAt
      (fun t : ℝ ↦ h16CenteredTransportJet N K 3 v t x)
      (h16CenteredTransportJet N K 4 v 0 x) 0 := by
  let S : Set (ComplexSymmetricCoordinates N) :=
    {y | coeCornerSupport (complexSymmetricMatrixOfCoordinates y)}
  have hopen : IsOpen S := by
    let L := complexSymmetricMatrixOfCoordinatesCLMScratch N
    have hpreimage : S = L ⁻¹' Metric.ball (0 : ConcreteMatrixState N) 1 := by
      ext y
      change coeCornerSupport (complexSymmetricMatrixOfCoordinates y) ↔
        dist (L y) 0 < 1
      rw [coeCornerSupport_iff_cstar_norm_lt_one_scratch hN]
      rw [dist_zero_right]
      change ‖complexSymmetricMatrixOfCoordinates y‖ < 1 ↔
        ‖complexSymmetricMatrixOfCoordinates y‖ < 1
      rfl
    rw [hpreimage]
    exact Metric.isOpen_ball.preimage L.continuous
  have hflow : Continuous (fun t : ℝ ↦
      h16CenteredCoordinateFlow v (-t) x) := by
    have hparam : Continuous (fun t : ℝ ↦
        (((v, -t), x) : (ComplexUnitSphere N × ℝ) ×
          ComplexSymmetricCoordinates N)) := by
      fun_prop
    have hall : Continuous (fun p :
        (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
          h16CenteredCoordinateFlow p.1.1 p.1.2 p.2) :=
      continuous_h16CenteredCoordinateFlow_allParameters (N := N) hN
    change Continuous
      ((fun p : (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N ↦
          h16CenteredCoordinateFlow p.1.1 p.1.2 p.2) ∘
        (fun t : ℝ ↦ (((v, -t), x) :
          (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N)))
    exact hall.comp hparam
  by_cases hx : x ∈ S
  · have hsupport : x ∈ h16CenteredTransportSupport v 0 := by
      simpa [S, h16CenteredTransportSupport] using hx
    have hev : ∀ᶠ t in 𝓝 0,
        x ∈ h16CenteredTransportSupport v t := by
      have hline : Continuous (fun t : ℝ ↦
          (((v, t), x) : H16CenteredJointParameter N)) := by
        fun_prop
      have hjoint : (((v, 0), x) : H16CenteredJointParameter N) ∈
          h16CenteredJointSupport N := by
        simpa [h16CenteredJointSupport] using hsupport
      have hevent := hline.continuousAt.eventually
        ((isOpen_h16CenteredJointSupport hN).mem_nhds hjoint)
      filter_upwards [hevent] with t ht
      simpa [h16CenteredJointSupport] using ht
    let raw : ℝ → ℝ := fun t ↦ iteratedDeriv 3
      (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) t
    have hraw : HasDerivAt raw
        (iteratedDeriv 4
          (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) 0) 0 := by
      exact h16CenteredTransportInteriorJet_three_hasDerivAt
        (N := N) (K := K) hN v x 0
        (h16CenteredTransportGapDeterminant_pos_of_support_fourth
          (N := N) hsupport)
    have heq : (fun t : ℝ ↦ h16CenteredTransportJet N K 3 v t x)
        =ᶠ[𝓝 0] raw := by
      filter_upwards [hev] with t ht
      simp [h16CenteredTransportJet, ht, raw]
    have hnext : h16CenteredTransportJet N K 4 v 0 x =
        iteratedDeriv 4
          (fun s : ℝ ↦ h16CenteredTransportInteriorDensity N K v s x) 0 := by
      simp [h16CenteredTransportJet, hsupport]
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv hnext.symm
  · have hxclosure : x ∉ closure S := by
      intro hxc
      apply hxfrontier
      change x ∈ frontier S
      exact ⟨hxc, by simpa [hopen.interior_eq] using hx⟩
    have houtOpen : IsOpen ((closure S)ᶜ) := isClosed_closure.isOpen_compl
    have hxout : x ∈ (closure S)ᶜ := by simpa using hxclosure
    have hevent : ∀ᶠ t in 𝓝 0,
        h16CenteredCoordinateFlow v (-t) x ∈ (closure S)ᶜ := by
      have hflow0 : h16CenteredCoordinateFlow v (-0) x ∈ (closure S)ᶜ := by
        simpa using hxout
      exact hflow.continuousAt.eventually (houtOpen.mem_nhds hflow0)
    have hev : ∀ᶠ t in 𝓝 0,
        x ∉ h16CenteredTransportSupport v t := by
      filter_upwards [hevent] with t ht
      intro hs
      have hmem : h16CenteredCoordinateFlow v (-t) x ∈ S := by
        simpa [S, h16CenteredTransportSupport] using hs
      exact ht (subset_closure hmem)
    have heq : (fun t : ℝ ↦ h16CenteredTransportJet N K 3 v t x)
        =ᶠ[𝓝 0] (fun _ ↦ 0) := by
      filter_upwards [hev] with t ht
      exact h16CenteredTransportJet_zero_off_support (K := K) 3 v t x ht
    have hsupportNot : x ∉ h16CenteredTransportSupport v 0 := by
      simpa [S, h16CenteredTransportSupport] using hx
    have hnext : h16CenteredTransportJet N K 4 v 0 x = 0 :=
      h16CenteredTransportJet_zero_off_support (K := K) 4 v 0 x hsupportNot
    exact ((hasDerivAt_const (x := 0) (c := (0 : ℝ))).congr_of_eventuallyEq heq).congr_deriv
      hnext.symm

/-- The sharp pointwise `3 -> 4` derivative holds for almost every coordinate;
the only discarded set is the convex matrix-ball frontier. -/
theorem h16CenteredTransportJet_three_hasDerivAt_zero_ae
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    ∀ᵐ x ∂complexSymmetricCoordinateVolume N,
      HasDerivAt
        (fun t : ℝ ↦ h16CenteredTransportJet N K 3 v t x)
        (h16CenteredTransportJet N K 4 v 0 x) 0 := by
  classical
  have hnull := measure_h16COECoordinateSupport_frontier_zero hN
  filter_upwards [show ∀ᵐ x ∂complexSymmetricCoordinateVolume N,
      x ∉ frontier {y : ComplexSymmetricCoordinates N |
        coeCornerSupport (complexSymmetricMatrixOfCoordinates y)} by
    simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hnull] with x hx
  exact h16CenteredTransportJet_three_hasDerivAt_zero_of_not_frontier hN v x hx

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
