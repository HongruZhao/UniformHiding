import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantLocalLowerJetContinuity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# The first direct H16 frontier derivative

This module proves the genuinely delicate pointwise part of the first lower
direct-`L1` slot.  At a moving-support frontier point the determinant gap is
zero.  The smooth ambient gap is `O(|h|)`, while the density exponent is at
least `7 / 2`; equivalently, the ambient real power has derivative zero at
the origin.  Its derivative remainder is therefore `o(|h|)`.  The literal
zero extension is pointwise dominated by that ambient remainder, even on the
side where the support indicator is zero.

No boundary-nullity, finite-perimeter, coarea, or Gauss--Green input is used.
-/

open Filter Set Asymptotics
open scoped ContDiff Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem h16CenteredGap_time_contDiff_direct
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

/-- At a joint frontier point, the order-zero literal determinant density has
the order-one literal jet as its time derivative.  The proof exposes the
frontier `o(|h|)` estimate rather than discarding the frontier as null. -/
theorem h16CenteredTransportJet_zero_hasDerivAt_on_jointFrontier
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    {p : H16CenteredJointParameter N}
    (hp : p ∈ frontier (h16CenteredJointSupport N)) :
    HasDerivAt
      (fun u : ℝ ↦ h16CenteredTransportJet N K 0 p.1.1 u p.2)
      (h16CenteredTransportJet N K 1 p.1.1 p.1.2 p.2)
      p.1.2 := by
  let q : ℝ → ℝ := fun u ↦
    h16CenteredTransportGapDeterminant p.1.1 u p.2
  let a : ℝ := (h16COECoordinateRawMass N K)⁻¹.toReal
  let G : ℝ → ℝ := fun u ↦
    a * (q u) ^ coeCornerDensityExponent N K
  let F : ℝ → ℝ := fun u ↦
    h16CenteredTransportJet N K 0 p.1.1 u p.2
  have hpnot : p ∉ h16CenteredJointSupport N := by
    intro hpmem
    exact Set.disjoint_left.1
      (disjoint_frontier_iff_isOpen.mpr (isOpen_h16CenteredJointSupport hN))
      hp hpmem
  have hsupportNot :
      p.2 ∉ h16CenteredTransportSupport p.1.1 p.1.2 := by
    simpa [h16CenteredJointSupport] using hpnot
  have hqzero : q p.1.2 = 0 := by
    exact h16CenteredTransportGap_zero_on_joint_frontier hN hp
  have hFzero : F p.1.2 = 0 := by
    exact h16CenteredTransportJet_zero_off_support
      (K := K) 0 p.1.1 p.1.2 p.2 hsupportNot
  have hnextzero :
      h16CenteredTransportJet N K 1 p.1.1 p.1.2 p.2 = 0 := by
    exact h16CenteredTransportJet_zero_off_support
      (K := K) 1 p.1.1 p.1.2 p.2 hsupportNot
  have hq : HasDerivAt q (deriv q p.1.2) p.1.2 := by
    exact ((h16CenteredGap_time_contDiff_direct hN p.1.1 p.2).differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hexponentOne :
      (1 : ℝ) ≤ coeCornerDensityExponent N K := by
    linarith [coe_boundary_exponent_ge_seven_halves hboundary]
  have hexponentSub :
      0 < coeCornerDensityExponent N K - 1 := by
    linarith [coe_boundary_exponent_ge_seven_halves hboundary]
  have hpower : HasDerivAt
      (fun u : ℝ ↦ (q u) ^ coeCornerDensityExponent N K) 0 p.1.2 := by
    convert hq.rpow_const (Or.inr hexponentOne) using 1
    simp [hqzero, Real.zero_rpow hexponentSub.ne']
  have hG : HasDerivAt G 0 p.1.2 := by
    simpa [G] using hpower.const_mul a
  have hGzero : G p.1.2 = 0 := by
    simp [G, hqzero, Real.zero_rpow
      (show coeCornerDensityExponent N K ≠ 0 by linarith [hexponentOne])]
  have hFG : F =O[𝓝 p.1.2] G := by
    apply IsBigO.of_bound 1
    filter_upwards [] with u
    by_cases hu : p.2 ∈ h16CenteredTransportSupport p.1.1 u
    · simp [F, G, h16CenteredTransportJet, hu,
        h16CenteredTransportInteriorDensity, q, a]
    · have hzero := h16CenteredTransportJet_zero_off_support
        (N := N) (K := K) (r := (0 : Fin 5)) p.1.1 u p.2 hu
      simp [F, hzero]
  have hGo : G =o[𝓝 p.1.2] (fun u : ℝ ↦ u - p.1.2) := by
    simpa [hGzero] using hG.isLittleO
  have hFo : F =o[𝓝 p.1.2] (fun u : ℝ ↦ u - p.1.2) :=
    hFG.trans_isLittleO hGo
  have hderivZero : HasDerivAt F 0 p.1.2 := by
    apply HasDerivAt.of_isLittleO
    simpa [hFzero] using hFo
  simpa [F, hnextzero] using hderivZero

/-- The explicit frontier remainder estimate underlying the preceding
derivative theorem. -/
theorem h16CenteredTransportJet_zero_isLittleO_on_jointFrontier
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    {p : H16CenteredJointParameter N}
    (hp : p ∈ frontier (h16CenteredJointSupport N)) :
    (fun u : ℝ ↦
      h16CenteredTransportJet N K 0 p.1.1 u p.2 -
        h16CenteredTransportJet N K 0 p.1.1 p.1.2 p.2) =o[𝓝 p.1.2]
      (fun u : ℝ ↦ u - p.1.2) := by
  have hpnot : p ∉ h16CenteredJointSupport N := by
    intro hpmem
    exact Set.disjoint_left.1
      (disjoint_frontier_iff_isOpen.mpr (isOpen_h16CenteredJointSupport hN))
      hp hpmem
  have hsupportNot :
      p.2 ∉ h16CenteredTransportSupport p.1.1 p.1.2 := by
    simpa [h16CenteredJointSupport] using hpnot
  have hzero :
      h16CenteredTransportJet N K 0 p.1.1 p.1.2 p.2 = 0 :=
    h16CenteredTransportJet_zero_off_support
      (K := K) 0 p.1.1 p.1.2 p.2 hsupportNot
  have hnextzero :
      h16CenteredTransportJet N K 1 p.1.1 p.1.2 p.2 = 0 :=
    h16CenteredTransportJet_zero_off_support
      (K := K) 1 p.1.1 p.1.2 p.2 hsupportNot
  have hd := h16CenteredTransportJet_zero_hasDerivAt_on_jointFrontier
    (N := N) (K := K) hN hboundary hp
  have hd0 := hd.congr_deriv hnextzero
  simpa [hzero] using hd0.isLittleO

private theorem h16CenteredTransportGapDeterminant_pos_of_support_direct
    {N : ℕ} {v : ComplexUnitSphere N} {t : ℝ}
    {x : ComplexSymmetricCoordinates N}
    (hx : x ∈ h16CenteredTransportSupport v t) :
    0 < h16CenteredTransportGapDeterminant v t x := by
  apply h16COECoordinateGapDeterminant_pos
  simpa [h16CenteredTransportSupport] using hx

/-- The first literal lower-jet derivative holds at every coordinate, not
merely almost everywhere.  Interior points use ordinary smooth calculus,
points outside the closed support are locally zero, and frontier points use
the explicit `o(|h|)` estimate above. -/
theorem h16CenteredTransportJet_zero_hasDerivAt
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦ h16CenteredTransportJet N K 0 v u x)
      (h16CenteredTransportJet N K 1 v t x) t := by
  let p : H16CenteredJointParameter N := ((v, t), x)
  let S := h16CenteredJointSupport N
  have hopen : IsOpen S := isOpen_h16CenteredJointSupport hN
  have hline : Continuous (fun u : ℝ ↦
      (((v, u), x) : H16CenteredJointParameter N)) := by
    fun_prop
  by_cases hin : p ∈ S
  · have hsupport : x ∈ h16CenteredTransportSupport v t := by
      simpa [p, S, h16CenteredJointSupport] using hin
    have hev : ∀ᶠ u in 𝓝 t,
        x ∈ h16CenteredTransportSupport v u := by
      have hevent := hline.continuousAt.eventually (hopen.mem_nhds hin)
      filter_upwards [hevent] with u hu
      simpa [p, S, h16CenteredJointSupport] using hu
    let raw : ℝ → ℝ := fun u ↦
      h16CenteredTransportInteriorDensity N K v u x
    have hqdiff : DifferentiableAt ℝ
        (fun u : ℝ ↦ h16CenteredTransportGapDeterminant v u x) t :=
      ((h16CenteredGap_time_contDiff_direct hN v x).differentiable
        (by simp)).differentiableAt
    have hqpos : 0 < h16CenteredTransportGapDeterminant v t x :=
      h16CenteredTransportGapDeterminant_pos_of_support_direct hsupport
    have hrawdiff : DifferentiableAt ℝ raw t := by
      unfold raw h16CenteredTransportInteriorDensity
      exact (differentiableAt_const
        ((h16COECoordinateRawMass N K)⁻¹.toReal)).mul
        (hqdiff.rpow_const (Or.inl hqpos.ne'))
    have hraw : HasDerivAt raw (iteratedDeriv 1 raw t) t := by
      simpa only [iteratedDeriv_one] using hrawdiff.hasDerivAt
    have heq : (fun u : ℝ ↦ h16CenteredTransportJet N K 0 v u x)
        =ᶠ[𝓝 t] raw := by
      filter_upwards [hev] with u hu
      simp [h16CenteredTransportJet, hu, raw]
    have hnext : h16CenteredTransportJet N K 1 v t x =
        iteratedDeriv 1 raw t := by
      simp [h16CenteredTransportJet, hsupport, raw]
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv hnext.symm
  · by_cases hclosure : p ∈ closure S
    · have hpfrontier : p ∈ frontier S := by
        refine ⟨hclosure, ?_⟩
        simpa [hopen.interior_eq] using hin
      simpa [p, S] using
        (h16CenteredTransportJet_zero_hasDerivAt_on_jointFrontier
          (N := N) (K := K) hN hboundary hpfrontier)
    · have houtOpen : IsOpen ((closure S)ᶜ) := isClosed_closure.isOpen_compl
      have hpout : p ∈ (closure S)ᶜ := by simpa using hclosure
      have hevent := hline.continuousAt.eventually (houtOpen.mem_nhds hpout)
      have hev : ∀ᶠ u in 𝓝 t,
          x ∉ h16CenteredTransportSupport v u := by
        filter_upwards [hevent] with u hu
        intro hsupport
        have hmem : (((v, u), x) : H16CenteredJointParameter N) ∈ S := by
          simpa [S, h16CenteredJointSupport] using hsupport
        exact hu (subset_closure hmem)
      have heq : (fun u : ℝ ↦ h16CenteredTransportJet N K 0 v u x)
          =ᶠ[𝓝 t] (fun _ ↦ 0) := by
        filter_upwards [hev] with u hu
        exact h16CenteredTransportJet_zero_off_support
          (K := K) 0 v u x hu
      have hsupportNot : x ∉ h16CenteredTransportSupport v t := by
        simpa [p, S, h16CenteredJointSupport] using hin
      have hnext : h16CenteredTransportJet N K 1 v t x = 0 :=
        h16CenteredTransportJet_zero_off_support
          (K := K) 1 v t x hsupportNot
      exact ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq).congr_deriv
        hnext.symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
