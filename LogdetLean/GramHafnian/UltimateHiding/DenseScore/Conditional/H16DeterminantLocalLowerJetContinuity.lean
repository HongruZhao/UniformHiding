import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantLocalJointMeasurability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16A5GapBoundaryVanishing
import Mathlib.Topology.Piecewise
import Mathlib.Tactic

/-!
# Continuity of the literal H16 centered determinant jets through order three

For orders at most three, the Faà di Bruno extension has only positive
boundary powers.  It is therefore globally continuous and vanishes on the
frontier of the exact positive-definite support.  This proves continuity of
the literal zero extension without any Gauss--Green or coarea input.
-/

open Set
open scoped ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

abbrev H16CenteredJointParameter (N : ℕ) :=
  (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N

def h16CenteredJointSupport (N : ℕ) :
    Set (H16CenteredJointParameter N) :=
  {p | p.2 ∈ h16CenteredTransportSupport p.1.1 p.1.2}

def h16CenteredInverseFlowEuc (N : ℕ) :
    H16CenteredJointParameter N → H16EuclideanCoordinateSpace N :=
  fun p ↦ h16CoordinateEuclideanEquiv N
    (h16CenteredCoordinateFlow p.1.1 (-p.1.2) p.2)

private theorem continuous_h16CenteredInverseFlowCoordinates_joint
    {N : ℕ} (hN : 1 ≤ N) :
    Continuous (fun p : H16CenteredJointParameter N ↦
      h16CenteredCoordinateFlow p.1.1 (-p.1.2) p.2) := by
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

theorem continuous_h16CenteredInverseFlowEuc
    {N : ℕ} (hN : 1 ≤ N) :
    Continuous (h16CenteredInverseFlowEuc N) := by
  exact (h16CoordinateEuclideanEquiv N).continuous.comp
    (continuous_h16CenteredInverseFlowCoordinates_joint hN)

theorem h16CenteredJointSupport_eq_preimage_eucSupport
    {N : ℕ} :
    h16CenteredJointSupport N =
      h16CenteredInverseFlowEuc N ⁻¹' h16EucSupport N := by
  ext p
  simp [h16CenteredJointSupport, h16CenteredInverseFlowEuc,
    h16CenteredTransportSupport, h16EucSupport]

theorem isOpen_h16CenteredJointSupport
    {N : ℕ} (hN : 1 ≤ N) :
    IsOpen (h16CenteredJointSupport N) := by
  rw [h16CenteredJointSupport_eq_preimage_eucSupport]
  exact (isOpen_h16EucSupport N).preimage
    (continuous_h16CenteredInverseFlowEuc hN)

theorem h16CenteredTransportGap_eq_eucGap
    {N : ℕ} (p : H16CenteredJointParameter N) :
    h16CenteredTransportGapDeterminant p.1.1 p.1.2 p.2 =
      h16EucGap N (h16CenteredInverseFlowEuc N p) := by
  simp [h16CenteredInverseFlowEuc, h16EucGap,
    h16COECoordinateGapDeterminant,
    h16CenteredTransportGapDeterminant]

theorem h16CenteredTransportGap_zero_on_joint_frontier
    {N : ℕ} (hN : 1 ≤ N)
    {p : H16CenteredJointParameter N}
    (hp : p ∈ frontier (h16CenteredJointSupport N)) :
    h16CenteredTransportGapDeterminant p.1.1 p.1.2 p.2 = 0 := by
  let y := h16CenteredInverseFlowEuc N p
  have hpnot : p ∉ h16CenteredJointSupport N := by
    intro hpmem
    exact Set.disjoint_left.1
      (disjoint_frontier_iff_isOpen.mpr (isOpen_h16CenteredJointSupport hN))
      hp hpmem
  have hymap : MapsTo (h16CenteredInverseFlowEuc N)
      (h16CenteredJointSupport N) (h16EucSupport N) := by
    intro q hq
    rw [h16CenteredJointSupport_eq_preimage_eucSupport] at hq
    exact hq
  have hyclosure : y ∈ closure (h16EucSupport N) := by
    exact map_mem_closure
      (f := h16CenteredInverseFlowEuc N)
      (s := h16CenteredJointSupport N)
      (t := h16EucSupport N)
      (continuous_h16CenteredInverseFlowEuc hN) hp.1 hymap
  have hynot : y ∉ h16EucSupport N := by
    intro hy
    apply hpnot
    rw [h16CenteredJointSupport_eq_preimage_eucSupport]
    exact hy
  have hyfrontier : y ∈ frontier (h16EucSupport N) := by
    exact ⟨hyclosure, fun hyinterior ↦ hynot (interior_subset hyinterior)⟩
  rw [h16CenteredTransportGap_eq_eucGap]
  exact h16EucGap_boundaryVanishing N y hyfrontier

private theorem continuous_iteratedDeriv_rpow_through_three
    {N K r s : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 3) (hs : s ≤ r) :
    Continuous (iteratedDeriv s
      (fun z : ℝ ↦ z ^ coeCornerDensityExponent N K)) := by
  have hexponent : 0 ≤ coeCornerDensityExponent N K - (s : ℝ) := by
    have hs3 : s ≤ 3 := hs.trans hr
    have hsR : (s : ℝ) ≤ 3 := by exact_mod_cast hs3
    linarith [coe_boundary_exponent_ge_seven_halves hboundary]
  have heq : iteratedDeriv s
      (fun z : ℝ ↦ z ^ coeCornerDensityExponent N K) =
      fun z : ℝ ↦ (descPochhammer ℝ s).eval
          (coeCornerDensityExponent N K) *
        z ^ (coeCornerDensityExponent N K - s) := by
    funext z
    rw [iteratedDeriv_eq_iterate]
    exact Real.iter_deriv_rpow_const
      (coeCornerDensityExponent N K) z s
  rw [heq]
  exact continuous_const.mul (Real.continuous_rpow_const hexponent)

theorem continuous_h16CenteredInteriorJetFormula_through_three
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 3) :
    Continuous (h16CenteredInteriorJetFormula N K r) := by
  unfold h16CenteredInteriorJetFormula
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro c hc
  apply Continuous.mul
  · exact (continuous_iteratedDeriv_rpow_through_three hboundary hr c.length_le).comp
      (by
        have hzero := continuous_h16CenteredGapTimeJet hN 0
        change Continuous (fun p : H16CenteredJointParameter N ↦
          h16CenteredTransportGapDeterminant p.1.1 p.1.2 p.2) at hzero
        exact hzero)
  · apply continuous_finsetProd
    intro j hj
    exact continuous_h16CenteredGapTimeJet hN (c.partSize j)

theorem h16CenteredInteriorJetFormula_zero_of_gap_zero
    {N K r : ℕ} (hboundary : 2 * N + 8 ≤ K) (hr : r ≤ 3)
    {p : H16CenteredJointParameter N}
    (hgap : h16CenteredTransportGapDeterminant p.1.1 p.1.2 p.2 = 0) :
    h16CenteredInteriorJetFormula N K r p = 0 := by
  unfold h16CenteredInteriorJetFormula
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro c hc
  have hlen : c.length ≤ 3 := c.length_le.trans hr
  have hexponent : 0 < coeCornerDensityExponent N K - (c.length : ℝ) := by
    have hlenR : (c.length : ℝ) ≤ 3 := by exact_mod_cast hlen
    linarith [coe_boundary_exponent_ge_seven_halves hboundary]
  have houter : iteratedDeriv c.length
      (fun z : ℝ ↦ z ^ coeCornerDensityExponent N K) 0 = 0 := by
    rw [iteratedDeriv_eq_iterate,
      Real.iter_deriv_rpow_const,
      Real.zero_rpow hexponent.ne']
    ring
  rw [hgap, houter, zero_mul]

theorem continuous_h16CenteredTransportJet_through_three
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : Fin 4) :
    Continuous (fun p : H16CenteredJointParameter N ↦
      h16CenteredTransportJet N K r.castSucc p.1.1 p.1.2 p.2) := by
  classical
  let S := h16CenteredJointSupport N
  let F := h16CenteredInteriorJetFormula N K (r : ℕ)
  have hr : (r : ℕ) ≤ 3 := by omega
  have hpiece : (fun p : H16CenteredJointParameter N ↦
      h16CenteredTransportJet N K r.castSucc p.1.1 p.1.2 p.2) =
      fun p ↦ if p ∈ S then F p else 0 := by
    funext p
    by_cases hp : p ∈ S
    · have hp' : p.2 ∈ h16CenteredTransportSupport p.1.1 p.1.2 := by
        simpa [S, h16CenteredJointSupport] using hp
      rw [if_pos hp]
      change h16CenteredTransportJet N K r.castSucc p.1.1 p.1.2 p.2 =
        h16CenteredInteriorJetFormula N K (r : ℕ) p
      rw [h16CenteredTransportJet, if_pos hp']
      simpa using
        (h16CenteredTransportInteriorJet_eq_formula_of_support
          (N := N) (K := K) (r := (r : ℕ)) hN p hp')
    · have hp' : p.2 ∉ h16CenteredTransportSupport p.1.1 p.1.2 := by
        simpa [S, h16CenteredJointSupport] using hp
      rw [if_neg hp]
      change h16CenteredTransportJet N K r.castSucc p.1.1 p.1.2 p.2 = 0
      exact h16CenteredTransportJet_zero_off_support
        (K := K) r.castSucc p.1.1 p.1.2 p.2 hp'
  rw [hpiece]
  apply Continuous.if
  · intro p hp
    apply h16CenteredInteriorJetFormula_zero_of_gap_zero hboundary hr
    exact h16CenteredTransportGap_zero_on_joint_frontier hN hp
  · exact continuous_h16CenteredInteriorJetFormula_through_three
      hN hboundary hr
  · exact continuous_const

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
