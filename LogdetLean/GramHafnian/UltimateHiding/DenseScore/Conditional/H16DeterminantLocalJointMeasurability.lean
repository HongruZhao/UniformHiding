import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantLocalObligations
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantJetAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Tactic

/-!
# Joint measurability of the literal fourth centered determinant jet

This module isolates the non-boundary-measure part of the H16 determinant
obligations.  The proof uses the smooth ambient determinant gap and the
one-variable Faà di Bruno formula.  No Gauss--Green or coarea input occurs.
-/

open MeasureTheory
open scoped ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private abbrev H16AmbientGapParameter (N : ℕ) :=
  EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N

private def h16AmbientTimeDirection (N : ℕ) :
    (H16AmbientGapParameter N × ℝ) := (0, 1)

private def h16AmbientGapTimeJet (N r : ℕ)
    (p : H16AmbientGapParameter N × ℝ) : ℝ :=
  (iteratedFDeriv ℝ r (h16AmbientTransportGap N) p :
      (Fin r → (H16AmbientGapParameter N × ℝ)) → ℝ)
    (fun _ ↦ h16AmbientTimeDirection N)

private theorem continuous_h16AmbientGapTimeJet (N r : ℕ) :
    Continuous (h16AmbientGapTimeJet N r) := by
  unfold h16AmbientGapTimeJet
  exact ((contDiff_h16AmbientTransportGap N).continuous_iteratedFDeriv
      (mod_cast le_top)).eval continuous_const

private def h16TimeLine (N : ℕ) :
    ℝ →L[ℝ] (H16AmbientGapParameter N × ℝ) :=
  (0 : ℝ →L[ℝ] H16AmbientGapParameter N).prod
    (ContinuousLinearMap.id ℝ ℝ)

private theorem h16TimeLine_apply (N : ℕ) (t : ℝ) :
    h16TimeLine N t = (0, t) := by
  rfl

private theorem h16AmbientGapTimeJet_eq_iteratedDeriv
    (N r : ℕ) (q : H16AmbientGapParameter N) (t : ℝ) :
    h16AmbientGapTimeJet N r (q, t) =
      iteratedDeriv r (fun u : ℝ ↦ h16AmbientTransportGap N (q, u)) t := by
  let L := h16TimeLine N
  let a : H16AmbientGapParameter N × ℝ := (q, 0)
  let g : (H16AmbientGapParameter N × ℝ) → ℝ :=
    fun z ↦ h16AmbientTransportGap N (a + z)
  have hg : ContDiff ℝ ∞ g := by
    exact (contDiff_h16AmbientTransportGap N).comp
      (contDiff_const.add contDiff_id)
  have hsection :
      (fun u : ℝ ↦ h16AmbientTransportGap N (q, u)) = g ∘ L := by
    funext u
    simp [g, a, L, h16TimeLine]
  have hcomp := L.iteratedFDeriv_comp_right
    hg t (i := r) (mod_cast le_top)
  have hshift : iteratedFDeriv ℝ r g (L t) =
      iteratedFDeriv ℝ r (h16AmbientTransportGap N) (a + L t) := by
    exact iteratedFDeriv_comp_add_left r a (L t)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hsection, hcomp, hshift]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp [h16AmbientGapTimeJet, h16AmbientTimeDirection, a, L,
    h16TimeLine]

def h16CenteredGapTimeJet (N r : ℕ)
    (p : (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N) : ℝ :=
  iteratedDeriv r
    (fun u : ℝ ↦ h16CenteredTransportGapDeterminant p.1.1 u p.2)
    p.1.2

private theorem h16CenteredGapTimeJet_eq_ambient
    {N : ℕ} (hN : 1 ≤ N) (r : ℕ)
    (p : (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N) :
    h16CenteredGapTimeJet N r p =
      h16AmbientGapTimeJet N r ((p.1.1.1, p.2), p.1.2) := by
  unfold h16CenteredGapTimeJet
  rw [h16AmbientGapTimeJet_eq_iteratedDeriv]
  congr 1
  funext u
  exact h16CenteredTransportGap_eq_ambient hN p.1.1 u p.2

theorem continuous_h16CenteredGapTimeJet
    {N : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    Continuous (h16CenteredGapTimeJet N r) := by
  have hm : Continuous (fun p : (ComplexUnitSphere N × ℝ) ×
      ComplexSymmetricCoordinates N ↦ ((p.1.1.1, p.2), p.1.2)) := by
    fun_prop
  exact ((continuous_h16AmbientGapTimeJet N r).comp hm).congr
    (fun p ↦ (h16CenteredGapTimeJet_eq_ambient hN r p).symm)

private theorem measurableSet_h16CenteredTransportSupport_joint
    {N : ℕ} (hN : 1 ≤ N) :
    MeasurableSet {p : (ComplexUnitSphere N × ℝ) ×
        ComplexSymmetricCoordinates N |
      p.2 ∈ h16CenteredTransportSupport p.1.1 p.1.2} := by
  have hflow : Continuous (fun p : (ComplexUnitSphere N × ℝ) ×
      ComplexSymmetricCoordinates N ↦
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
  exact (measurableSet_coeCornerSupport N).preimage
    ((measurable_complexSymmetricMatrixOfCoordinates N).comp hflow.measurable)

def h16CenteredInteriorJetFormula
    (N K r : ℕ)
    (p : (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N) : ℝ :=
  (h16COECoordinateRawMass N K)⁻¹.toReal *
    ∑ c : OrderedFinpartition r,
      iteratedDeriv c.length
          (fun z : ℝ ↦ z ^ coeCornerDensityExponent N K)
          (h16CenteredTransportGapDeterminant p.1.1 p.1.2 p.2) *
        ∏ j, h16CenteredGapTimeJet N (c.partSize j) p

private theorem h16CenteredTransportGapDeterminant_pos_of_support
    {N : ℕ} {p : (ComplexUnitSphere N × ℝ) ×
        ComplexSymmetricCoordinates N}
    (hp : p.2 ∈ h16CenteredTransportSupport p.1.1 p.1.2) :
    0 < h16CenteredTransportGapDeterminant p.1.1 p.1.2 p.2 := by
  apply h16COECoordinateGapDeterminant_pos
  simpa [h16CenteredTransportSupport] using hp

private theorem h16CenteredGap_time_contDiff
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

theorem h16CenteredTransportInteriorJet_eq_formula_of_support
    {N K r : ℕ} (hN : 1 ≤ N)
    (p : (ComplexUnitSphere N × ℝ) × ComplexSymmetricCoordinates N)
    (hp : p.2 ∈ h16CenteredTransportSupport p.1.1 p.1.2) :
    iteratedDeriv r
        (fun u : ℝ ↦ h16CenteredTransportInteriorDensity
          N K p.1.1 u p.2) p.1.2 =
      h16CenteredInteriorJetFormula N K r p := by
  have hgapPos : 0 < h16CenteredTransportGapDeterminant
      p.1.1 p.1.2 p.2 :=
    h16CenteredTransportGapDeterminant_pos_of_support hp
  have houter : ContDiffAt ℝ r
      (fun z : ℝ ↦ z ^ coeCornerDensityExponent N K)
      (h16CenteredTransportGapDeterminant p.1.1 p.1.2 p.2) :=
    Real.contDiffAt_rpow_const_of_ne hgapPos.ne'
  have hinner : ContDiffAt ℝ r
      (fun u : ℝ ↦ h16CenteredTransportGapDeterminant p.1.1 u p.2)
      p.1.2 :=
    (h16CenteredGap_time_contDiff hN p.1.1 p.2).contDiffAt.of_le
      (mod_cast le_top)
  unfold h16CenteredTransportInteriorDensity
    h16CenteredInteriorJetFormula
  rw [iteratedDeriv_const_mul_field]
  change (h16COECoordinateRawMass N K)⁻¹.toReal *
      iteratedDeriv r
        ((fun z : ℝ ↦ z ^ coeCornerDensityExponent N K) ∘
          fun u : ℝ ↦ h16CenteredTransportGapDeterminant p.1.1 u p.2)
        p.1.2 = _
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition houter hinner le_rfl]
  congr 1

private theorem measurable_iteratedDeriv_rpow
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) (r : ℕ) :
    Measurable (iteratedDeriv r
      (fun z : ℝ ↦ z ^ coeCornerDensityExponent N K)) := by
  induction r with
  | zero =>
      rw [iteratedDeriv_zero]
      apply (Real.continuous_rpow_const ?_).measurable
      linarith [coe_boundary_exponent_ge_seven_halves hboundary]
  | succ r _ih =>
      rw [iteratedDeriv_succ]
      exact measurable_deriv _

private theorem measurable_h16CenteredInteriorJetFormula
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (r : ℕ) :
    Measurable (h16CenteredInteriorJetFormula N K r) := by
  unfold h16CenteredInteriorJetFormula
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro c hc
  apply Measurable.mul
  · apply (measurable_iteratedDeriv_rpow hboundary c.length).comp
    have hzero := continuous_h16CenteredGapTimeJet hN 0
    change Continuous (fun p : (ComplexUnitSphere N × ℝ) ×
      ComplexSymmetricCoordinates N ↦
        h16CenteredTransportGapDeterminant p.1.1 p.1.2 p.2) at hzero
    exact hzero.measurable
  · apply Finset.measurable_prod
    intro j hj
    exact (continuous_h16CenteredGapTimeJet hN (c.partSize j)).measurable

theorem measurable_h16CenteredTransportJet_four
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) :
    Measurable (fun p : (ComplexUnitSphere N × ℝ) ×
        ComplexSymmetricCoordinates N ↦
      h16CenteredTransportJet N K 4 p.1.1 p.1.2 p.2) := by
  classical
  let S : Set ((ComplexUnitSphere N × ℝ) ×
      ComplexSymmetricCoordinates N) :=
    {p | p.2 ∈ h16CenteredTransportSupport p.1.1 p.1.2}
  have hS : MeasurableSet S :=
    measurableSet_h16CenteredTransportSupport_joint hN
  have hformula : (fun p : (ComplexUnitSphere N × ℝ) ×
      ComplexSymmetricCoordinates N ↦
      h16CenteredTransportJet N K 4 p.1.1 p.1.2 p.2) =
      fun p ↦ if p ∈ S then
        h16CenteredInteriorJetFormula N K 4 p else 0 := by
    funext p
    by_cases hp : p ∈ S
    · simp only [hp, if_true, S]
      rw [h16CenteredTransportJet]
      split
      · exact h16CenteredTransportInteriorJet_eq_formula_of_support
          hN p hp
      · contradiction
    · simp only [hp, if_false, S]
      exact h16CenteredTransportJet_zero_off_support 4 p.1.1 p.1.2 p.2 hp
  rw [hformula]
  exact Measurable.ite hS
    (measurable_h16CenteredInteriorJetFormula hN hboundary 4)
    measurable_const

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
