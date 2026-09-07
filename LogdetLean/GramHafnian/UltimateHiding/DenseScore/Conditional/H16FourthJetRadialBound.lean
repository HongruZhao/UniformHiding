import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16DeterminantLocalJointMeasurability
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# The determinant-local fourth-jet radial bound

This module proves the algebraic radial estimate left as a field of
`H16CenteredDeterminantLocalObligations`.  The fourth derivative is factored
as the sharp singular power `q ^ (alpha - 4)` times a coefficient continuous
on the compact product of the projective sphere and the closed unit
coordinate ball.  Compactness therefore supplies a uniform nonnegative
constant.  No integration, Gauss--Green theorem, or new axiom is used.
-/

open MeasureTheory Set NormedSpace
open scoped BigOperators ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private abbrev H16FourthGapParameter (N : ℕ) :=
  EuclideanSpace ℂ (Fin N) × ComplexSymmetricCoordinates N

private def h16FourthTimeDirection (N : ℕ) :
    H16FourthGapParameter N × ℝ :=
  (0, 1)

/-- The time-direction evaluation of the ambient iterated Frechet derivative
of the determinant gap. -/
def h16AmbientGapTimeJet (N r : ℕ)
    (p : H16FourthGapParameter N × ℝ) : ℝ :=
  (iteratedFDeriv ℝ r (h16AmbientTransportGap N) p :
      (Fin r → (H16FourthGapParameter N × ℝ)) → ℝ)
    (fun _ ↦ h16FourthTimeDirection N)

theorem continuous_h16AmbientGapTimeJet (N r : ℕ) :
    Continuous (h16AmbientGapTimeJet N r) := by
  unfold h16AmbientGapTimeJet
  exact ((contDiff_h16AmbientTransportGap N).continuous_iteratedFDeriv
      (mod_cast le_top)).eval continuous_const

private def h16FourthTimeLine (N : ℕ) :
    ℝ →L[ℝ] (H16FourthGapParameter N × ℝ) :=
  (0 : ℝ →L[ℝ] H16FourthGapParameter N).prod
    (ContinuousLinearMap.id ℝ ℝ)

private theorem h16AmbientGapTimeJet_eq_iteratedDeriv
    (N r : ℕ) (q : H16FourthGapParameter N) (t : ℝ) :
    h16AmbientGapTimeJet N r (q, t) =
      iteratedDeriv r (fun u : ℝ ↦ h16AmbientTransportGap N (q, u)) t := by
  let L := h16FourthTimeLine N
  let a : H16FourthGapParameter N × ℝ := (q, 0)
  let g : (H16FourthGapParameter N × ℝ) → ℝ :=
    fun z ↦ h16AmbientTransportGap N (a + z)
  have hg : ContDiff ℝ ∞ g := by
    exact (contDiff_h16AmbientTransportGap N).comp
      (contDiff_const.add contDiff_id)
  have hsection :
      (fun u : ℝ ↦ h16AmbientTransportGap N (q, u)) = g ∘ L := by
    funext u
    simp [g, a, L, h16FourthTimeLine]
  have hcomp := L.iteratedFDeriv_comp_right
    hg t (i := r) (mod_cast le_top)
  have hshift : iteratedFDeriv ℝ r g (L t) =
      iteratedFDeriv ℝ r (h16AmbientTransportGap N) (a + L t) := by
    exact iteratedFDeriv_comp_add_left r a (L t)
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hsection, hcomp, hshift]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp [h16AmbientGapTimeJet, h16FourthTimeDirection, a, L,
    h16FourthTimeLine]

/-- The `r`-th raw determinant-gap time derivative at the base time. -/
def h16CenteredGapBaseTimeJet (N r : ℕ)
    (p : ComplexUnitSphere N × ComplexSymmetricCoordinates N) : ℝ :=
  iteratedDeriv r
    (fun u : ℝ ↦ h16CenteredTransportGapDeterminant p.1 u p.2) 0

theorem h16CenteredGapBaseTimeJet_eq_ambient
    {N : ℕ} (hN : 1 ≤ N) (r : ℕ)
    (p : ComplexUnitSphere N × ComplexSymmetricCoordinates N) :
    h16CenteredGapBaseTimeJet N r p =
      h16AmbientGapTimeJet N r ((p.1.1, p.2), 0) := by
  unfold h16CenteredGapBaseTimeJet
  rw [h16AmbientGapTimeJet_eq_iteratedDeriv]
  congr 1
  funext u
  exact h16CenteredTransportGap_eq_ambient hN p.1 u p.2

theorem continuous_h16CenteredGapBaseTimeJet
    {N : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    Continuous (h16CenteredGapBaseTimeJet N r) := by
  have hm : Continuous (fun p : ComplexUnitSphere N ×
      ComplexSymmetricCoordinates N ↦ ((p.1.1, p.2), (0 : ℝ))) := by
    fun_prop
  exact ((continuous_h16AmbientGapTimeJet N r).comp hm).congr
    (fun p ↦ (h16CenteredGapBaseTimeJet_eq_ambient hN r p).symm)

theorem h16CenteredTransportGapDeterminant_zero
    {N : ℕ} (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredTransportGapDeterminant v 0 x =
      h16COECoordinateGapDeterminant N x := by
  unfold h16CenteredTransportGapDeterminant
    h16COECoordinateGapDeterminant h16CenteredCoordinateFlow
  simp

@[simp]
theorem h16CenteredGapBaseTimeJet_zero
    {N : ℕ} (p : ComplexUnitSphere N × ComplexSymmetricCoordinates N) :
    h16CenteredGapBaseTimeJet N 0 p =
      h16COECoordinateGapDeterminant N p.2 := by
  simp [h16CenteredGapBaseTimeJet,
    h16CenteredTransportGapDeterminant_zero]

/-- After extracting `q ^ (alpha - 4)` from the fourth derivative, this is
the remaining nonsingular coefficient. -/
def h16FourthJetRadialCoefficient (N K : ℕ)
    (p : ComplexUnitSphere N × ComplexSymmetricCoordinates N) : ℝ :=
  (h16COECoordinateRawMass N K)⁻¹.toReal *
    ∑ c : OrderedFinpartition 4,
      (descPochhammer ℝ c.length).eval (coeCornerDensityExponent N K) *
        (h16COECoordinateGapDeterminant N p.2) ^ (4 - c.length) *
          ∏ j, h16CenteredGapBaseTimeJet N (c.partSize j) p

theorem continuous_h16FourthJetRadialCoefficient
    {N K : ℕ} (hN : 1 ≤ N) :
    Continuous (h16FourthJetRadialCoefficient N K) := by
  have hgap : Continuous (fun p : ComplexUnitSphere N ×
      ComplexSymmetricCoordinates N ↦
        h16COECoordinateGapDeterminant N p.2) := by
    exact (continuous_h16CenteredGapBaseTimeJet hN 0).congr
      (fun p ↦ h16CenteredGapBaseTimeJet_zero p)
  unfold h16FourthJetRadialCoefficient
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro c _hc
  apply Continuous.mul
  · exact continuous_const.mul (hgap.pow _)
  · apply continuous_finsetProd
    intro j _hj
    exact continuous_h16CenteredGapBaseTimeJet hN (c.partSize j)

private theorem h16CenteredTransportGap_time_contDiff
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

private theorem h16_iteratedDeriv_rpow_factor_four
    {q alpha : ℝ} (hq : 0 < q) (c : OrderedFinpartition 4) :
    iteratedDeriv c.length (fun z : ℝ ↦ z ^ alpha) q =
      (descPochhammer ℝ c.length).eval alpha *
        q ^ (alpha - 4) * q ^ (4 - c.length) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  have hlength : c.length ≤ 4 := OrderedFinpartition.length_le c
  have hexponent : alpha - (c.length : ℝ) =
      (alpha - 4) + ((4 - c.length : ℕ) : ℝ) := by
    rw [Nat.cast_sub hlength]
    push_cast
    ring
  rw [hexponent, Real.rpow_add_natCast hq.ne']
  ring

/-- Exact extraction of the sharp fourth-order determinant power from the
interior fourth derivative. -/
theorem h16CenteredTransportInteriorDensity_four_factor
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N)
    (hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)) :
    iteratedDeriv 4
        (fun u : ℝ ↦ h16CenteredTransportInteriorDensity N K v u x) 0 =
      h16FourthJetRadialCoefficient N K (v, x) *
        (h16COECoordinateGapDeterminant N x) ^
          (coeCornerDensityExponent N K - 4) := by
  let q := h16COECoordinateGapDeterminant N x
  let alpha := coeCornerDensityExponent N K
  have hq : 0 < q := h16COECoordinateGapDeterminant_pos hx
  have houter : ContDiffAt ℝ 4 (fun z : ℝ ↦ z ^ alpha) q :=
    Real.contDiffAt_rpow_const_of_ne hq.ne'
  have houter0 : ContDiffAt ℝ 4 (fun z : ℝ ↦ z ^ alpha)
      (h16CenteredTransportGapDeterminant v 0 x) := by
    simpa [q, h16CenteredTransportGapDeterminant_zero] using houter
  have hinner : ContDiffAt ℝ 4
      (fun u : ℝ ↦ h16CenteredTransportGapDeterminant v u x) 0 :=
    (h16CenteredTransportGap_time_contDiff hN v x).contDiffAt.of_le
      (WithTop.coe_le_coe.2 (show (4 : ℕ∞) ≤ ⊤ from le_top))
  unfold h16CenteredTransportInteriorDensity
  rw [iteratedDeriv_const_mul_field]
  change (h16COECoordinateRawMass N K)⁻¹.toReal *
      iteratedDeriv 4
        ((fun z : ℝ ↦ z ^ alpha) ∘
          fun u : ℝ ↦ h16CenteredTransportGapDeterminant v u x) 0 = _
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition
    houter0 hinner le_rfl]
  have hgapzero : h16CenteredTransportGapDeterminant v 0 x = q := by
    simpa [q] using h16CenteredTransportGapDeterminant_zero v x
  simp_rw [hgapzero, h16_iteratedDeriv_rpow_factor_four hq]
  unfold h16FourthJetRadialCoefficient
  change (h16COECoordinateRawMass N K)⁻¹.toReal *
      (∑ c : OrderedFinpartition 4,
        ((descPochhammer ℝ c.length).eval alpha *
            q ^ (alpha - 4) * q ^ (4 - c.length)) *
          ∏ j, h16CenteredGapBaseTimeJet N (c.partSize j) (v, x)) = _
  have hqzero : h16COECoordinateGapDeterminant N x = q := rfl
  rw [hqzero]
  have hsum :
      (∑ c : OrderedFinpartition 4,
        ((descPochhammer ℝ c.length).eval alpha *
            q ^ (alpha - 4) * q ^ (4 - c.length)) *
          ∏ j, h16CenteredGapBaseTimeJet N (c.partSize j) (v, x)) =
        q ^ (alpha - 4) *
          ∑ c : OrderedFinpartition 4,
            (descPochhammer ℝ c.length).eval alpha *
              q ^ (4 - c.length) *
                ∏ j, h16CenteredGapBaseTimeJet N (c.partSize j) (v, x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _hc
    ring
  rw [hsum]
  ring

/-- The zero-extended literal fourth jet has the same factorization, since
both sides vanish off the open determinant support. -/
theorem h16CenteredTransportJet_four_factor
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredTransportJet N K 4 v 0 x =
      h16FourthJetRadialCoefficient N K (v, x) *
        h16COEFourthRadialKernel N K x := by
  classical
  by_cases hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)
  · have hsupport : x ∈ h16CenteredTransportSupport v 0 := by
      simpa [h16CenteredTransportSupport] using hx
    rw [h16CenteredTransportJet, if_pos hsupport]
    change iteratedDeriv 4
        (fun u : ℝ ↦ h16CenteredTransportInteriorDensity N K v u x) 0 = _
    rw [h16CenteredTransportInteriorDensity_four_factor hN v x hx]
    unfold h16COEFourthRadialKernel
    rw [if_pos hx]
  · have hnotSupport : x ∉ h16CenteredTransportSupport v 0 := by
      simpa [h16CenteredTransportSupport] using hx
    rw [h16CenteredTransportJet_zero_off_support 4 v 0 x hnotSupport]
    unfold h16COEFourthRadialKernel
    rw [if_neg hx]
    ring

private theorem exists_h16FourthJetRadialCoefficient_bound
    {N K : ℕ} (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N),
        x ∈ Metric.closedBall 0 1 →
          ‖h16FourthJetRadialCoefficient N K (v, x)‖ ≤ C := by
  let ball : Set (ComplexSymmetricCoordinates N) := Metric.closedBall 0 1
  let F : ComplexUnitSphere N × ball → ℝ := fun p ↦
    ‖h16FourthJetRadialCoefficient N K (p.1, p.2.1)‖
  have hF : Continuous F := by
    let param : ComplexUnitSphere N × ball →
        ComplexUnitSphere N × ComplexSymmetricCoordinates N :=
      fun p ↦ (p.1, p.2.1)
    have hparam : Continuous param := by
      unfold param
      fun_prop
    have hcomp :=
      (continuous_h16FourthJetRadialCoefficient
        (N := N) (K := K) hN).comp hparam
    simpa only [F, param, Function.comp_apply] using hcomp.norm
  obtain ⟨C, hC⟩ := isCompact_univ.bddAbove_image hF.continuousOn
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro v x hx
  have hp : (v, ⟨x, hx⟩) ∈
      (Set.univ : Set (ComplexUnitSphere N × ball)) := Set.mem_univ _
  have hFC : F (v, ⟨x, hx⟩) ≤ C :=
    hC (Set.mem_image_of_mem F hp)
  have hFC' : ‖h16FourthJetRadialCoefficient N K (v, x)‖ ≤ C := by
    simpa only [F] using hFC
  exact hFC'.trans (le_max_left C 0)

/-- A canonical nonnegative compactness constant for the fourth radial
coefficient. -/
noncomputable def h16CenteredFourthJetRadialConstant
    (N K : ℕ) (hN : 1 ≤ N) : ℝ :=
  Classical.choose
    (exists_h16FourthJetRadialCoefficient_bound (N := N) (K := K) hN)

theorem h16CenteredFourthJetRadialConstant_nonnegative
    {N K : ℕ} (hN : 1 ≤ N) :
    0 ≤ h16CenteredFourthJetRadialConstant N K hN :=
  (Classical.choose_spec
    (exists_h16FourthJetRadialCoefficient_bound (N := N) (K := K) hN)).1

private theorem h16FourthJetRadialCoefficient_le_constant
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N)
    (hx : x ∈ Metric.closedBall 0 1) :
    ‖h16FourthJetRadialCoefficient N K (v, x)‖ ≤
      h16CenteredFourthJetRadialConstant N K hN :=
  (Classical.choose_spec
    (exists_h16FourthJetRadialCoefficient_bound (N := N) (K := K) hN)).2
      v x hx

/-- Pointwise, hence stronger than the almost-everywhere field requested in
`H16CenteredDeterminantLocalObligations`, fourth-jet radial estimate. -/
theorem h16CenteredTransportJet_four_radial_bound
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    ‖h16CenteredTransportJet N K 4 v 0 x‖ ≤
      h16CenteredFourthJetRadialConstant N K hN *
        h16COEFourthRadialKernel N K x := by
  classical
  by_cases hx : coeCornerSupport (complexSymmetricMatrixOfCoordinates x)
  · have hxball : x ∈ Metric.closedBall 0 1 :=
      h16COECoordinateSupport_subset_closedBall hx
    rw [h16CenteredTransportJet_four_factor hN]
    rw [norm_mul]
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (h16COEFourthRadialKernel_nonnegative N K x)]
    exact mul_le_mul_of_nonneg_right
      (h16FourthJetRadialCoefficient_le_constant hN v x hxball)
      (h16COEFourthRadialKernel_nonnegative N K x)
  · have hnotSupport : x ∉ h16CenteredTransportSupport v 0 := by
      simpa [h16CenteredTransportSupport] using hx
    rw [h16CenteredTransportJet_zero_off_support 4 v 0 x hnotSupport]
    unfold h16COEFourthRadialKernel
    simp [hx]

/-- The now-proved radial estimate, including the already proved joint
measurability, packaged in the exact structure used downstream. -/
noncomputable def h16CenteredFourthJetRadialEstimate_proved
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) :
    H16CenteredFourthJetRadialEstimate N K where
  constant := h16CenteredFourthJetRadialConstant N K hN
  constant_nonnegative :=
    h16CenteredFourthJetRadialConstant_nonnegative hN
  jet_aestronglyMeasurable := by
    intro v
    have hparam : Measurable
        (fun x : ComplexSymmetricCoordinates N ↦ (((v, (0 : ℝ))), x)) :=
      measurable_const.prodMk measurable_id
    exact ((measurable_h16CenteredTransportJet_four hN hboundary).comp
      hparam).aestronglyMeasurable
  jet_norm_le := by
    intro v
    exact ae_of_all _ fun x ↦
      h16CenteredTransportJet_four_radial_bound hN v x

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
