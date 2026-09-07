import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16AnalyticCriticalSet
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16SupportedRpowFTC

/-!
# Supported powers along real-analytic curves

An everywhere real-analytic scalar curve has either identically zero
derivative or only finitely many critical points on a compact interval.  The
finite case can be handled without explicitly sorting the critical points:
induct on any finite set containing them, split at the newly inserted point,
and concatenate interval integrability and the exact integral identity.

This file implements that argument.  In particular, a positive supported
power composed with an everywhere real-analytic scalar curve is absolutely
continuous on every compact interval.  Applied to the H16 determinant gap,
this removes the previously missing finite-monotonicity decomposition.
-/

open Filter MeasureTheory Set
open scoped Interval ContDiff Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- If the critical points of a smooth scalar path on an interval are covered
by a finite set, then the transported supported-power derivative is interval
integrable and satisfies the exact FTC identity.  The proof inducts on the
finite cover, splitting the interval at each inserted point. -/
theorem intervalIntegrable_and_integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_finite_critical_cover
    {β a b : ℝ} (hβ : 0 < β)
    {q q' : ℝ → ℝ}
    (hq : Continuous q)
    (hqq' : ∀ x, HasDerivAt q (q' x) x)
    (hq' : Continuous q')
    {S : Set ℝ} (hS : S.Finite)
    (hcrit : ∀ x ∈ Ioo (min a b) (max a b), q' x = 0 → x ∈ S) :
    IntervalIntegrable
        (fun x ↦ h16SupportedRpowDeriv β (q x) * q' x)
        volume a b ∧
      (∫ x in a..b, h16SupportedRpowDeriv β (q x) * q' x) =
        h16SupportedRpow β (q b) - h16SupportedRpow β (q a) := by
  induction S, hS using Set.Finite.induction_on generalizing a b with
  | empty =>
      have hne : ∀ x ∈ Ioo (min a b) (max a b), q' x ≠ 0 := by
        intro x hx hxzero
        simpa using hcrit x hx hxzero
      rcases isPreconnected_Ioo.mapsTo_Ioi_or_Iio
          hq'.continuousOn hne with hpos | hneg
      · have hnonneg : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ q' x := by
          intro x hx
          exact (hpos hx).le
        exact ⟨
          intervalIntegrable_h16SupportedRpowDeriv_comp_mul_of_deriv_nonneg
            hβ hq.continuousOn (fun x _ ↦ hqq' x) hnonneg,
          integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_deriv_nonneg
            hβ hq.continuousOn (fun x _ ↦ hqq' x) hnonneg⟩
      · have hnonpos : ∀ x ∈ Ioo (min a b) (max a b), q' x ≤ 0 := by
          intro x hx
          exact (hneg hx).le
        exact ⟨
          intervalIntegrable_h16SupportedRpowDeriv_comp_mul_of_deriv_nonpos
            hβ hq.continuousOn (fun x _ ↦ hqq' x) hnonpos,
          integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_deriv_nonpos
            hβ hq.continuousOn (fun x _ ↦ hqq' x) hnonpos⟩
  | @insert c S hcS hS ih =>
      by_cases hc : c ∈ Ioo (min a b) (max a b)
      · have hleft := ih (a := a) (b := c) (fun x hx hxzero ↦ by
          have hxmain : x ∈ Ioo (min a b) (max a b) := by
            simp only [mem_Ioo] at hc hx ⊢
            grind
          have hxinsert := hcrit x hxmain hxzero
          simp only [mem_insert_iff] at hxinsert
          rcases hxinsert with hxc | hxS
          · subst x
            simp only [mem_Ioo] at hx
            grind
          · exact hxS)
        have hright := ih (a := c) (b := b) (fun x hx hxzero ↦ by
          have hxmain : x ∈ Ioo (min a b) (max a b) := by
            simp only [mem_Ioo] at hc hx ⊢
            grind
          have hxinsert := hcrit x hxmain hxzero
          simp only [mem_insert_iff] at hxinsert
          rcases hxinsert with hxc | hxS
          · subst x
            simp only [mem_Ioo] at hx
            grind
          · exact hxS)
        refine ⟨hleft.1.trans hright.1, ?_⟩
        rw [← intervalIntegral.integral_add_adjacent_intervals hleft.1 hright.1,
          hleft.2, hright.2]
        ring
      · apply ih (a := a) (b := b)
        intro x hx hxzero
        have hxinsert := hcrit x hx hxzero
        simp only [mem_insert_iff] at hxinsert
        rcases hxinsert with hxc | hxS
        · subst x
          exact (hc hx).elim
        · exact hxS

/-- A finite critical-point cover is enough to make the supported power of a
smooth scalar path absolutely continuous on the whole interval. -/
theorem absolutelyContinuousOnInterval_h16SupportedRpow_comp_of_finite_critical_cover
    {β a b : ℝ} (hβ : 0 < β)
    {q q' : ℝ → ℝ}
    (hq : Continuous q)
    (hqq' : ∀ x, HasDerivAt q (q' x) x)
    (hq' : Continuous q')
    {S : Set ℝ} (hS : S.Finite)
    (hcrit : ∀ x ∈ Ioo (min a b) (max a b), q' x = 0 → x ∈ S) :
    AbsolutelyContinuousOnInterval
      (fun x ↦ h16SupportedRpow β (q x)) a b := by
  let k : ℝ → ℝ := fun x ↦ h16SupportedRpowDeriv β (q x) * q' x
  have hwhole :=
    intervalIntegrable_and_integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_finite_critical_cover
      hβ hq hqq' hq' hS hcrit
  have hprimitive : AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in a..x, k t) a b :=
    hwhole.1.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hconst : AbsolutelyContinuousOnInterval
      (fun _x : ℝ ↦ h16SupportedRpow β (q a)) a b :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hsum := hconst.add hprimitive
  rw [absolutelyContinuousOnInterval_iff] at hsum ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hsum ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlength
  have hresult := hbound E hE hlength
  convert hresult using 1
  apply Finset.sum_congr rfl
  intro i hi
  have endpoint_identity (x : ℝ) (hx : x ∈ [[a, b]]) :
      h16SupportedRpow β (q a) + ∫ t in a..x, k t =
        h16SupportedRpow β (q x) := by
    have hsubcrit : ∀ y ∈ Ioo (min a x) (max a x), q' y = 0 → y ∈ S := by
      intro y hy hyzero
      apply hcrit y
      · simp only [uIcc, mem_Icc] at hx
        simp only [mem_Ioo] at hy ⊢
        grind
      · exact hyzero
    have hax :=
      intervalIntegrable_and_integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_finite_critical_cover
        hβ hq hqq' hq' hS hsubcrit
    change h16SupportedRpow β (q a) + ∫ t in a..x, k t = _
    rw [show (∫ t in a..x, k t) =
        h16SupportedRpow β (q x) - h16SupportedRpow β (q a) by
      simpa only [k] using hax.2]
    ring
  simp only [Pi.add_apply]
  rw [endpoint_identity (E.2 i).1 (hE.1 i hi).1,
    endpoint_identity (E.2 i).2 (hE.1 i hi).2]

/-- Every positive supported power of an everywhere real-analytic scalar
curve is absolutely continuous on every compact interval. -/
theorem absolutelyContinuousOnInterval_h16SupportedRpow_comp_of_analytic
    {β a b : ℝ} (hβ : 0 < β)
    {q : ℝ → ℝ} (hq : ∀ x, AnalyticAt ℝ q x) :
    AbsolutelyContinuousOnInterval
      (fun x ↦ h16SupportedRpow β (q x)) a b := by
  have hqcont : Continuous q := continuous_iff_continuousAt.mpr fun x ↦
    (hq x).continuousAt
  have hqdiff : Differentiable ℝ q := fun x ↦ (hq x).differentiableAt
  have hderivcont : Continuous (deriv q) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hq x).deriv.continuousAt
  rcases finite_critical_set_or_deriv_eq_zero_of_analytic hq a b with
      hfinite | hzero
  · apply absolutelyContinuousOnInterval_h16SupportedRpow_comp_of_finite_critical_cover
      hβ hqcont (fun x ↦ (hqdiff x).hasDerivAt) hderivcont hfinite
    intro x hx hxzero
    exact ⟨by
      simp only [uIcc, mem_Icc, mem_Ioo] at hx ⊢
      grind, hxzero⟩
  · have hconst : q = fun _x ↦ q 0 := by
      funext x
      exact is_const_of_deriv_eq_zero hqdiff (fun t ↦ congrFun hzero t) x 0
    rw [hconst]
    exact contDiff_const.contDiffOn.absolutelyContinuousOnInterval

/-- Exact transported-kernel FTC for an everywhere real-analytic scalar
curve.  This is the integral form used when splicing the scalar boundary
factor into the H16 determinant-jet formula. -/
theorem intervalIntegrable_and_integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_analytic
    {β a b : ℝ} (hβ : 0 < β)
    {q : ℝ → ℝ} (hq : ∀ x, AnalyticAt ℝ q x) :
    IntervalIntegrable
        (fun x ↦ h16SupportedRpowDeriv β (q x) * deriv q x)
        volume a b ∧
      (∫ x in a..b,
          h16SupportedRpowDeriv β (q x) * deriv q x) =
        h16SupportedRpow β (q b) - h16SupportedRpow β (q a) := by
  have hqcont : Continuous q := continuous_iff_continuousAt.mpr fun x ↦
    (hq x).continuousAt
  have hqdiff : Differentiable ℝ q := fun x ↦ (hq x).differentiableAt
  have hderivcont : Continuous (deriv q) :=
    continuous_iff_continuousAt.mpr fun x ↦ (hq x).deriv.continuousAt
  rcases finite_critical_set_or_deriv_eq_zero_of_analytic hq a b with
      hfinite | hzero
  · apply intervalIntegrable_and_integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_finite_critical_cover
      hβ hqcont (fun x ↦ (hqdiff x).hasDerivAt) hderivcont hfinite
    intro x hx hxzero
    exact ⟨by
      simp only [uIcc, mem_Icc, mem_Ioo] at hx ⊢
      grind, hxzero⟩
  · have hkernel :
        (fun x ↦ h16SupportedRpowDeriv β (q x) * deriv q x) =
          fun _x ↦ (0 : ℝ) := by
      funext x
      rw [congrFun hzero x]
      simp
    rw [hkernel]
    refine ⟨by simp, ?_⟩
    rw [intervalIntegral.integral_zero]
    have hqab : q b = q a :=
      is_const_of_deriv_eq_zero hqdiff (fun t ↦ congrFun hzero t) b a
    rw [hqab]
    ring

/-- Literal H16 specialization: the sharp order-three positive-part
determinant factor is absolutely continuous on every compact time interval,
with no monotonicity assumption. -/
theorem absolutelyContinuousOnInterval_h16CenteredThirdBoundaryPower
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N)
    (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ h16SupportedRpow
        (coeCornerDensityExponent N K - 3)
        (h16CenteredTransportGapDeterminant v t x)) a b := by
  apply absolutelyContinuousOnInterval_h16SupportedRpow_comp_of_analytic
    (h16CenteredThirdBoundaryExponent_pos hboundary)
  exact analyticAt_h16CenteredTransportGapDeterminant hN v x

/-- Literal exact scalar FTC for the sharp H16 boundary factor, valid on an
arbitrary compact time interval and with no monotonicity hypothesis. -/
theorem integral_h16CenteredThirdBoundaryPower_timeDerivativeKernel_eq_sub
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N)
    (a b : ℝ) :
    (∫ t in a..b,
        h16SupportedRpowDeriv
            (coeCornerDensityExponent N K - 3)
            (h16CenteredTransportGapDeterminant v t x) *
          deriv (fun u : ℝ ↦
            h16CenteredTransportGapDeterminant v u x) t) =
      h16SupportedRpow
          (coeCornerDensityExponent N K - 3)
          (h16CenteredTransportGapDeterminant v b x) -
        h16SupportedRpow
          (coeCornerDensityExponent N K - 3)
          (h16CenteredTransportGapDeterminant v a x) := by
  exact
    (intervalIntegrable_and_integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_analytic
      (a := a) (b := b)
      (h16CenteredThirdBoundaryExponent_pos hboundary)
      (analyticAt_h16CenteredTransportGapDeterminant hN v x)).2

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
