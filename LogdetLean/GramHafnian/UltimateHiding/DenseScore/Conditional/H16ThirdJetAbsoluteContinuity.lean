import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FiniteFrontierTruncationAC

/-!
# Pointwise absolute continuity of the sharp H16 third jet

The order-three interior Faà di Bruno formula is rewritten with every radial
power as a zero-supported positive power.  Each such factor is absolutely
continuous along the analytic determinant curve, while all determinant-jet
coefficients are analytic.  The resulting global formula is therefore
locally absolutely continuous and vanishes whenever the determinant gap is
zero.

The literal order-three jet is exactly this formula truncated by the open
positive-definite time support.  The time support has finite compact
frontier, so the finite-frontier truncation theorem gives absolute continuity
of the literal zero extension on every compact time interval.
-/

open Filter MeasureTheory Set
open scoped Interval Topology ContDiff BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem analyticAt_iteratedDeriv_of_analytic_h16
    {f : ℝ → ℝ} (hf : ∀ x, AnalyticAt ℝ f x) (r : ℕ) :
    ∀ x, AnalyticAt ℝ (iteratedDeriv r f) x := by
  induction r with
  | zero =>
      simpa only [iteratedDeriv_zero] using hf
  | succ r ih =>
      intro x
      simpa only [Nat.succ_eq_add_one, iteratedDeriv_succ] using (ih x).deriv

/-- For fixed direction and coordinate point, every scalar determinant time
jet is smooth (indeed analytic) in time. -/
theorem contDiff_h16CenteredGapTimeJet_time
    {N : ℕ} (hN : 1 ≤ N) (r : ℕ)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N) :
    ContDiff ℝ ∞
      (fun t : ℝ ↦ h16CenteredGapTimeJet N r (((v, t), x))) := by
  let q : ℝ → ℝ := fun t ↦ h16CenteredTransportGapDeterminant v t x
  have hanalytic : ∀ t, AnalyticAt ℝ (iteratedDeriv r q) t :=
    analyticAt_iteratedDeriv_of_analytic_h16
      (analyticAt_h16CenteredTransportGapDeterminant hN v x) r
  have hcontdiff : ContDiff ℝ ∞ (iteratedDeriv r q) :=
    contDiff_iff_contDiffAt.mpr fun t ↦ (hanalytic t).contDiffAt
  simpa only [h16CenteredGapTimeJet, q] using hcontdiff

/-- Global order-three Bell formula with the radial real powers replaced by
their positive-part zero extensions. -/
def h16CenteredThirdSupportedFormula
    (N K : ℕ) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) (t : ℝ) : ℝ :=
  (h16COECoordinateRawMass N K)⁻¹.toReal *
    ∑ c : OrderedFinpartition 3,
      (descPochhammer ℝ c.length).eval (coeCornerDensityExponent N K) *
        h16SupportedRpow
          (coeCornerDensityExponent N K - (c.length : ℝ))
          (h16CenteredTransportGapDeterminant v t x) *
        ∏ j, h16CenteredGapTimeJet N (c.partSize j) (((v, t), x))

/-- Every term in the supported Bell formula is absolutely continuous on an
arbitrary compact interval. -/
private theorem absolutelyContinuousOnInterval_h16CenteredThirdSupportedFormula_term
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N)
    (c : OrderedFinpartition 3) (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦
        (descPochhammer ℝ c.length).eval (coeCornerDensityExponent N K) *
          h16SupportedRpow
            (coeCornerDensityExponent N K - (c.length : ℝ))
            (h16CenteredTransportGapDeterminant v t x) *
          ∏ j, h16CenteredGapTimeJet N (c.partSize j) (((v, t), x)))
      a b := by
  have hlen : c.length ≤ 3 := c.length_le
  have hlenR : (c.length : ℝ) ≤ 3 := by exact_mod_cast hlen
  have hβ : 0 < coeCornerDensityExponent N K - (c.length : ℝ) := by
    linarith [coe_boundary_exponent_ge_seven_halves hboundary]
  have hpow : AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ h16SupportedRpow
        (coeCornerDensityExponent N K - (c.length : ℝ))
        (h16CenteredTransportGapDeterminant v t x)) a b :=
    absolutelyContinuousOnInterval_h16SupportedRpow_comp_of_analytic hβ
      (analyticAt_h16CenteredTransportGapDeterminant hN v x)
  have hprodCD : ContDiff ℝ ∞
      (fun t : ℝ ↦
        ∏ j, h16CenteredGapTimeJet N (c.partSize j) (((v, t), x))) := by
    exact contDiff_prod fun j _ ↦
      contDiff_h16CenteredGapTimeJet_time hN (c.partSize j) v x
  have hprod : AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦
        ∏ j, h16CenteredGapTimeJet N (c.partSize j) (((v, t), x))) a b :=
    (hprodCD.of_le (by norm_num)).contDiffOn.absolutelyContinuousOnInterval
  have hmul := hpow.mul hprod
  simpa only [Pi.mul_apply, mul_assoc] using
    hmul.const_mul
      ((descPochhammer ℝ c.length).eval (coeCornerDensityExponent N K))

/-- The complete supported Bell formula is locally absolutely continuous. -/
theorem absolutelyContinuousOnInterval_h16CenteredThirdSupportedFormula
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N)
    (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (h16CenteredThirdSupportedFormula N K v x) a b := by
  let term : OrderedFinpartition 3 → ℝ → ℝ := fun c t ↦
    (descPochhammer ℝ c.length).eval (coeCornerDensityExponent N K) *
      h16SupportedRpow
        (coeCornerDensityExponent N K - (c.length : ℝ))
        (h16CenteredTransportGapDeterminant v t x) *
      ∏ j, h16CenteredGapTimeJet N (c.partSize j) (((v, t), x))
  have hterm (c : OrderedFinpartition 3) :
      AbsolutelyContinuousOnInterval (term c) a b := by
    simpa only [term] using
      absolutelyContinuousOnInterval_h16CenteredThirdSupportedFormula_term
        hN hboundary v x c a b
  have hsum : AbsolutelyContinuousOnInterval
      (fun t ↦ ∑ c : OrderedFinpartition 3, term c t) a b := by
    classical
    let S : Finset (OrderedFinpartition 3) := Finset.univ
    have hpartial : ∀ T : Finset (OrderedFinpartition 3),
        AbsolutelyContinuousOnInterval (fun t ↦ ∑ c ∈ T, term c t) a b := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
          simpa using
            (contDiff_const.contDiffOn.absolutelyContinuousOnInterval :
              AbsolutelyContinuousOnInterval (fun _t : ℝ ↦ (0 : ℝ)) a b)
      | @insert c T hc ih =>
          have heq : (fun t ↦ ∑ d ∈ insert c T, term d t) =
              term c + fun t ↦ ∑ d ∈ T, term d t := by
            funext t
            simp only [Finset.sum_insert hc, Pi.add_apply]
          rw [heq]
          exact (hterm c).add ih
    simpa only [S, Finset.sum_const_zero, Finset.sum_apply] using hpartial S
  unfold h16CenteredThirdSupportedFormula
  exact hsum.const_mul (h16COECoordinateRawMass N K)⁻¹.toReal

/-- On the positive-definite time support, the supported Bell formula is the
literal order-three jet. -/
theorem h16CenteredTransportJet_three_eq_supportedFormula_of_timeSupport
    {N K : ℕ} (hN : 1 ≤ N)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N) {t : ℝ}
    (ht : t ∈ h16CenteredTimeSupport v x) :
    h16CenteredTransportJet N K 3 v t x =
      h16CenteredThirdSupportedFormula N K v x t := by
  have hsupport : x ∈ h16CenteredTransportSupport v t := by
    simpa only [h16CenteredTimeSupport, mem_setOf_eq] using ht
  have hqpos : 0 < h16CenteredTransportGapDeterminant v t x := by
    apply h16COECoordinateGapDeterminant_pos
    simpa [h16CenteredTransportSupport] using hsupport
  rw [h16CenteredTransportJet, if_pos hsupport]
  change iteratedDeriv 3
      (fun u : ℝ ↦ h16CenteredTransportInteriorDensity N K v u x) t = _
  rw [h16CenteredTransportInteriorJet_eq_formula_of_support
    (N := N) (K := K) (r := 3) hN (((v, t), x)) hsupport]
  unfold h16CenteredInteriorJetFormula h16CenteredThirdSupportedFormula
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]
  rw [h16SupportedRpow_of_pos hqpos]

/-- The supported Bell formula vanishes on the exact time-support frontier. -/
theorem h16CenteredThirdSupportedFormula_zero_on_timeSupport_frontier
    {N K : ℕ} (hN : 1 ≤ N)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N) {t : ℝ}
    (ht : t ∈ frontier (h16CenteredTimeSupport v x)) :
    h16CenteredThirdSupportedFormula N K v x t = 0 := by
  have hgap :=
    h16CenteredTransportGap_zero_on_timeSupport_frontier hN v x ht
  unfold h16CenteredThirdSupportedFormula
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro c hc
  rw [hgap]
  simp

/-- The literal third jet is exactly the finite-frontier truncation of the
global supported Bell formula. -/
theorem h16CenteredTransportJet_three_eq_openTrunc_supportedFormula
    {N K : ℕ} (hN : 1 ≤ N)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N) :
    (fun t : ℝ ↦ h16CenteredTransportJet N K 3 v t x) =
      h16OpenTrunc (h16CenteredTimeSupport v x)
        (h16CenteredThirdSupportedFormula N K v x) := by
  funext t
  by_cases ht : t ∈ h16CenteredTimeSupport v x
  · rw [h16OpenTrunc, indicator_of_mem ht]
    exact h16CenteredTransportJet_three_eq_supportedFormula_of_timeSupport
      hN v x ht
  · rw [h16OpenTrunc, indicator_of_notMem ht]
    apply h16CenteredTransportJet_zero_off_support
    simpa only [h16CenteredTimeSupport, mem_setOf_eq] using ht

/-- The sharp literal order-three zero-extended jet is absolutely continuous
in time at every fixed coordinate point. -/
theorem absolutelyContinuousOnInterval_h16CenteredTransportJet_three
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N)
    (a b : ℝ) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ h16CenteredTransportJet N K 3 v t x) a b := by
  rw [h16CenteredTransportJet_three_eq_openTrunc_supportedFormula hN v x]
  apply absolutelyContinuousOnInterval_ite_mem_of_finite_frontier
  · exact isOpen_h16CenteredTimeSupport hN v x
  · exact fun c d ↦
      absolutelyContinuousOnInterval_h16CenteredThirdSupportedFormula
        hN hboundary v x c d
  · exact fun t ht ↦
      h16CenteredThirdSupportedFormula_zero_on_timeSupport_frontier
        hN v x ht
  · exact finite_h16CenteredTimeSupport_frontier_on_uIcc hN v x a b

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
