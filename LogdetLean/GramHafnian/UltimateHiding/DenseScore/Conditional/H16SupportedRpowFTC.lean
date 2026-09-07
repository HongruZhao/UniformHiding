import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthSecantL1VanishingReduction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# A scalar FTC through a moving supported-real-power boundary

At the sharp H16 endpoint, the order-three determinant jet contains real
powers whose smallest exponent is `1 / 2`.  Its order-four derivative has
the corresponding integrable `-1 / 2` singularity.  Ordinary `C¹`
composition is therefore unavailable at a support crossing.

This module proves the exact one-dimensional replacement.  The positive-part
power

`x ↦ if 0 < x then x ^ β else 0`

is absolutely continuous for every `β > 0`, has its expected derivative
away from the single boundary point, and satisfies the exact fundamental
theorem of calculus.  The result is then transported through any monotone
`C¹` scalar gap path, including affine paths that move the support through
the observation point.

The determinant gap along the centered matrix-exponential flow is smooth,
but the current library does not yet prove that each compact time interval
admits a finite/countable monotonicity decomposition with summable variation.
Moreover, positivity of the determinant alone is weaker than positive
definiteness of the full COE denominator away from the connected support
component.  Consequently the scalar theorem below is a genuine strict
reduction of the H16 obstruction, not a declaration of the missing H16 limit.
-/

open Filter MeasureTheory Set
open scoped Topology Interval ContDiff

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The literal zero extension of a positive real power. -/
def h16SupportedRpow (β x : ℝ) : ℝ :=
  if 0 < x then x ^ β else 0

/-- The a.e. derivative of `h16SupportedRpow β`.  At the support frontier it
is assigned the harmless representative value zero. -/
def h16SupportedRpowDeriv (β x : ℝ) : ℝ :=
  if 0 < x then β * x ^ (β - 1) else 0

@[simp]
theorem h16SupportedRpow_of_pos {β x : ℝ} (hx : 0 < x) :
    h16SupportedRpow β x = x ^ β := by
  simp [h16SupportedRpow, hx]

@[simp]
theorem h16SupportedRpow_of_nonpos {β x : ℝ} (hx : x ≤ 0) :
    h16SupportedRpow β x = 0 := by
  simp [h16SupportedRpow, not_lt.mpr hx]

@[simp]
theorem h16SupportedRpow_zero {β : ℝ} :
    h16SupportedRpow β 0 = 0 := by
  simp [h16SupportedRpow]

@[simp]
theorem h16SupportedRpowDeriv_of_pos {β x : ℝ} (hx : 0 < x) :
    h16SupportedRpowDeriv β x = β * x ^ (β - 1) := by
  simp [h16SupportedRpowDeriv, hx]

@[simp]
theorem h16SupportedRpowDeriv_of_nonpos {β x : ℝ} (hx : x ≤ 0) :
    h16SupportedRpowDeriv β x = 0 := by
  simp [h16SupportedRpowDeriv, not_lt.mpr hx]

theorem measurable_h16SupportedRpowDeriv (β : ℝ) :
    Measurable (h16SupportedRpowDeriv β) := by
  have hrpow : Measurable (fun x : ℝ ↦ x ^ (β - 1)) := by
    by_cases hβone : β - 1 = 0
    · rw [hβone]
      simpa only [Real.rpow_zero] using
        (measurable_const : Measurable (fun _x : ℝ ↦ (1 : ℝ)))
    · have hfun : (fun x : ℝ ↦ x ^ (β - 1)) = fun x ↦
          if 0 ≤ x then
            if x = 0 then 0 else Real.exp (Real.log x * (β - 1))
          else Real.exp (Real.log x * (β - 1)) *
            Real.cos ((β - 1) * Real.pi) := by
        funext x
        by_cases hx : 0 ≤ x
        · rw [if_pos hx, Real.rpow_def_of_nonneg hx, if_neg hβone]
        · rw [if_neg hx, Real.rpow_def_of_neg (lt_of_not_ge hx)]
      rw [hfun]
      exact Measurable.ite (measurableSet_le measurable_const measurable_id)
        (Measurable.ite
          (measurableSet_eq_fun measurable_id measurable_const)
          measurable_const (by fun_prop)) (by fun_prop)
  unfold h16SupportedRpowDeriv
  exact Measurable.ite measurableSet_Ioi
    (measurable_const.mul hrpow) measurable_const

/-- The supported derivative kernel is integrable on every finite interval
as soon as `β > 0`; its worst singularity is `x ^ (β - 1)`. -/
theorem intervalIntegrable_h16SupportedRpowDeriv
    {β a b : ℝ} (hβ : 0 < β) :
    IntervalIntegrable (h16SupportedRpowDeriv β) volume a b := by
  have hraw : IntervalIntegrable
      (fun x : ℝ ↦ β * x ^ (β - 1)) volume a b :=
    (intervalIntegral.intervalIntegrable_rpow'
      (show -1 < β - 1 by linarith)).const_mul β
  apply hraw.mono_fun
  · exact (measurable_h16SupportedRpowDeriv β).aestronglyMeasurable
      |>.restrict
  · exact ae_of_all _ fun x ↦ by
      by_cases hx : 0 < x
      · simp [h16SupportedRpowDeriv, hx]
      · simp only [h16SupportedRpowDeriv, if_neg hx, norm_zero,
          norm_mul]
        positivity

private theorem integral_h16SupportedRpowDeriv_zero_right
    {β b : ℝ} (hβ : 0 < β) :
    (∫ x in (0 : ℝ)..b, h16SupportedRpowDeriv β x) =
      h16SupportedRpow β b := by
  rcases le_total 0 b with hb | hb
  · calc
      (∫ x in (0 : ℝ)..b, h16SupportedRpowDeriv β x) =
          ∫ x in (0 : ℝ)..b, β * x ^ (β - 1) := by
            apply intervalIntegral.integral_congr_uIoo
            intro x hx
            have hxpos : 0 < x := by
              rw [uIoo_of_le hb] at hx
              exact hx.1
            simp [h16SupportedRpowDeriv, hxpos]
      _ = β * ∫ x in (0 : ℝ)..b, x ^ (β - 1) := by
            rw [intervalIntegral.integral_const_mul]
      _ = β * ((b ^ β - (0 : ℝ) ^ β) / β) := by
            rw [integral_rpow
              (show -1 < β - 1 ∨
                  β - 1 ≠ -1 ∧ (0 : ℝ) ∉ [[(0 : ℝ), b]] by
                exact Or.inl (by linarith))]
            ring_nf
      _ = b ^ β := by
            rw [Real.zero_rpow hβ.ne']
            field_simp
            ring
      _ = h16SupportedRpow β b := by
            rcases hb.eq_or_lt with rfl | hbpos
            · simp [h16SupportedRpow, Real.zero_rpow hβ.ne']
            · exact (h16SupportedRpow_of_pos hbpos).symm
  · have hzero :
        (∫ x in (0 : ℝ)..b, h16SupportedRpowDeriv β x) =
          ∫ _x in (0 : ℝ)..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      have hxneg : x < 0 := by
        have hx' : x ∈ Ioo b 0 := by
          simpa [uIoo_of_ge hb] using hx
        exact hx'.2
      simp [h16SupportedRpowDeriv, not_lt.mpr hxneg.le]
    rw [hzero, intervalIntegral.integral_zero]
    exact (h16SupportedRpow_of_nonpos hb).symm

/-- Exact scalar FTC for the zero-extended real power, including intervals
that cross the support boundary. -/
theorem integral_h16SupportedRpowDeriv_eq_sub
    {β a b : ℝ} (hβ : 0 < β) :
    (∫ x in a..b, h16SupportedRpowDeriv β x) =
      h16SupportedRpow β b - h16SupportedRpow β a := by
  have h0b := intervalIntegrable_h16SupportedRpowDeriv
    (a := 0) (b := b) hβ
  have h0a := intervalIntegrable_h16SupportedRpowDeriv
    (a := 0) (b := a) hβ
  rw [← intervalIntegral.integral_interval_sub_left h0b h0a]
  rw [integral_h16SupportedRpowDeriv_zero_right hβ]
  rw [integral_h16SupportedRpowDeriv_zero_right hβ]

/-- The positive-part real power is absolutely continuous on every compact
interval even when `0 < β < 1`, where it is not Lipschitz at zero. -/
theorem absolutelyContinuousOnInterval_h16SupportedRpow
    {β a b : ℝ} (hβ : 0 < β) :
    AbsolutelyContinuousOnInterval (h16SupportedRpow β) a b := by
  let g : ℝ → ℝ := h16SupportedRpowDeriv β
  have hg : IntervalIntegrable g volume a b := by
    simpa only [g] using
      (intervalIntegrable_h16SupportedRpowDeriv (a := a) (b := b) hβ)
  have hprimitive : AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in a..x, g t) a b :=
    hg.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hconst : AbsolutelyContinuousOnInterval
      (fun _x : ℝ ↦ h16SupportedRpow β a) a b := by
    exact contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hsum := hconst.add hprimitive
  have hfun : ((fun _x : ℝ ↦ h16SupportedRpow β a) +
      (fun x : ℝ ↦ ∫ t in a..x, g t)) = h16SupportedRpow β := by
    funext x
    simp only [Pi.add_apply]
    rw [show (∫ t in a..x, g t) =
        h16SupportedRpow β x - h16SupportedRpow β a by
      simpa only [g] using
        (integral_h16SupportedRpowDeriv_eq_sub
          (β := β) (a := a) (b := x) hβ)]
    ring
  rw [← hfun]
  exact hsum

/-- Away from the single support frontier, the supported power has the
literal supported derivative. -/
theorem h16SupportedRpow_hasDerivAt_of_ne_zero
    {β x : ℝ} (_hβ : 0 < β) (hx : x ≠ 0) :
    HasDerivAt (h16SupportedRpow β)
      (h16SupportedRpowDeriv β x) x := by
  rcases lt_trichotomy x 0 with hxneg | hxeq | hxpos
  · have heq : h16SupportedRpow β =ᶠ[𝓝 x] (fun _ ↦ 0) := by
      filter_upwards [Iio_mem_nhds hxneg] with y hy
      change y < 0 at hy
      exact h16SupportedRpow_of_nonpos hy.le
    have hzero := hasDerivAt_const (x := x) (c := (0 : ℝ))
    have hderiv : h16SupportedRpowDeriv β x = 0 := by
      exact h16SupportedRpowDeriv_of_nonpos hxneg.le
    exact (hzero.congr_of_eventuallyEq heq).congr_deriv hderiv.symm
  · exact (hx hxeq).elim
  · have heq : h16SupportedRpow β =ᶠ[𝓝 x] (fun y ↦ y ^ β) := by
      filter_upwards [Ioi_mem_nhds hxpos] with y hy
      change 0 < y at hy
      exact h16SupportedRpow_of_pos hy
    have hraw : HasDerivAt (fun y : ℝ ↦ y ^ β)
        (β * x ^ (β - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx)
    have hderiv : h16SupportedRpowDeriv β x =
        β * x ^ (β - 1) := h16SupportedRpowDeriv_of_pos hxpos
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv hderiv.symm

/-- The supported-power derivative identity holds almost everywhere; only
the singleton frontier is discarded. -/
theorem h16SupportedRpow_hasDerivAt_ae
    {β : ℝ} (hβ : 0 < β) :
    ∀ᵐ x : ℝ ∂volume,
      HasDerivAt (h16SupportedRpow β)
        (h16SupportedRpowDeriv β x) x := by
  have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hx
  exact h16SupportedRpow_hasDerivAt_of_ne_zero hβ hx

/-! ## Passage through a monotone smooth moving gap -/

/-- Exact supported-power FTC through a nondecreasing `C¹` scalar gap path.
No differentiability of the outer power at a support crossing is assumed. -/
theorem integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_deriv_nonneg
    {β a b : ℝ} (hβ : 0 < β)
    {q q' : ℝ → ℝ}
    (hq : ContinuousOn q [[a, b]])
    (hqq' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt q (q' x) x)
    (hq' : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ q' x) :
    (∫ x in a..b,
        h16SupportedRpowDeriv β (q x) * q' x) =
      h16SupportedRpow β (q b) - h16SupportedRpow β (q a) := by
  change (∫ x in a..b,
      (h16SupportedRpowDeriv β ∘ q) x * q' x) = _
  rw [intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    hq hqq' hq']
  exact integral_h16SupportedRpowDeriv_eq_sub hβ

/-- Exact supported-power FTC through a nonincreasing `C¹` scalar gap path. -/
theorem integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_deriv_nonpos
    {β a b : ℝ} (hβ : 0 < β)
    {q q' : ℝ → ℝ}
    (hq : ContinuousOn q [[a, b]])
    (hqq' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt q (q' x) x)
    (hq' : ∀ x ∈ Ioo (min a b) (max a b), q' x ≤ 0) :
    (∫ x in a..b,
        h16SupportedRpowDeriv β (q x) * q' x) =
      h16SupportedRpow β (q b) - h16SupportedRpow β (q a) := by
  change (∫ x in a..b,
      (h16SupportedRpowDeriv β ∘ q) x * q' x) = _
  rw [intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    hq hqq' hq']
  exact integral_h16SupportedRpowDeriv_eq_sub hβ

/-- The derivative kernel transported through a nondecreasing `C¹` gap is
interval-integrable. -/
theorem intervalIntegrable_h16SupportedRpowDeriv_comp_mul_of_deriv_nonneg
    {β a b : ℝ} (hβ : 0 < β)
    {q q' : ℝ → ℝ}
    (hq : ContinuousOn q [[a, b]])
    (hqq' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt q (q' x) x)
    (hq' : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ q' x) :
    IntervalIntegrable
      (fun x ↦ h16SupportedRpowDeriv β (q x) * q' x)
      volume a b := by
  change IntervalIntegrable
    (fun x ↦ (h16SupportedRpowDeriv β ∘ q) x * q' x)
    volume a b
  rw [intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    hq hqq' hq']
  exact intervalIntegrable_h16SupportedRpowDeriv hβ

/-- The derivative kernel transported through a nonincreasing `C¹` gap is
interval-integrable. -/
theorem intervalIntegrable_h16SupportedRpowDeriv_comp_mul_of_deriv_nonpos
    {β a b : ℝ} (hβ : 0 < β)
    {q q' : ℝ → ℝ}
    (hq : ContinuousOn q [[a, b]])
    (hqq' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt q (q' x) x)
    (hq' : ∀ x ∈ Ioo (min a b) (max a b), q' x ≤ 0) :
    IntervalIntegrable
      (fun x ↦ h16SupportedRpowDeriv β (q x) * q' x)
      volume a b := by
  change IntervalIntegrable
    (fun x ↦ (h16SupportedRpowDeriv β ∘ q) x * q' x)
    volume a b
  rw [intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
    hq hqq' hq']
  exact intervalIntegrable_h16SupportedRpowDeriv hβ

private theorem absolutelyContinuousOnInterval_congr_of_eqOn
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfg : Set.EqOn f g [[a, b]]) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro E hE hlength
  have hresult := hbound E hE hlength
  convert hresult using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hfg (hE.1 i hi).1, hfg (hE.1 i hi).2]

/-- A supported positive power remains absolutely continuous after composition
with a nondecreasing `C¹` gap path.  This is the precise scalar regularity
needed on each monotonicity piece of a moving determinant support. -/
theorem absolutelyContinuousOnInterval_h16SupportedRpow_comp_of_deriv_nonneg
    {β a b : ℝ} (hβ : 0 < β)
    {q q' : ℝ → ℝ}
    (hq : ContinuousOn q [[a, b]])
    (hqq' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt q (q' x) x)
    (hq' : ∀ x ∈ Ioo (min a b) (max a b), 0 ≤ q' x) :
    AbsolutelyContinuousOnInterval
      (fun x ↦ h16SupportedRpow β (q x)) a b := by
  let k : ℝ → ℝ := fun x ↦
    h16SupportedRpowDeriv β (q x) * q' x
  have hk : IntervalIntegrable k volume a b := by
    simpa only [k] using
      (intervalIntegrable_h16SupportedRpowDeriv_comp_mul_of_deriv_nonneg
        hβ hq hqq' hq')
  have hprimitive : AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in a..x, k t) a b :=
    hk.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hconst : AbsolutelyContinuousOnInterval
      (fun _x : ℝ ↦ h16SupportedRpow β (q a)) a b := by
    exact contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hsum := hconst.add hprimitive
  apply absolutelyContinuousOnInterval_congr_of_eqOn hsum
  intro x hx
  simp only [Pi.add_apply]
  have hqax : ContinuousOn q [[a, x]] := by
    apply hq.mono
    intro y hy
    simp only [uIcc, mem_Icc] at hx hy ⊢
    grind
  have hqq'ax : ∀ y ∈ Ioo (min a x) (max a x),
      HasDerivAt q (q' y) y := by
    intro y hy
    apply hqq' y
    simp only [mem_Ioo] at hy ⊢
    simp only [uIcc, mem_Icc] at hx
    grind
  have hq'ax : ∀ y ∈ Ioo (min a x) (max a x), 0 ≤ q' y := by
    intro y hy
    apply hq' y
    simp only [mem_Ioo] at hy ⊢
    simp only [uIcc, mem_Icc] at hx
    grind
  have hFTC :=
    integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_deriv_nonneg
      (β := β) (a := a) (b := x) hβ hqax hqq'ax hq'ax
  change h16SupportedRpow β (q a) + ∫ t in a..x, k t = _
  rw [show (∫ t in a..x, k t) =
      h16SupportedRpow β (q x) - h16SupportedRpow β (q a) by
    simpa only [k] using hFTC]
  ring

/-- The analogous absolute-continuity theorem for a nonincreasing `C¹` gap
path. -/
theorem absolutelyContinuousOnInterval_h16SupportedRpow_comp_of_deriv_nonpos
    {β a b : ℝ} (hβ : 0 < β)
    {q q' : ℝ → ℝ}
    (hq : ContinuousOn q [[a, b]])
    (hqq' : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt q (q' x) x)
    (hq' : ∀ x ∈ Ioo (min a b) (max a b), q' x ≤ 0) :
    AbsolutelyContinuousOnInterval
      (fun x ↦ h16SupportedRpow β (q x)) a b := by
  let k : ℝ → ℝ := fun x ↦
    h16SupportedRpowDeriv β (q x) * q' x
  have hk : IntervalIntegrable k volume a b := by
    simpa only [k] using
      (intervalIntegrable_h16SupportedRpowDeriv_comp_mul_of_deriv_nonpos
        hβ hq hqq' hq')
  have hprimitive : AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in a..x, k t) a b :=
    hk.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hconst : AbsolutelyContinuousOnInterval
      (fun _x : ℝ ↦ h16SupportedRpow β (q a)) a b := by
    exact contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hsum := hconst.add hprimitive
  apply absolutelyContinuousOnInterval_congr_of_eqOn hsum
  intro x hx
  simp only [Pi.add_apply]
  have hqax : ContinuousOn q [[a, x]] := by
    apply hq.mono
    intro y hy
    simp only [uIcc, mem_Icc] at hx hy ⊢
    grind
  have hqq'ax : ∀ y ∈ Ioo (min a x) (max a x),
      HasDerivAt q (q' y) y := by
    intro y hy
    apply hqq' y
    simp only [mem_Ioo] at hy ⊢
    simp only [uIcc, mem_Icc] at hx
    grind
  have hq'ax : ∀ y ∈ Ioo (min a x) (max a x), q' y ≤ 0 := by
    intro y hy
    apply hq' y
    simp only [mem_Ioo] at hy ⊢
    simp only [uIcc, mem_Icc] at hx
    grind
  have hFTC :=
    integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_deriv_nonpos
      (β := β) (a := a) (b := x) hβ hqax hqq'ax hq'ax
  change h16SupportedRpow β (q a) + ∫ t in a..x, k t = _
  rw [show (∫ t in a..x, k t) =
      h16SupportedRpow β (q x) - h16SupportedRpow β (q a) by
    simpa only [k] using hFTC]
  ring

/-- Concrete affine moving-support specialization.  It includes a transverse
crossing `c + m t = 0` and is the exact local model of a regular determinant
frontier point. -/
theorem integral_h16SupportedRpowDeriv_affine_mul_eq_sub
    {β a b c m : ℝ} (hβ : 0 < β) :
    (∫ t in a..b,
        h16SupportedRpowDeriv β (c + t * m) * m) =
      h16SupportedRpow β (c + b * m) -
        h16SupportedRpow β (c + a * m) := by
  rcases le_total 0 m with hm | hm
  · apply integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_deriv_nonneg
      hβ (q := fun t ↦ c + t * m) (q' := fun _ ↦ m)
    · fun_prop
    · intro x hx
      have h : HasDerivAt (fun t : ℝ ↦ c + t * m) (0 + 1 * m) x :=
        (hasDerivAt_const x c).add ((hasDerivAt_id x).mul_const m)
      simpa only [zero_add, one_mul] using h
    · exact fun _ _ ↦ hm
  · apply integral_h16SupportedRpowDeriv_comp_mul_eq_sub_of_deriv_nonpos
      hβ (q := fun t ↦ c + t * m) (q' := fun _ ↦ m)
    · fun_prop
    · intro x hx
      have h : HasDerivAt (fun t : ℝ ↦ c + t * m) (0 + 1 * m) x :=
        (hasDerivAt_const x c).add ((hasDerivAt_id x).mul_const m)
      simpa only [zero_add, one_mul] using h
    · exact fun _ _ ↦ hm

/-! ## Literal H16 determinant-gap specialization -/

/-- The sharp order-three boundary power in H16 is strictly positive; at the
minimal dense boundary it is exactly `1 / 2`. -/
theorem h16CenteredThirdBoundaryExponent_pos
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    0 < coeCornerDensityExponent N K - 3 := by
  linarith [coe_boundary_exponent_ge_seven_halves hboundary]

/-- Smoothness in time of the literal centered determinant gap. -/
theorem contDiff_h16CenteredTransportGapDeterminant_time
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    ContDiff ℝ ∞ (fun t : ℝ ↦
      h16CenteredTransportGapDeterminant v t x) := by
  have heq : (fun t : ℝ ↦ h16CenteredTransportGapDeterminant v t x) =
      fun t : ℝ ↦ h16AmbientTransportGap N ((v.1, x), t) := by
    funext t
    exact h16CenteredTransportGap_eq_ambient hN v t x
  rw [heq]
  exact (contDiff_h16AmbientTransportGap N).comp
    (contDiff_const.prodMk contDiff_id)

/-- On the literal positive-definite transport support, the scalar supported
power agrees with the interior real-power factor.  No converse is asserted:
outside the COE component, a determinant may be positive without the
denominator being positive definite. -/
theorem h16SupportedRpow_centeredGap_eq_rpow_of_mem_transportSupport
    {N : ℕ} {β : ℝ} {v : ComplexUnitSphere N} {t : ℝ}
    {x : ComplexSymmetricCoordinates N}
    (hx : x ∈ h16CenteredTransportSupport v t) :
    h16SupportedRpow β (h16CenteredTransportGapDeterminant v t x) =
      (h16CenteredTransportGapDeterminant v t x) ^ β := by
  apply h16SupportedRpow_of_pos
  apply h16COECoordinateGapDeterminant_pos
  simpa [h16CenteredTransportSupport] using hx

/-- On every interval where the actual centered determinant gap is
nondecreasing, its sharp order-three scalar positive-part factor is absolutely
continuous across all determinant-zero crossings.  To apply this directly to
the literal jet, the interval must also remain in the closure of the COE
positive-definite component. -/
theorem absolutelyContinuousOnInterval_h16CenteredThirdBoundaryPower_of_gapDeriv_nonneg
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N)
    {a b : ℝ}
    (hgap' : ∀ t ∈ Ioo (min a b) (max a b),
      0 ≤ deriv
        (fun u : ℝ ↦ h16CenteredTransportGapDeterminant v u x) t) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ h16SupportedRpow
        (coeCornerDensityExponent N K - 3)
        (h16CenteredTransportGapDeterminant v t x)) a b := by
  let q : ℝ → ℝ := fun t ↦
    h16CenteredTransportGapDeterminant v t x
  let q' : ℝ → ℝ := deriv q
  apply absolutelyContinuousOnInterval_h16SupportedRpow_comp_of_deriv_nonneg
    (h16CenteredThirdBoundaryExponent_pos hboundary)
    (q := q) (q' := q')
  · exact (contDiff_h16CenteredTransportGapDeterminant_time hN v x).continuous.continuousOn
  · intro t ht
    exact ((contDiff_h16CenteredTransportGapDeterminant_time hN v x).differentiable
      (by simp)).differentiableAt.hasDerivAt
  · exact hgap'

/-- The corresponding literal H16 theorem on intervals where the determinant
gap is nonincreasing. -/
theorem absolutelyContinuousOnInterval_h16CenteredThirdBoundaryPower_of_gapDeriv_nonpos
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (x : ComplexSymmetricCoordinates N)
    {a b : ℝ}
    (hgap' : ∀ t ∈ Ioo (min a b) (max a b),
      deriv (fun u : ℝ ↦
        h16CenteredTransportGapDeterminant v u x) t ≤ 0) :
    AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ h16SupportedRpow
        (coeCornerDensityExponent N K - 3)
        (h16CenteredTransportGapDeterminant v t x)) a b := by
  let q : ℝ → ℝ := fun t ↦
    h16CenteredTransportGapDeterminant v t x
  let q' : ℝ → ℝ := deriv q
  apply absolutelyContinuousOnInterval_h16SupportedRpow_comp_of_deriv_nonpos
    (h16CenteredThirdBoundaryExponent_pos hboundary)
    (q := q) (q' := q')
  · exact (contDiff_h16CenteredTransportGapDeterminant_time hN v x).continuous.continuousOn
  · intro t ht
    exact ((contDiff_h16CenteredTransportGapDeterminant_time hN v x).differentiable
      (by simp)).differentiableAt.hasDerivAt
  · exact hgap'

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
