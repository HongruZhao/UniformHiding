import LogdetLean.ComplexPolygammaSeries
import LogdetLean.LogGammaPolygamma
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.Convex.Topology
import Mathlib.Tactic

/-!
# Complex digamma derivatives on the open right half-plane

Mathlib defines the complex digamma function as the logarithmic derivative
of Gamma, but currently supplies no polygamma derivative formulas.  This file
fills precisely that reusable gap.  It proves, from normally convergent
reciprocal-power series, that on `0 < re z`

`digamma'(z) = sum_l (z+l)^(-2)` and
`digamma''(z) = -2 sum_l (z+l)^(-3)`.

These are NIST DLMF 5.15.1.  The proof is included rather than imported: it
first identifies Mathlib's complex logarithmic derivative with the already
proved real Euler series on the positive axis and then applies the complex
identity principle.
-/

namespace LogdetLean

noncomputable section

open Complex Filter Set
open scoped BigOperators Topology

/-- Complex trigamma reciprocal-square series. -/
def complexTrigammaSeries (z : ℂ) : ℂ :=
  ∑' l : ℕ, (((z + (l : ℝ))⁻¹) ^ 2)

/-- Positive-sign complex second-polygamma reciprocal-cube series. -/
def complexNegPsiTwoSeries (z : ℂ) : ℂ :=
  2 * ∑' l : ℕ, (((z + (l : ℝ))⁻¹) ^ 3)

private theorem re_add_nat_le_norm {z : ℂ} (hz : 0 < z.re) (l : ℕ) :
    z.re + (l : ℝ) ≤ ‖z + (l : ℝ)‖ := by
  have h := Complex.abs_re_le_norm (z + (l : ℝ))
  simpa [abs_of_pos (add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg l))]
    using h

private theorem norm_inv_pow_le_re
    {z : ℂ} (hz : 0 < z.re) (l r : ℕ) :
    ‖((z + (l : ℝ))⁻¹ ^ r)‖ ≤
      1 / (z.re + (l : ℝ)) ^ r := by
  have hre : 0 < z.re + (l : ℝ) :=
    add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg l)
  have hnorm : 0 < ‖z + (l : ℝ)‖ :=
    hre.trans_le (re_add_nat_le_norm hz l)
  rw [norm_pow, norm_inv, one_div]
  simpa only [inv_pow] using
    (pow_le_pow_left₀ (inv_nonneg.mpr hnorm.le)
      ((inv_le_inv₀ hnorm hre).2 (re_add_nat_le_norm hz l)) r)

theorem summable_complex_inv_pow {z : ℂ} (hz : 0 < z.re)
    {r : ℕ} (hr : 1 < r) :
    Summable (fun l : ℕ ↦ ((z + (l : ℝ))⁻¹ ^ r)) := by
  apply Summable.of_norm_bounded
    (summable_shifted_reciprocal_pow hz hr)
  intro l
  simpa [one_div] using norm_inv_pow_le_re hz l r

private theorem hasDerivAt_complex_inv_sq
    {l : ℕ} {z : ℂ}
    (hz : z + (l : ℝ) ≠ 0) :
    HasDerivAt (fun w : ℂ ↦ ((w + (l : ℝ))⁻¹ ^ 2))
      (-(2 : ℂ) * ((z + (l : ℝ))⁻¹ ^ 3)) z := by
  have hshift : HasDerivAt (fun w : ℂ ↦ w + (l : ℝ)) 1 z :=
    (hasDerivAt_id z).add_const (l : ℂ)
  have hinv := hshift.inv hz
  have hpow := hinv.pow 2
  convert hpow using 1 <;> try rfl
  simp only [Pi.inv_apply]
  norm_num
  field_simp [hz]

theorem hasDerivAt_complexTrigammaSeries
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt complexTrigammaSeries (-complexNegPsiTwoSeries z) z := by
  let delta : ℝ := z.re / 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  let U : Set ℂ := {w | delta < w.re}
  have hUopen : IsOpen U := by
    exact isOpen_Ioi.preimage Complex.continuous_re
  have hUpre : IsPreconnected U := by
    exact (convex_halfSpace_gt Complex.reLm.isLinear delta).isPreconnected
  have hzU : z ∈ U := by dsimp [U, delta]; linarith
  have hsum : HasDerivAt
      (fun w : ℂ ↦ ∑' l : ℕ, ((w + (l : ℝ))⁻¹ ^ 2))
      (∑' l : ℕ, -(2 : ℂ) * ((z + (l : ℝ))⁻¹ ^ 3)) z := by
    apply hasDerivAt_tsum_of_isPreconnected
        (u := fun l : ℕ ↦ 2 * (1 / (delta + (l : ℝ)) ^ 3))
        (g := fun (l : ℕ) (w : ℂ) ↦ ((w + (l : ℝ))⁻¹ ^ 2))
        (g' := fun (l : ℕ) (w : ℂ) ↦
          -(2 : ℂ) * ((w + (l : ℝ))⁻¹ ^ 3))
        (t := U) (y₀ := z) (y := z)
        ((summable_shifted_reciprocal_pow hdelta (by norm_num : 1 < 3)).mul_left 2)
        hUopen hUpre
    · intro l w hw
      apply hasDerivAt_complex_inv_sq
      intro heq
      have hre := congrArg Complex.re heq
      dsimp [U] at hw
      simp at hre
      have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
      linarith
    · intro l w hw
      dsimp [U] at hw
      rw [norm_mul, norm_neg, show ‖(2 : ℂ)‖ = 2 by norm_num]
      calc
        2 * ‖(w + (l : ℝ))⁻¹ ^ 3‖ ≤
            2 * (1 / (w.re + (l : ℝ)) ^ 3) := by
          gcongr
          exact norm_inv_pow_le_re (hdelta.trans hw) l 3
        _ ≤ 2 * (1 / (delta + (l : ℝ)) ^ 3) := by
          gcongr
    · exact hzU
    · exact summable_complex_inv_pow hz (by norm_num)
    · exact hzU
  unfold complexTrigammaSeries complexNegPsiTwoSeries
  convert hsum using 1
  have hs := summable_complex_inv_pow hz (by norm_num : 1 < 3)
  rw [show -(2 * ∑' l : ℕ, (z + (l : ℝ))⁻¹ ^ 3) =
      (-(2 : ℂ)) * ∑' l : ℕ, (z + (l : ℝ))⁻¹ ^ 3 by ring,
    hs.tsum_mul_left]

/-- Restriction of the general reciprocal-cube series to a vertical line. -/
theorem complexNegPsiTwoSeries_axis (x u : ℝ) :
    complexNegPsiTwoSeries ((x : ℂ) + (u : ℂ) * Complex.I) =
      complexNegPsiTwoAxis x u := by
  unfold complexNegPsiTwoSeries complexNegPsiTwoAxis
  congr 1
  apply tsum_congr
  intro l
  push_cast
  ring

/-! ## Identification with Mathlib's complex digamma -/

/-- On the positive real axis, Mathlib's complex logarithmic derivative of
Gamma is the cast of the real Euler digamma series. -/
theorem complex_digamma_ofReal_eq_digammaSeries
    {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = (digammaSeries x : ℂ) := by
  have hGC : HasDerivAt Complex.Gamma
      (deriv Complex.Gamma (x : ℂ)) (x : ℂ) := by
    exact (Complex.differentiableAt_Gamma (x : ℂ) (fun n heq ↦ by
      have hre := congrArg Complex.re heq
      simp at hre
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)).hasDerivAt
  have hcast : HasDerivAt
      (fun y : ℝ ↦ Complex.Gamma (y : ℂ))
      (deriv Complex.Gamma (x : ℂ)) x := hGC.comp_ofReal
  let dR : ℝ := deriv Real.Gamma x
  have hGR : HasDerivAt Real.Gamma dR x := by
    dsimp [dR]
    exact (Real.differentiableAt_Gamma (fun n heq ↦ by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)).hasDerivAt
  have hcast' : HasDerivAt (fun y : ℝ ↦ (Real.Gamma y : ℂ))
      (deriv Complex.Gamma (x : ℂ)) x := by
    simpa only [Complex.Gamma_ofReal] using hcast
  have hderiv : deriv Complex.Gamma (x : ℂ) =
      (dR : ℂ) :=
    hcast'.unique hGR.ofReal_comp
  have hlog := hGR.log (Real.Gamma_pos_of_pos hx).ne'
  have hratio : dR / Real.Gamma x = digammaSeries x := by
    calc
      dR / Real.Gamma x =
          deriv (Real.log ∘ Real.Gamma) x := by
            simpa only [Function.comp_def] using hlog.deriv.symm
      _ = digammaSeries x := deriv_logGamma_eq_digammaSeries hx
  rw [Complex.digamma_def, logDeriv_apply, hderiv,
    Complex.Gamma_ofReal]
  norm_cast

/-- Open right half-plane used for the branch-free Gamma derivatives. -/
def complexRightHalfPlane : Set ℂ := {z | 0 < z.re}

theorem isOpen_complexRightHalfPlane : IsOpen complexRightHalfPlane := by
  exact isOpen_Ioi.preimage Complex.continuous_re

theorem isPreconnected_complexRightHalfPlane :
    IsPreconnected complexRightHalfPlane := by
  exact (convex_halfSpace_gt Complex.reLm.isLinear 0).isPreconnected

theorem analyticOnNhd_complex_digamma_rightHalfPlane :
    AnalyticOnNhd ℂ Complex.digamma complexRightHalfPlane := by
  have hGdiff : DifferentiableOn ℂ Complex.Gamma complexRightHalfPlane := by
    intro z hz
    change 0 < z.re at hz
    exact (Complex.differentiableAt_Gamma z (fun n heq ↦ by
      have hre := congrArg Complex.re heq
      simp at hre
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      exact (not_lt_of_ge hn) (by linarith [hz]))).differentiableWithinAt
  have hG : AnalyticOnNhd ℂ Complex.Gamma complexRightHalfPlane :=
    hGdiff.analyticOnNhd isOpen_complexRightHalfPlane
  have hGderiv := hG.deriv_of_isOpen isOpen_complexRightHalfPlane
  have hnonzero : ∀ z ∈ complexRightHalfPlane, Complex.Gamma z ≠ 0 := by
    intro z hz
    change 0 < z.re at hz
    apply Complex.Gamma_ne_zero
    intro n heq
    have hre := congrArg Complex.re heq
    simp at hre
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact (not_lt_of_ge hn) (by linarith [hz])
  have hquot : AnalyticOnNhd ℂ
      (fun z ↦ deriv Complex.Gamma z / Complex.Gamma z)
      complexRightHalfPlane := hGderiv.div hG hnonzero
  have heq : Complex.digamma =
      (fun z ↦ deriv Complex.Gamma z / Complex.Gamma z) := by
    funext z
    exact logDeriv_apply Complex.Gamma z
  rwa [heq]

theorem analyticOnNhd_complexTrigammaSeries_rightHalfPlane :
    AnalyticOnNhd ℂ complexTrigammaSeries complexRightHalfPlane := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_complexRightHalfPlane
  intro z hz
  exact (hasDerivAt_complexTrigammaSeries hz).differentiableAt.differentiableWithinAt

theorem complexTrigammaSeries_ofReal {x : ℝ} (_hx : 0 < x) :
    complexTrigammaSeries (x : ℂ) = (trigammaSeries x : ℂ) := by
  unfold complexTrigammaSeries trigammaSeries
  symm
  rw [Complex.ofReal_tsum
    (fun l : ℕ ↦ 1 / (x + (l : ℝ)) ^ 2)]
  apply tsum_congr
  intro l
  simp only [one_div]
  push_cast
  rw [inv_pow]

private theorem deriv_complex_digamma_ofReal
    {x : ℝ} (hx : 0 < x) :
    deriv Complex.digamma (x : ℂ) = (trigammaSeries x : ℂ) := by
  have hDC : HasDerivAt Complex.digamma
      (deriv Complex.digamma (x : ℂ)) (x : ℂ) :=
    (analyticOnNhd_complex_digamma_rightHalfPlane
      (x : ℂ) (by simpa [complexRightHalfPlane] using hx)).differentiableAt.hasDerivAt
  have hrestrict : HasDerivAt
      (fun y : ℝ ↦ Complex.digamma (y : ℂ))
      (deriv Complex.digamma (x : ℂ)) x := hDC.comp_ofReal
  have hevent : (fun y : ℝ ↦ Complex.digamma (y : ℂ)) =ᶠ[𝓝 x]
      (fun y ↦ (digammaSeries y : ℂ)) := by
    filter_upwards [eventually_gt_nhds hx] with y hy
    exact complex_digamma_ofReal_eq_digammaSeries hy
  have hrestrict' : HasDerivAt (fun y ↦ (digammaSeries y : ℂ))
      (deriv Complex.digamma (x : ℂ)) x :=
    hrestrict.congr_of_eventuallyEq hevent.symm
  exact hrestrict'.unique (hasDerivAt_digammaSeries hx).ofReal_comp

/-- Mathlib's complex digamma derivative is exactly the reciprocal-square
series throughout the open right half-plane. -/
theorem eqOn_deriv_complex_digamma_complexTrigammaSeries :
    EqOn (deriv Complex.digamma) complexTrigammaSeries
      complexRightHalfPlane := by
  have hD :=
    analyticOnNhd_complex_digamma_rightHalfPlane.deriv_of_isOpen
      isOpen_complexRightHalfPlane
  have hS := analyticOnNhd_complexTrigammaSeries_rightHalfPlane
  have hone : (1 : ℂ) ∈ complexRightHalfPlane := by
    simp [complexRightHalfPlane]
  refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hD hS
    isPreconnected_complexRightHalfPlane hone ?_
  have hevent : ∀ᶠ x : ℝ in 𝓝 1, 0 < x := eventually_gt_nhds zero_lt_one
  have hreal : ∃ᶠ x : ℝ in nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ,
      deriv Complex.digamma (x : ℂ) = complexTrigammaSeries (x : ℂ) := by
    have heq : ∀ᶠ x : ℝ in nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ,
        deriv Complex.digamma (x : ℂ) = complexTrigammaSeries (x : ℂ) := by
      filter_upwards [hevent.filter_mono inf_le_left] with x hx
      rw [deriv_complex_digamma_ofReal hx,
        complexTrigammaSeries_ofReal hx]
    exact heq.frequently
  rw [frequently_iff_seq_forall] at hreal ⊢
  obtain ⟨xs, hxs, heq⟩ := hreal
  refine ⟨fun n ↦ (xs n : ℂ), ?_, heq⟩
  rw [tendsto_nhdsWithin_iff] at hxs ⊢
  constructor
  · change Tendsto (Complex.ofReal ∘ xs) atTop
      (𝓝 (Complex.ofReal 1))
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hxs.1
  · simpa using hxs.2

theorem hasDerivAt_complex_digamma {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Complex.digamma (complexTrigammaSeries z) z := by
  have hd := (analyticOnNhd_complex_digamma_rightHalfPlane z
    (by simpa [complexRightHalfPlane] using hz)).differentiableAt.hasDerivAt
  exact hd.congr_deriv
    (eqOn_deriv_complex_digamma_complexTrigammaSeries
      (by simpa [complexRightHalfPlane] using hz))

/-- The reciprocal-cube second-polygamma series is holomorphic on the open
right half-plane.  This follows because it is minus the derivative of the
holomorphic trigamma series; no fourth-order termwise differentiation is
needed. -/
theorem analyticOnNhd_complexNegPsiTwoSeries_rightHalfPlane :
    AnalyticOnNhd ℂ complexNegPsiTwoSeries complexRightHalfPlane := by
  have hderiv :=
    analyticOnNhd_complexTrigammaSeries_rightHalfPlane.deriv_of_isOpen
      isOpen_complexRightHalfPlane
  have heq : Set.EqOn (deriv complexTrigammaSeries)
      (fun z ↦ -complexNegPsiTwoSeries z) complexRightHalfPlane := by
    intro z hz
    exact (hasDerivAt_complexTrigammaSeries
      (by simpa [complexRightHalfPlane] using hz)).deriv
  have hneg := hderiv.congr isOpen_complexRightHalfPlane heq
  have hpos := hneg.neg
  refine hpos.congr isOpen_complexRightHalfPlane ?_
  intro z _hz
  simp

end

end LogdetLean
