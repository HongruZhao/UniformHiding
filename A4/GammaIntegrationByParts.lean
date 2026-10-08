import A4.WishartDensityGamma
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory ProbabilityTheory Set Filter Topology

noncomputable section

namespace A4Research

def gammaKernel (a r x : ℝ) : ℝ := x ^ (a - 1) * Real.exp (-(r * x))

theorem hasDerivAt_gammaKernel {a r x : ℝ} (hx : 0 < x) :
    HasDerivAt (gammaKernel a r)
      (((a - 1) / x - r) * gammaKernel a r x) x := by
  have hp := Real.hasDerivAt_rpow_const (p := a - 1) (Or.inl hx.ne')
  have he : HasDerivAt (fun y : ℝ ↦ Real.exp (-(r * y)))
      (-r * Real.exp (-(r * x))) x := by
    convert (((hasDerivAt_id x).const_mul r).neg.exp) using 1 <;>
      first | rfl | (simp only [Pi.neg_apply, id_eq, mul_one, neg_mul] <;> ring)
  unfold gammaKernel
  apply (hp.mul he).congr_deriv
  rw [Real.rpow_sub hx (a - 1) 1, Real.rpow_one]
  ring

/-- Unconditional conversion of a Gamma expectation into its positive-half-line
kernel integral, using the literal Gamma density from mathlib. -/
theorem gammaMeasure_integral_eq_kernel {a r : ℝ}
    (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    (∫ x, f x ∂gammaMeasure a r) =
      (r ^ a / Real.Gamma a) * ∫ x in Ioi (0 : ℝ), gammaKernel a r x * f x := by
  unfold gammaMeasure gammaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gammaPDFReal a r).ennreal_ofReal)
    (ae_of_all _ fun x ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  have heq : (fun x : ℝ ↦ gammaPDFReal a r x * f x) =ᵐ[volume]
      (Ioi (0 : ℝ)).indicator (fun x ↦
        (r ^ a / Real.Gamma a) * (gammaKernel a r x * f x)) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    by_cases hpos : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hpos)]
      simp only [gammaPDFReal, if_pos hpos.le, gammaKernel]
      ring
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hpos)]
      simp only [gammaPDFReal, if_neg (not_le.mpr
        (lt_of_le_of_ne (not_lt.mp hpos) hx)), zero_mul]
  rw [integral_congr_ae heq, integral_indicator measurableSet_Ioi, integral_const_mul]

set_option backward.isDefEq.respectTransparency false in
/-- Scalar Gamma integration by parts with explicit boundary and integrability
conditions. These conditions must be checked for the inverse-moment test fields;
this lemma does not assume a matrix Stein--Haff identity. -/
theorem gammaMeasure_integrationByParts {a r : ℝ} (ha : 1 < a) (hr : 0 < r)
    (f f' : ℝ → ℝ)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f (f' x) x)
    (hzero : ContinuousWithinAt (fun x ↦ gammaKernel a r x * f x) (Ici 0) 0)
    (htop : Tendsto (fun x ↦ gammaKernel a r x * f x) atTop (𝓝 0))
    (hint : IntegrableOn (fun x ↦ gammaKernel a r x * f x) (Ioi 0))
    (hderivint : IntegrableOn (fun x ↦ gammaKernel a r x * f' x) (Ioi 0))
    (hdivint : IntegrableOn (fun x ↦ gammaKernel a r x * (f x / x)) (Ioi 0)) :
    (∫ x, f' x ∂gammaMeasure a r) =
      r * (∫ x, f x ∂gammaMeasure a r) -
        (a - 1) * (∫ x, f x / x ∂gammaMeasure a r) := by
  let g' : ℝ → ℝ := fun x ↦ gammaKernel a r x * f' x +
    (a - 1) * (gammaKernel a r x * (f x / x)) -
    r * (gammaKernel a r x * f x)
  have hgderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivAt (fun y ↦ gammaKernel a r y * f y) (g' x) x := by
    intro x hx
    apply ((hasDerivAt_gammaKernel hx).mul (hderiv x hx)).congr_deriv
    dsimp [g']
    ring
  have hgint : IntegrableOn g' (Ioi (0 : ℝ)) :=
    (hderivint.add (hdivint.const_mul (a - 1))).sub (hint.const_mul r)
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto hzero hgderiv hgint htop
  have hgzero : gammaKernel a r (0 : ℝ) * f 0 = 0 := by
    simp [gammaKernel, Real.zero_rpow (sub_pos.mpr ha).ne']
  rw [hgzero, sub_zero] at hFTC
  dsimp only [g'] at hFTC
  change (∫ x in Ioi (0 : ℝ),
    ((fun y ↦ gammaKernel a r y * f' y) +
      (fun y ↦ (a - 1) * (gammaKernel a r y * (f y / y)))) x -
      (fun y ↦ r * (gammaKernel a r y * f y)) x) = 0 at hFTC
  rw [integral_sub (hderivint.add (hdivint.const_mul (a - 1))) (hint.const_mul r)] at hFTC
  simp only [Pi.add_apply] at hFTC
  rw [integral_add hderivint (hdivint.const_mul (a - 1)),
    integral_const_mul, integral_const_mul] at hFTC
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  rw [gammaMeasure_integral_eq_kernel ha0 hr f',
    gammaMeasure_integral_eq_kernel ha0 hr f,
    gammaMeasure_integral_eq_kernel ha0 hr (fun x ↦ f x / x)]
  linear_combination (r ^ a / Real.Gamma a) * hFTC

end A4Research
