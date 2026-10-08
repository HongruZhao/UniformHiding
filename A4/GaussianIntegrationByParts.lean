import A4.TriangularGaussianLaplace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace A4Research

def gaussianHalfKernel (x : ℝ) : ℝ := Real.exp (-(x ^ 2))

theorem hasDerivAt_gaussianHalfKernel (x : ℝ) :
    HasDerivAt gaussianHalfKernel (-2 * x * gaussianHalfKernel x) x := by
  unfold gaussianHalfKernel
  convert ((hasDerivAt_id x).pow 2).neg.exp using 1 <;>
    first | rfl | (simp only [Pi.neg_apply, Pi.pow_apply, id_eq,
      Nat.cast_ofNat, pow_one, mul_one] <;> ring)

theorem gaussianHalf_integral_eq_kernel (f : ℝ → ℝ) :
    (∫ x, f x ∂gaussianReal 0 (1 / 2)) =
      (Real.sqrt Real.pi)⁻¹ * ∫ x, gaussianHalfKernel x * f x := by
  rw [integral_gaussianReal_eq_integral_smul (v := (1 / 2 : NNReal)) (by norm_num)]
  simp only [smul_eq_mul, gaussianPDFReal, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat, sub_zero]
  norm_num only [mul_div_cancel_right₀, mul_one, mul_div_assoc,
    div_self (show (2 : ℝ) ≠ 0 by norm_num), div_one]
  rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring]
  change (∫ x, (Real.sqrt Real.pi)⁻¹ * gaussianHalfKernel x * f x) = _
  simp_rw [mul_assoc]
  exact integral_const_mul _ _

/-- Gaussian integration by parts from the actual density and the improper
fundamental theorem of calculus. The boundary and integrability obligations
are explicit, for application to the inverse-moment Bartlett slices. -/
theorem gaussianHalf_integrationByParts (f f' : ℝ → ℝ)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hbot : Tendsto (fun x ↦ gaussianHalfKernel x * f x) atBot (𝓝 0))
    (htop : Tendsto (fun x ↦ gaussianHalfKernel x * f x) atTop (𝓝 0))
    (hderivint : Integrable (fun x ↦ gaussianHalfKernel x * f' x))
    (hxint : Integrable (fun x ↦ gaussianHalfKernel x * (x * f x))) :
    (∫ x, f' x ∂gaussianReal 0 (1 / 2)) =
      2 * (∫ x, x * f x ∂gaussianReal 0 (1 / 2)) := by
  let g' : ℝ → ℝ := fun x ↦ gaussianHalfKernel x * f' x -
    2 * (gaussianHalfKernel x * (x * f x))
  have hgderiv : ∀ x,
      HasDerivAt (fun y ↦ gaussianHalfKernel y * f y) (g' x) x := by
    intro x
    apply ((hasDerivAt_gaussianHalfKernel x).mul (hderiv x)).congr_deriv
    dsimp only [g']
    ring
  have hgint : Integrable g' := hderivint.sub (hxint.const_mul 2)
  have hFTC := integral_of_hasDerivAt_of_tendsto hgderiv hgint hbot htop
  simp only [sub_self] at hFTC
  dsimp only [g'] at hFTC
  rw [integral_sub hderivint (hxint.const_mul 2), integral_const_mul] at hFTC
  rw [gaussianHalf_integral_eq_kernel f',
    gaussianHalf_integral_eq_kernel (fun x ↦ x * f x)]
  linear_combination (Real.sqrt Real.pi)⁻¹ * hFTC

end A4Research
