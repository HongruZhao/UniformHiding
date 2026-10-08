import A3.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace A3Research

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem wishart_map_invSqrtTwo_gaussian :
    (gaussianReal 0 1).map (fun x : ℝ ↦ (Real.sqrt 2)⁻¹ * x) =
      gaussianReal 0 (1 / 2) := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  ext
  simp only [NNReal.coe_mk, NNReal.coe_one, mul_one,
    NNReal.coe_div, NNReal.coe_ofNat]
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

def complexHalfGaussianDensity (z : ℂ) : ℝ≥0∞ :=
  gaussianPDF 0 (1 / 2) z.re * gaussianPDF 0 (1 / 2) z.im

theorem measurable_complexHalfGaussianDensity : Measurable complexHalfGaussianDensity := by
  unfold complexHalfGaussianDensity
  fun_prop

/-- The circular Gaussian in the original target has independent variance-half
real and imaginary parts. -/
theorem circularGaussian_eq_map_halfGaussian :
    LogdetLean.GramHafnian.circularGaussian =
      Measure.map Complex.measurableEquivRealProd.symm
        ((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2))) := by
  rw [← wishart_map_invSqrtTwo_gaussian,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  rw [Measure.map_map Complex.measurableEquivRealProd.symm.measurable (by fun_prop)]
  unfold LogdetLean.GramHafnian.circularGaussian
  congr 1
  funext q
  apply Complex.ext <;>
    simp [LogdetLean.GramHafnian.circularGaussianCoordinate, div_eq_mul_inv] <;>
    field_simp <;> rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Exact density with respect to actual complex Lebesgue measure. -/
theorem circularGaussian_eq_withDensity :
    LogdetLean.GramHafnian.circularGaussian =
      (volume : Measure ℂ).withDensity complexHalfGaussianDensity := by
  rw [circularGaussian_eq_map_halfGaussian,
    gaussianReal_of_var_ne_zero 0 (by norm_num : (1 / 2 : ℝ≥0) ≠ 0),
    prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _)]
  have hcomp : (fun q : ℝ × ℝ ↦ gaussianPDF 0 (1 / 2) q.1 * gaussianPDF 0 (1 / 2) q.2) =
      complexHalfGaussianDensity ∘ Complex.measurableEquivRealProd.symm := by
    funext q
    rfl
  rw [hcomp]
  ext s hs
  rw [Measure.map_apply Complex.measurableEquivRealProd.symm.measurable hs,
    withDensity_apply _ (hs.preimage Complex.measurableEquivRealProd.symm.measurable),
    withDensity_apply _ hs]
  have h := setLIntegral_map hs measurable_complexHalfGaussianDensity
    Complex.measurableEquivRealProd.symm.measurable
    (μ := (volume : Measure (ℝ × ℝ)))
  rw [Complex.volume_preserving_equiv_real_prod.symm.map_eq] at h
  simpa only [Function.comp_apply, Measure.volume_eq_prod] using h.symm

theorem gaussianHalf_pdf_real (x : ℝ) :
    gaussianPDFReal 0 (1 / 2) x = (Real.sqrt Real.pi)⁻¹ * Real.exp (-x ^ 2) := by
  simp only [gaussianPDFReal, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat,
    sub_zero]
  congr 1
  · congr 1
    ring
  · congr 1
    ring

theorem complexHalfGaussianDensity_eq_kernel (z : ℂ) :
    complexHalfGaussianDensity z =
      ENNReal.ofReal (Real.pi⁻¹ * Real.exp (-Complex.normSq z)) := by
  unfold complexHalfGaussianDensity
  simp only [gaussianPDF_def, gaussianHalf_pdf_real]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hconst : (Real.sqrt Real.pi)⁻¹ * (Real.sqrt Real.pi)⁻¹ = Real.pi⁻¹ := by
    rw [← mul_inv_rev, Real.mul_self_sqrt Real.pi_pos.le]
  rw [mul_mul_mul_comm, hconst, ← Real.exp_add]
  congr 2
  simp only [Complex.normSq_apply]
  ring

theorem circularGaussian_isProbabilityMeasure :
    IsProbabilityMeasure LogdetLean.GramHafnian.circularGaussian := by
  rw [circularGaussian_eq_map_halfGaussian]
  exact Measure.isProbabilityMeasure_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable

end A3Research
