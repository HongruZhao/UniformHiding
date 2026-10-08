import A3.ComplexGaussianIsotropy

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section
namespace A3Research

theorem circularGaussian_integral_exp_quadratic (lambda : ℝ) (b : ℂ)
    (hlambda : lambda < 1) :
    (∫ z : ℂ, Real.exp (lambda * Complex.normSq z + 2 * Complex.re (star b * z))
      ∂LogdetLean.GramHafnian.circularGaussian) =
      (1 - lambda)⁻¹ * Real.exp (Complex.normSq b / (1 - lambda)) := by
  rw [circularGaussian_eq_map_halfGaussian,
    integral_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable
      (by fun_prop)]
  have hp (q : ℝ × ℝ) :
      Real.exp (lambda * Complex.normSq (Complex.measurableEquivRealProd.symm q) +
        2 * Complex.re (star b * Complex.measurableEquivRealProd.symm q)) =
      Real.exp (lambda * q.1 ^ 2 + 2 * b.re * q.1) *
        Real.exp (lambda * q.2 ^ 2 + 2 * b.im * q.2) := by
    rw [← Real.exp_add]
    congr 1
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    change lambda * (q.1 * q.1 + q.2 * q.2) + 2 * (b.re * q.1 - -b.im * q.2) = _
    ring
  simp_rw [hp]
  rw [integral_prod_mul
    (fun x : ℝ ↦ Real.exp (lambda * x ^ 2 + 2 * b.re * x))
    (fun x : ℝ ↦ Real.exp (lambda * x ^ 2 + 2 * b.im * x)),
    A4Research.gaussianHalf_integral_exp_quadratic lambda b.re hlambda,
    A4Research.gaussianHalf_integral_exp_quadratic lambda b.im hlambda,
    mul_mul_mul_comm, ← Real.exp_add]
  congr 1
  · rw [← mul_inv_rev, Real.mul_self_sqrt (sub_pos.mpr hlambda).le]
  · congr 1
    simp only [Complex.normSq_apply]
    ring

theorem circularGaussian_integrable_exp_quadratic (lambda : ℝ) (b : ℂ)
    (hlambda : lambda < 1) :
    Integrable (fun z : ℂ ↦
      Real.exp (lambda * Complex.normSq z + 2 * Complex.re (star b * z)))
      LogdetLean.GramHafnian.circularGaussian := by
  apply Integrable.of_integral_ne_zero
  rw [circularGaussian_integral_exp_quadratic lambda b hlambda]
  exact (mul_pos (inv_pos.mpr (sub_pos.mpr hlambda)) (Real.exp_pos _)).ne'

theorem circularGaussianVector_integral_diagonal_quadratic {d : ℕ}
    (lambda : Fin d → ℝ) (b : Fin d → ℂ) (hlambda : ∀ i, lambda i < 1) :
    (∫ z : Fin d → ℂ,
      Real.exp (∑ i, (lambda i * Complex.normSq (z i) + 2 * Complex.re (star (b i) * z i)))
      ∂LogdetLean.GramHafnian.circularGaussianVector d) =
      (∏ i, (1 - lambda i)⁻¹) *
        Real.exp (∑ i, Complex.normSq (b i) / (1 - lambda i)) := by
  unfold LogdetLean.GramHafnian.circularGaussianVector
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (fun i : Fin d ↦ fun z : ℂ ↦
    Real.exp (lambda i * Complex.normSq z + 2 * Complex.re (star (b i) * z)))]
  simp_rw [circularGaussian_integral_exp_quadratic _ _ (hlambda _)]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]

end A3Research
