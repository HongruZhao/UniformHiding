import LogdetLean.GramHafnian.ShiftedAnticoncentration.FourierCompression.BilinearGaussianKernel
import LogdetLean.GramHafnian.ShiftedAnticoncentration.GaussianDisk

/-!
# The noncentral circular-Gaussian Laplace kernel

This file evaluates the exact Laplace kernel of a transpose-linear form of
iid paper-normalized circular complex Gaussians, including an arbitrary
deterministic complex shift.  The proof reduces the linear form to one scaled
circular Gaussian, realizes that Gaussian by two independent real standard
Gaussians, and applies the existing one-dimensional completed-square formula
to each real coordinate.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Real

namespace LogdetLean.GramHafnian

noncomputable section

private theorem integral_exp_neg_mul_sq_affine_gaussianReal
    (a c t : ℝ) (ht : 0 ≤ t) :
    (∫ x : ℝ, Real.exp (-t * (a * x + c) ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 + 2 * t * a ^ 2))⁻¹ *
        Real.exp (-t * c ^ 2 / (1 + 2 * t * a ^ 2)) := by
  let lambda : ℝ := 1 + 2 * t * a ^ 2
  let d : ℂ := ((-2 * t * a * c : ℝ) : ℂ)
  have hlambda : 0 < lambda := by
    dsimp [lambda]
    positivity
  have htilt := integral_cexp_tilted_standardGaussian lambda hlambda d
  have hargReal :
      -t * c ^ 2 + (-2 * t * a * c) ^ 2 / (2 * lambda) =
        -t * c ^ 2 / lambda := by
    field_simp [ne_of_gt hlambda]
    dsimp [lambda]
    ring
  have harg :
      (((-t * c ^ 2 : ℝ) : ℂ) + d ^ 2 / (2 * lambda)) =
        (((-t * c ^ 2 / lambda : ℝ) : ℂ)) := by
    dsimp [d]
    exact_mod_cast hargReal
  have hkernel :
      (fun x : ℝ => Complex.exp (((-t * (a * x + c) ^ 2 : ℝ) : ℂ))) =
        fun x : ℝ =>
          Complex.exp (((-t * c ^ 2 : ℝ) : ℂ)) *
            Complex.exp
              (-(((lambda - 1) / 2 : ℝ) : ℂ) * (x : ℂ) ^ 2 + d * x) := by
    funext x
    rw [← Complex.exp_add]
    congr 1
    dsimp [lambda, d]
    push_cast
    ring
  have hcomplex :
      (∫ x : ℝ, Complex.exp (((-t * (a * x + c) ^ 2 : ℝ) : ℂ))
          ∂gaussianReal 0 1) =
        (((Real.sqrt lambda)⁻¹ *
          Real.exp (-t * c ^ 2 / lambda) : ℝ) : ℂ) := by
    rw [hkernel, integral_const_mul, htilt]
    calc
      Complex.exp (((-t * c ^ 2 : ℝ) : ℂ)) *
          (((Real.sqrt lambda)⁻¹ : ℂ) *
            Complex.exp (d ^ 2 / (2 * lambda))) =
          (((Real.sqrt lambda)⁻¹ : ℂ) *
            Complex.exp
              (((-t * c ^ 2 : ℝ) : ℂ) + d ^ 2 / (2 * lambda))) := by
                rw [Complex.exp_add]
                ring
      _ = (((Real.sqrt lambda)⁻¹ : ℂ) *
            Complex.exp (((-t * c ^ 2 / lambda : ℝ) : ℂ))) := by
              rw [harg]
      _ = (((Real.sqrt lambda)⁻¹ *
            Real.exp (-t * c ^ 2 / lambda) : ℝ) : ℂ) := by
              rw [Complex.ofReal_mul, Complex.ofReal_inv,
                Complex.ofReal_exp]
  have hint : Integrable
      (fun x : ℝ => Complex.exp (((-t * (a * x + c) ^ 2 : ℝ) : ℂ)))
      (gaussianReal 0 1) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    rw [Complex.norm_exp_ofReal]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _))
  calc
    (∫ x : ℝ, Real.exp (-t * (a * x + c) ^ 2) ∂gaussianReal 0 1) =
        Complex.re
          (∫ x : ℝ, Complex.exp (((-t * (a * x + c) ^ 2 : ℝ) : ℂ))
            ∂gaussianReal 0 1) := by
      simpa only [RCLike.re_eq_complex_re, Complex.exp_ofReal_re] using
        integral_re hint
    _ = (Real.sqrt (1 + 2 * t * a ^ 2))⁻¹ *
          Real.exp (-t * c ^ 2 / (1 + 2 * t * a ^ 2)) := by
      rw [hcomplex]
      change (Real.sqrt lambda)⁻¹ * Real.exp (-t * c ^ 2 / lambda) = _
      rfl

private theorem integral_exp_neg_norm_sq_sqrt_smul_add_circular
    (V : ℝ) (hV : 0 ≤ V) (b : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ z : ℂ, Real.exp (-t * ‖Real.sqrt V • z + b‖ ^ 2) ∂circularGaussian) =
      (1 + t * V)⁻¹ * Real.exp (-t * ‖b‖ ^ 2 / (1 + t * V)) := by
  rw [circularGaussian,
    integral_map measurable_circularGaussianCoordinate.aemeasurable (by fun_prop)]
  let a : ℝ := Real.sqrt V * Real.sqrt 2 / 2
  have haSq : a ^ 2 = V / 2 := by
    dsimp [a]
    rw [div_pow, mul_pow, Real.sq_sqrt hV,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hdenom : 0 < 1 + t * V := by
    positivity
  have hnorm (q : ℝ × ℝ) :
      ‖Real.sqrt V • circularGaussianCoordinate q + b‖ ^ 2 =
        (a * q.1 + b.re) ^ 2 + (a * q.2 + b.im) ^ 2 := by
    have hre : (Real.sqrt V • circularGaussianCoordinate q + b).re =
        a * q.1 + b.re := by
      dsimp [a, circularGaussianCoordinate]
      simp [div_eq_mul_inv]
      ring
    have him : (Real.sqrt V • circularGaussianCoordinate q + b).im =
        a * q.2 + b.im := by
      dsimp [a, circularGaussianCoordinate]
      simp [div_eq_mul_inv]
      ring
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  simp_rw [hnorm]
  have hsplit :
      (fun q : ℝ × ℝ =>
        Real.exp (-t * ((a * q.1 + b.re) ^ 2 + (a * q.2 + b.im) ^ 2))) =
      (fun q : ℝ × ℝ =>
        Real.exp (-t * (a * q.1 + b.re) ^ 2) *
          Real.exp (-t * (a * q.2 + b.im) ^ 2)) := by
    funext q
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit]
  let f : ℝ → ℝ := fun x => Real.exp (-t * (a * x + b.re) ^ 2)
  let g : ℝ → ℝ := fun x => Real.exp (-t * (a * x + b.im) ^ 2)
  have hf : Integrable f (gaussianReal 0 1) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _))
  have hg : Integrable g (gaussianReal 0 1) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _))
  have hfg : Integrable
      (fun q : ℝ × ℝ => f q.1 * g q.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    hf.mul_prod hg
  have hdenomEq : 1 + 2 * t * a ^ 2 = 1 + t * V := by
    rw [haSq]
    ring
  have hsqrtDenomSq : (Real.sqrt (1 + t * V)) ^ 2 = 1 + t * V :=
    Real.sq_sqrt hdenom.le
  have hsqrtDenomNe : Real.sqrt (1 + t * V) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hdenom)
  have hprefactor :
      (Real.sqrt (1 + t * V))⁻¹ * (Real.sqrt (1 + t * V))⁻¹ =
        (1 + t * V)⁻¹ := by
    field_simp [hsqrtDenomNe, hdenom.ne']
    nlinarith
  have hexponential :
      Real.exp (-t * b.re ^ 2 / (1 + t * V)) *
          Real.exp (-t * b.im ^ 2 / (1 + t * V)) =
        Real.exp (-t * ‖b‖ ^ 2 / (1 + t * V)) := by
    rw [← Real.exp_add]
    congr 1
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  calc
    (∫ q : ℝ × ℝ,
        Real.exp (-t * (a * q.1 + b.re) ^ 2) *
          Real.exp (-t * (a * q.2 + b.im) ^ 2)
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1))) =
      ∫ x : ℝ, ∫ y : ℝ, f x * g y ∂gaussianReal 0 1
        ∂gaussianReal 0 1 := by
          simpa [f, g] using integral_prod (fun q : ℝ × ℝ => f q.1 * g q.2) hfg
    _ = (∫ x : ℝ, f x ∂gaussianReal 0 1) *
          (∫ y : ℝ, g y ∂gaussianReal 0 1) := by
            simp_rw [integral_const_mul]
            rw [integral_mul_const]
    _ = ((Real.sqrt (1 + t * V))⁻¹ *
          Real.exp (-t * b.re ^ 2 / (1 + t * V))) *
        ((Real.sqrt (1 + t * V))⁻¹ *
          Real.exp (-t * b.im ^ 2 / (1 + t * V))) := by
            rw [show (∫ x : ℝ, f x ∂gaussianReal 0 1) =
                (Real.sqrt (1 + t * V))⁻¹ *
                  Real.exp (-t * b.re ^ 2 / (1 + t * V)) by
              simpa [f, hdenomEq] using
                integral_exp_neg_mul_sq_affine_gaussianReal a b.re t ht]
            rw [show (∫ x : ℝ, g x ∂gaussianReal 0 1) =
                (Real.sqrt (1 + t * V))⁻¹ *
                  Real.exp (-t * b.im ^ 2 / (1 + t * V)) by
              simpa [g, hdenomEq] using
                integral_exp_neg_mul_sq_affine_gaussianReal a b.im t ht]
    _ = (1 + t * V)⁻¹ *
          Real.exp (-t * ‖b‖ ^ 2 / (1 + t * V)) := by
            calc
              ((Real.sqrt (1 + t * V))⁻¹ *
                    Real.exp (-t * b.re ^ 2 / (1 + t * V))) *
                  ((Real.sqrt (1 + t * V))⁻¹ *
                    Real.exp (-t * b.im ^ 2 / (1 + t * V))) =
                ((Real.sqrt (1 + t * V))⁻¹ *
                    (Real.sqrt (1 + t * V))⁻¹) *
                  (Real.exp (-t * b.re ^ 2 / (1 + t * V)) *
                    Real.exp (-t * b.im ^ 2 / (1 + t * V))) := by ring
              _ = (1 + t * V)⁻¹ *
                    Real.exp (-t * ‖b‖ ^ 2 / (1 + t * V)) := by
                      rw [hprefactor, hexponential]

/-- Exact noncentral Laplace kernel for a transpose-linear form of iid
paper-normalized circular complex Gaussians.  The statement includes zero
coefficient energy. -/
theorem integral_exp_neg_norm_sq_iidCircularTransposeLinearForm_add
    {k : ℕ} (y : Fin k → ℂ) (b : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : Fin k → ℂ,
        Real.exp (-t * ‖iidCircularTransposeLinearForm y x + b‖ ^ 2)
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian)) =
      (1 + t * circularCoefficientEnergy y)⁻¹ *
        Real.exp
          (-t * ‖b‖ ^ 2 / (1 + t * circularCoefficientEnergy y)) := by
  let mu : Measure (Fin k → ℂ) := Measure.pi fun _ : Fin k ↦ circularGaussian
  let F : ℂ → ℝ := fun z => Real.exp (-t * ‖z + b‖ ^ 2)
  have hpush :
      (∫ x : Fin k → ℂ, F (iidCircularTransposeLinearForm y x) ∂mu) =
        ∫ z : ℂ, F z ∂mu.map (iidCircularTransposeLinearForm y) := by
    symm
    exact integral_map
      (measurable_iidCircularTransposeLinearForm y).aemeasurable (by fun_prop)
  calc
    (∫ x : Fin k → ℂ,
        Real.exp (-t * ‖iidCircularTransposeLinearForm y x + b‖ ^ 2) ∂mu) =
      ∫ z : ℂ, F z ∂mu.map (iidCircularTransposeLinearForm y) := by
        simpa [F] using hpush
    _ = ∫ z : ℂ, F z
          ∂circularGaussian.map (fun w : ℂ =>
            Real.sqrt (circularCoefficientEnergy y) • w) := by
          rw [show mu.map (iidCircularTransposeLinearForm y) =
              circularGaussian.map (fun w : ℂ =>
                Real.sqrt (circularCoefficientEnergy y) • w) by
            simpa [mu] using map_iidCircularTransposeLinearForm_eq_scaled_circular y]
    _ = ∫ w : ℂ,
          F (Real.sqrt (circularCoefficientEnergy y) • w) ∂circularGaussian := by
            exact integral_map (by fun_prop) (by fun_prop)
    _ = (1 + t * circularCoefficientEnergy y)⁻¹ *
          Real.exp
            (-t * ‖b‖ ^ 2 / (1 + t * circularCoefficientEnergy y)) := by
              simpa [F] using
                integral_exp_neg_norm_sq_sqrt_smul_add_circular
                  (circularCoefficientEnergy y)
                  (circularCoefficientEnergy_nonneg y) b t ht

/-- Centered form of the exact circular-Gaussian Laplace kernel. -/
theorem integral_exp_neg_norm_sq_iidCircularTransposeLinearForm
    {k : ℕ} (y : Fin k → ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : Fin k → ℂ,
        Real.exp (-t * ‖iidCircularTransposeLinearForm y x‖ ^ 2)
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian)) =
      (1 + t * circularCoefficientEnergy y)⁻¹ := by
  simpa using
    integral_exp_neg_norm_sq_iidCircularTransposeLinearForm_add
      y (0 : ℂ) t ht

/-- Dropping the noncentral exponential gives the centered reciprocal-kernel
upper bound. -/
theorem integral_exp_neg_norm_sq_iidCircularTransposeLinearForm_add_le
    {k : ℕ} (y : Fin k → ℂ) (b : ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : Fin k → ℂ,
        Real.exp (-t * ‖iidCircularTransposeLinearForm y x + b‖ ^ 2)
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian)) ≤
      (1 + t * circularCoefficientEnergy y)⁻¹ := by
  rw [integral_exp_neg_norm_sq_iidCircularTransposeLinearForm_add y b t ht]
  have hdenom : 0 < 1 + t * circularCoefficientEnergy y := by
    nlinarith [mul_nonneg ht (circularCoefficientEnergy_nonneg y)]
  have hexponent :
      -t * ‖b‖ ^ 2 / (1 + t * circularCoefficientEnergy y) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (sq_nonneg _))
      hdenom.le
  calc
    (1 + t * circularCoefficientEnergy y)⁻¹ *
        Real.exp
          (-t * ‖b‖ ^ 2 / (1 + t * circularCoefficientEnergy y)) ≤
      (1 + t * circularCoefficientEnergy y)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr hexponent) (inv_nonneg.mpr hdenom.le)
    _ = (1 + t * circularCoefficientEnergy y)⁻¹ := by ring

end

end LogdetLean.GramHafnian
