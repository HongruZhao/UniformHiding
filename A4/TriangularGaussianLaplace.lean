import A4.Target
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Multivariate

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open scoped Matrix RealInnerProductSpace

noncomputable section

namespace A4Research

/-- The shifted quadratic integral of one variance-one-half real Gaussian.
The coefficient `b` is unrestricted, which is needed for a Bartlett column's
off-diagonal Schur-complement term. -/
theorem gaussianHalf_integral_exp_quadratic (lambda b : ℝ) (hlambda : lambda < 1) :
    (∫ x : ℝ, Real.exp (lambda * x ^ 2 + 2 * b * x)
      ∂gaussianReal 0 (1 / 2)) =
      (Real.sqrt (1 - lambda))⁻¹ * Real.exp (b ^ 2 / (1 - lambda)) := by
  rw [integral_gaussianReal_eq_integral_smul (v := (1 / 2 : NNReal)) (by norm_num)]
  simp only [smul_eq_mul, gaussianPDFReal, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat, sub_zero]
  norm_num only [mul_div_cancel_right₀, mul_one, mul_div_assoc,
    div_self (show (2 : ℝ) ≠ 0 by norm_num), div_one]
  rw [show 2 * Real.pi * (1 / 2) = Real.pi by ring]
  let c : ℝ := 1 - lambda
  have hc : 0 < c := sub_pos.mpr hlambda
  have hpoint (x : ℝ) :
      (Real.sqrt Real.pi)⁻¹ * Real.exp (-(x ^ 2)) *
        Real.exp (lambda * x ^ 2 + 2 * b * x) =
      ((Real.sqrt Real.pi)⁻¹ * Real.exp (b ^ 2 / c)) *
        Real.exp (-c * (x - b / c) ^ 2) := by
    simp only [mul_assoc]
    apply congrArg (fun y => (Real.sqrt Real.pi)⁻¹ * y)
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp [hc.ne']
    dsimp [c]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun x : ℝ => Real.exp (-c * x ^ 2)) (b / c),
    integral_gaussian c, Real.sqrt_div Real.pi_pos.le]
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  change (Real.sqrt Real.pi)⁻¹ * Real.exp (b ^ 2 / c) *
    (Real.sqrt Real.pi / Real.sqrt c) = _
  change _ = (Real.sqrt c)⁻¹ * Real.exp (b ^ 2 / c)
  field_simp

theorem gaussianHalf_integrable_exp_quadratic (lambda b : ℝ) (hlambda : lambda < 1) :
    Integrable (fun x : ℝ => Real.exp (lambda * x ^ 2 + 2 * b * x))
      (gaussianReal 0 (1 / 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussianHalf_integral_exp_quadratic lambda b hlambda]
  exact (mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hlambda)))
    (Real.exp_pos _)).ne'

/-- Exact shifted quadratic integration in an orthogonal eigenbasis. -/
theorem gaussianHalfVector_integral_diagonal_quadratic {d : ℕ}
    (lambda b : Fin d → ℝ) (hlambda : ∀ i, lambda i < 1) :
    (∫ x : Fin d → ℝ,
      Real.exp (∑ i : Fin d, (lambda i * x i ^ 2 + 2 * b i * x i))
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))) =
      (∏ i : Fin d, (Real.sqrt (1 - lambda i))⁻¹) *
        Real.exp (∑ i : Fin d, b i ^ 2 / (1 - lambda i)) := by
  simp_rw [Real.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (fun i : Fin d => fun x : ℝ => Real.exp (lambda i * x ^ 2 + 2 * b i * x))]
  simp_rw [gaussianHalf_integral_exp_quadratic _ _ (hlambda _)]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]

theorem map_invSqrtTwo_gaussian :
    (gaussianReal 0 1).map (fun x : ℝ => (Real.sqrt 2)⁻¹ * x) =
      gaussianReal 0 (1 / 2) := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  ext
  simp only [NNReal.coe_mk, NNReal.coe_one, mul_one,
    NNReal.coe_div, NNReal.coe_ofNat]
  rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem map_toLp_halfGaussianVector (d : ℕ) :
    (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))).map (WithLp.toLp 2) =
      (stdGaussian (EuclideanSpace ℝ (Fin d))).map
        (fun x : EuclideanSpace ℝ (Fin d) => (Real.sqrt 2)⁻¹ • x) := by
  let c : ℝ := (Real.sqrt 2)⁻¹
  let scaleRaw : (Fin d → ℝ) → (Fin d → ℝ) := fun x i => c * x i
  have hscaleRaw :
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map scaleRaw =
        Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2)) := by
    rw [Measure.pi_map_pi (fun _ =>
      (show Measurable (fun x : ℝ => c * x) by fun_prop).aemeasurable)]
    congr 1
    funext i
    exact map_invSqrtTwo_gaussian
  rw [← hscaleRaw, Measure.map_map
    (show Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) by fun_prop)
    (show Measurable scaleRaw by fun_prop), ← map_pi_eq_stdGaussian,
    Measure.map_map
      (show Measurable (fun x : EuclideanSpace ℝ (Fin d) => c • x) by fun_prop)
      (show Measurable (WithLp.toLp 2 : (Fin d → ℝ) → EuclideanSpace ℝ (Fin d)) by fun_prop)]
  apply Measure.map_congr
  filter_upwards [] with x
  ext i
  rfl

/-- Raw coordinates of a real Hermitian tilt's orthonormal eigenbasis. -/
def gaussianEigenRotate {d : ℕ} {theta : Matrix (Fin d) (Fin d) ℝ}
    (htheta : theta.IsHermitian) : (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin d → ℝ)).trans
    (htheta.eigenvectorBasis.repr.toMeasurableEquiv.trans
      (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm)

theorem gaussianEigenRotate_eq_mulVec {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (x : Fin d → ℝ) :
    gaussianEigenRotate htheta x =
      (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ *ᵥ x := by
  ext i
  change htheta.eigenvectorBasis.repr (WithLp.toLp 2 x) i = _
  rw [OrthonormalBasis.repr_apply_apply]
  simp [PiLp.inner_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem measurePreserving_gaussianEigenRotate {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian) :
    MeasurePreserving (gaussianEigenRotate htheta)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2)))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))) := by
  let E := EuclideanSpace ℝ (Fin d)
  let c : ℝ := (Real.sqrt 2)⁻¹
  let scale : E → E := fun x => c • x
  let eLp := MeasurableEquiv.toLp 2 (Fin d → ℝ)
  let eRep := htheta.eigenvectorBasis.repr.toMeasurableEquiv
  let muScaled : Measure E := (stdGaussian E).map scale
  have hLp : MeasurePreserving eLp
      (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))) muScaled := by
    refine ⟨eLp.measurable, ?_⟩
    change (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))).map
      (WithLp.toLp 2) = muScaled
    simpa [eLp, muScaled, scale, E, c] using map_toLp_halfGaussianVector d
  have hRep : MeasurePreserving eRep muScaled muScaled := by
    refine ⟨eRep.measurable, ?_⟩
    have hscale : Measurable scale := by fun_prop
    have hcomm : eRep ∘ scale = scale ∘ eRep := by
      funext x
      change htheta.eigenvectorBasis.repr (c • x) = c • htheta.eigenvectorBasis.repr x
      exact map_smul _ _ _
    dsimp only [muScaled]
    rw [Measure.map_map eRep.measurable hscale, hcomm,
      ← Measure.map_map hscale eRep.measurable]
    change (stdGaussian E |>.map htheta.eigenvectorBasis.repr).map scale = _
    rw [stdGaussian_map htheta.eigenvectorBasis.repr]
  exact (MeasurePreserving.symm eLp hLp).comp (hRep.comp hLp)

theorem gaussianEigenRotate_preserves_dotProduct {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (b x : Fin d → ℝ) :
    gaussianEigenRotate htheta b ⬝ᵥ gaussianEigenRotate htheta x = b ⬝ᵥ x := by
  have h := htheta.eigenvectorBasis.repr.inner_map_map (WithLp.toLp 2 b) (WithLp.toLp 2 x)
  change (htheta.eigenvectorBasis.repr (WithLp.toLp 2 b)).ofLp ⬝ᵥ
    (htheta.eigenvectorBasis.repr (WithLp.toLp 2 x)).ofLp = b ⬝ᵥ x
  change (htheta.eigenvectorBasis.repr (WithLp.toLp 2 x)).ofLp ⬝ᵥ
    (htheta.eigenvectorBasis.repr (WithLp.toLp 2 b)).ofLp = x ⬝ᵥ b at h
  exact (dotProduct_comm _ _).trans (h.trans (dotProduct_comm _ _))

theorem gaussianEigenRotate_quadratic {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (x : Fin d → ℝ) :
    x ⬝ᵥ (theta *ᵥ x) =
      ∑ i : Fin d, htheta.eigenvalues i * (gaussianEigenRotate htheta x i) ^ 2 := by
  conv_lhs => rw [htheta.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    RCLike.ofReal_real_eq_id, Function.id_comp]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, ← gaussianEigenRotate_eq_mulVec htheta x]
  simp only [Matrix.mulVec_diagonal, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Shifted Gaussian quadratic integration for an arbitrary real symmetric
matrix. The eigenbasis is transported by a proved measure-preserving map. -/
theorem gaussianHalfVector_integral_quadratic {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (hlambda : ∀ i : Fin d, htheta.eigenvalues i < 1) (b : Fin d → ℝ) :
    (∫ x : Fin d → ℝ, Real.exp (x ⬝ᵥ (theta *ᵥ x) + 2 * (b ⬝ᵥ x))
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))) =
      (∏ i : Fin d, (Real.sqrt (1 - htheta.eigenvalues i))⁻¹) *
        Real.exp (∑ i : Fin d,
          (gaussianEigenRotate htheta b i) ^ 2 / (1 - htheta.eigenvalues i)) := by
  let f : (Fin d → ℝ) → ℝ := fun x => Real.exp
    (∑ i : Fin d, (htheta.eigenvalues i * x i ^ 2 +
      2 * gaussianEigenRotate htheta b i * x i))
  have hp (x : Fin d → ℝ) :
      Real.exp (x ⬝ᵥ (theta *ᵥ x) + 2 * (b ⬝ᵥ x)) = f (gaussianEigenRotate htheta x) := by
    dsimp only [f]
    rw [gaussianEigenRotate_quadratic htheta x,
      ← gaussianEigenRotate_preserves_dotProduct htheta b x]
    congr 1
    simp only [dotProduct, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  calc
    _ = ∫ x : Fin d → ℝ, f (gaussianEigenRotate htheta x)
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2)) := by
      exact integral_congr_ae (Filter.Eventually.of_forall hp)
    _ = ∫ x : Fin d → ℝ, f x
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2)) :=
      (measurePreserving_gaussianEigenRotate htheta).integral_comp' f
    _ = _ := gaussianHalfVector_integral_diagonal_quadratic
      htheta.eigenvalues (gaussianEigenRotate htheta b) hlambda

/-- The SPD-domain assumption supplies the scalar conditions used in every
eigenbasis Gaussian integral. -/
theorem gaussianTilt_eigenvalues_lt_one {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (i : Fin d) : htheta.eigenvalues i < 1 := by
  let v : Fin d → ℝ := ⇑(htheta.eigenvectorBasis i)
  have hv : v ≠ 0 := (WithLp.ofLp_eq_zero 2).ne.mpr
    (htheta.eigenvectorBasis.orthonormal.ne_zero i)
  have hthetaV : theta *ᵥ v = htheta.eigenvalues i • v := by
    simpa [v] using htheta.mulVec_eigenvectorBasis i
  have honeSubV : (1 - theta) *ᵥ v = (1 - htheta.eigenvalues i) • v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hthetaV]
    ext j
    simp [sub_mul]
  have hquad := hpos.dotProduct_mulVec_pos hv
  rw [honeSubV, dotProduct_smul] at hquad
  have hvdot : 0 < star v ⬝ᵥ v := Matrix.dotProduct_star_self_pos_iff.mpr hv
  change 0 < (1 - htheta.eigenvalues i) * (star v ⬝ᵥ v) at hquad
  nlinarith

theorem gaussianHalfVector_integrable_quadratic {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℝ) :
    Integrable (fun x : Fin d → ℝ => Real.exp (x ⬝ᵥ (theta *ᵥ x) + 2 * (b ⬝ᵥ x)))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))) := by
  apply Integrable.of_integral_ne_zero
  rw [gaussianHalfVector_integral_quadratic htheta (gaussianTilt_eigenvalues_lt_one htheta hpos)]
  apply (mul_pos _ (Real.exp_pos _)).ne'
  apply Finset.prod_pos
  intro i _
  exact inv_pos.mpr (Real.sqrt_pos.mpr
    (sub_pos.mpr (gaussianTilt_eigenvalues_lt_one htheta hpos i)))

theorem gaussianTilt_diagonalization {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian) :
    1 - theta =
      (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *
        Matrix.diagonal (fun i => 1 - htheta.eigenvalues i) *
          star (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) := by
  let U : Matrix (Fin d) (Fin d) ℝ := htheta.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal htheta.eigenvalues
  have hspec : theta = U * D * star U := by
    simpa [U, D, Unitary.conjStarAlgAut_apply] using htheta.spectral_theorem
  have hu : U * star U = 1 := by
    dsimp [U]
    rw [← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hone : (1 : Matrix (Fin d) (Fin d) ℝ) = U * 1 * star U := by
    rw [Matrix.mul_one, hu]
  have hd : (1 : Matrix (Fin d) (Fin d) ℝ) - D =
      Matrix.diagonal (fun i => 1 - htheta.eigenvalues i) := by
    ext i j
    by_cases hij : i = j <;> simp [D, hij]
  calc
    1 - theta = 1 - (U * D * star U) := by rw [hspec]
    _ = U * 1 * star U - U * D * star U := by rw [← hone]
    _ = U * (1 - D) * star U := by noncomm_ring
    _ = _ := by rw [hd]

theorem gaussianTilt_det {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian) :
    Matrix.det (1 - theta) = ∏ i : Fin d, (1 - htheta.eigenvalues i) := by
  let U : Matrix (Fin d) (Fin d) ℝ := htheta.eigenvectorUnitary
  have hu : U * star U = 1 := by
    dsimp [U]
    rw [← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hdet : Matrix.det U * Matrix.det (star U) = 1 := by
    rw [← Matrix.det_mul, hu, Matrix.det_one]
  rw [gaussianTilt_diagonalization htheta, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal]
  change Matrix.det U * (∏ i : Fin d, (1 - htheta.eigenvalues i)) *
    Matrix.det (star U) = _
  calc
    _ = (Matrix.det U * Matrix.det (star U)) *
        (∏ i : Fin d, (1 - htheta.eigenvalues i)) := by ring
    _ = _ := by rw [hdet, one_mul]

theorem gaussianTilt_inverse_diagonalization {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (1 - theta)⁻¹ =
      (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *
        Matrix.diagonal (fun i => (1 - htheta.eigenvalues i)⁻¹) *
          star (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) := by
  let U : Matrix (Fin d) (Fin d) ℝ := htheta.eigenvectorUnitary
  have hu : U * star U = 1 := by
    dsimp [U]
    rw [← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hus : star U * U = 1 := by
    dsimp [U]
    rw [Unitary.coe_star_mul_self]
  have hUi : U⁻¹ = star U := Matrix.inv_eq_right_inv hu
  have hUis : (star U)⁻¹ = U := Matrix.inv_eq_right_inv hus
  have hD : (Matrix.diagonal (fun i => 1 - htheta.eigenvalues i))⁻¹ =
      Matrix.diagonal (fun i => (1 - htheta.eigenvalues i)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [(sub_pos.mpr (gaussianTilt_eigenvalues_lt_one htheta hpos i)).ne']
    · simp [hij]
  rw [gaussianTilt_diagonalization htheta]
  change (U * Matrix.diagonal (fun i => 1 - htheta.eigenvalues i) * star U)⁻¹ = _
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hUi, hUis, hD, Matrix.mul_assoc]

theorem gaussianTilt_inverse_quadratic {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℝ) :
    b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b) =
      ∑ i : Fin d, (gaussianEigenRotate htheta b i) ^ 2 / (1 - htheta.eigenvalues i) := by
  rw [gaussianTilt_inverse_diagonalization htheta hpos]
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, ← gaussianEigenRotate_eq_mulVec htheta b]
  simp only [Matrix.mulVec_diagonal, dotProduct, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Closed determinant/inverse form of the shifted Gaussian vector integral.
This is the exact column-integration input for Bartlett's arbitrary-real-shape
Wishart transform. -/
theorem gaussianHalfVector_integral_quadratic_det {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℝ) :
    (∫ x : Fin d → ℝ, Real.exp (x ⬝ᵥ (theta *ᵥ x) + 2 * (b ⬝ᵥ x))
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))) =
      Matrix.det (1 - theta) ^ (-1 / 2 : ℝ) *
        Real.exp (b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)) := by
  rw [gaussianHalfVector_integral_quadratic htheta
    (gaussianTilt_eigenvalues_lt_one htheta hpos),
    gaussianTilt_inverse_quadratic htheta hpos b]
  congr 1
  rw [gaussianTilt_det htheta]
  calc
    (∏ i : Fin d, (Real.sqrt (1 - htheta.eigenvalues i))⁻¹) =
        ∏ i : Fin d, (1 - htheta.eigenvalues i) ^ (-1 / 2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg
        (sub_pos.mpr (gaussianTilt_eigenvalues_lt_one htheta hpos i)).le]
      congr 1
      ring
    _ = _ := Real.finsetProd_rpow Finset.univ _
      (fun i _ => (sub_pos.mpr (gaussianTilt_eigenvalues_lt_one htheta hpos i)).le) _

end A4Research
