import A3.ComplexGaussianRotation

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ComplexOrder

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000

theorem circularGaussianVector_integral_quadratic {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (hlambda : ∀ i, htheta.eigenvalues i < 1) (b : Fin d → ℂ) :
    (∫ z : Fin d → ℂ,
      Real.exp ((star z ⬝ᵥ (theta *ᵥ z)).re + 2 * (star b ⬝ᵥ z).re)
      ∂LogdetLean.GramHafnian.circularGaussianVector d) =
      (∏ i, (1 - htheta.eigenvalues i)⁻¹) *
        Real.exp (∑ i, Complex.normSq (complexGaussianEigenRotate htheta b i) /
          (1 - htheta.eigenvalues i)) := by
  let f : (Fin d → ℂ) → ℝ := fun z ↦ Real.exp
    (∑ i, (htheta.eigenvalues i * Complex.normSq (z i) +
      2 * (star (complexGaussianEigenRotate htheta b i) * z i).re))
  have hp (z : Fin d → ℂ) :
      Real.exp ((star z ⬝ᵥ (theta *ᵥ z)).re + 2 * (star b ⬝ᵥ z).re) =
        f (complexGaussianEigenRotate htheta z) := by
    dsimp only [f]
    rw [complexGaussianEigenRotate_quadratic htheta z,
      ← complexGaussianEigenRotate_preserves_inner htheta b z]
    congr 1
    simp [dotProduct, Complex.mul_re, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  calc
    _ = ∫ z : Fin d → ℂ, f (complexGaussianEigenRotate htheta z)
        ∂LogdetLean.GramHafnian.circularGaussianVector d :=
      integral_congr_ae (Filter.Eventually.of_forall hp)
    _ = ∫ z : Fin d → ℂ, f z ∂LogdetLean.GramHafnian.circularGaussianVector d :=
      (measurePreserving_complexGaussianEigenRotate htheta).integral_comp' f
    _ = _ := circularGaussianVector_integral_diagonal_quadratic
      htheta.eigenvalues (complexGaussianEigenRotate htheta b) hlambda

theorem complexGaussianTilt_diagonalization {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian) :
    1 - theta =
      (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        Matrix.diagonal (fun i ↦ ((1 - htheta.eigenvalues i : ℝ) : ℂ)) *
          star (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) := by
  let U : Matrix (Fin d) (Fin d) ℂ := htheta.eigenvectorUnitary
  let D : Matrix (Fin d) (Fin d) ℂ := Matrix.diagonal (fun i ↦ (htheta.eigenvalues i : ℂ))
  have hspec : theta = U * D * star U := by
    simpa [U, D, Function.comp_def, Unitary.conjStarAlgAut_apply] using htheta.spectral_theorem
  have hu : U * star U = 1 := by
    dsimp [U]
    rw [← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hone : (1 : Matrix (Fin d) (Fin d) ℂ) = U * 1 * star U := by
    rw [Matrix.mul_one, hu]
  have hd : (1 : Matrix (Fin d) (Fin d) ℂ) - D =
      Matrix.diagonal (fun i ↦ ((1 - htheta.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [D, hij]
  calc
    1 - theta = 1 - U * D * star U := by rw [hspec]
    _ = U * 1 * star U - U * D * star U := by rw [← hone]
    _ = U * (1 - D) * star U := by noncomm_ring
    _ = _ := by rw [hd]

theorem complexGaussianTilt_det {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian) :
    (1 - theta).det = ((∏ i, (1 - htheta.eigenvalues i) : ℝ) : ℂ) := by
  let U : Matrix (Fin d) (Fin d) ℂ := htheta.eigenvectorUnitary
  have hu : U * star U = 1 := by
    dsimp [U]
    rw [← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hdet : U.det * (star U).det = 1 := by
    rw [← Matrix.det_mul, hu, Matrix.det_one]
  rw [complexGaussianTilt_diagonalization htheta, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_diagonal]
  change U.det * (∏ i, ((1 - htheta.eigenvalues i : ℝ) : ℂ)) * (star U).det = _
  rw [mul_right_comm, hdet, one_mul]
  exact (map_prod Complex.ofRealHom (fun i ↦ 1 - htheta.eigenvalues i) Finset.univ).symm

theorem complexGaussianTilt_inverse_diagonalization {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (1 - theta)⁻¹ =
      (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        Matrix.diagonal (fun i ↦ (((1 - htheta.eigenvalues i)⁻¹ : ℝ) : ℂ)) *
          star (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) := by
  let U : Matrix (Fin d) (Fin d) ℂ := htheta.eigenvectorUnitary
  have hu : U * star U = 1 := by
    dsimp [U]
    rw [← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hus : star U * U = 1 := by
    dsimp [U]
    rw [Unitary.coe_star_mul_self]
  have hUi : U⁻¹ = star U := Matrix.inv_eq_right_inv hu
  have hUis : (star U)⁻¹ = U := Matrix.inv_eq_right_inv hus
  have hD : (Matrix.diagonal (fun i ↦ ((1 - htheta.eigenvalues i : ℝ) : ℂ)))⁻¹ =
      Matrix.diagonal (fun i ↦ (((1 - htheta.eigenvalues i)⁻¹ : ℝ) : ℂ)) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      have hz : (1 - (htheta.eigenvalues i : ℂ)) ≠ 0 := by
        have hr := Complex.ofReal_ne_zero.mpr
          (sub_pos.mpr (hermitian_eigenvalues_lt_one htheta hpos i)).ne'
        simpa using hr
      simp [hz]
    · simp [hij]
  rw [complexGaussianTilt_diagonalization htheta]
  change (U * Matrix.diagonal (fun i ↦ ((1 - htheta.eigenvalues i : ℝ) : ℂ)) * star U)⁻¹ = _
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, hUi, hUis, hD, Matrix.mul_assoc]

theorem complexGaussianTilt_inverse_quadratic {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℂ) :
    (star b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)).re =
      ∑ i, Complex.normSq (complexGaussianEigenRotate htheta b i) /
        (1 - htheta.eigenvalues i) := by
  rw [complexGaussianTilt_inverse_diagonalization htheta hpos]
  simp only [Matrix.star_eq_conjTranspose]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hleft : star b ᵥ* (htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) =
      star ((htheta.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ).conjTranspose *ᵥ b) := by
    simp [Matrix.star_mulVec]
  rw [hleft, ← complexGaussianEigenRotate_eq_mulVec htheta b]
  simp only [Matrix.mulVec_diagonal, dotProduct, Complex.re_sum, Pi.star_apply,
    Complex.star_def]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm, ← Complex.normSq_eq_conj_mul_self]
  rw [← Complex.ofReal_mul, Complex.ofReal_re]
  simp only [div_eq_mul_inv, mul_comm]

/-- Exact complex isotropic Gaussian quadratic-affine integral in determinant/inverse form. -/
theorem circularGaussianVector_integral_quadratic_det {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℂ) :
    (∫ z : Fin d → ℂ,
      Real.exp ((star z ⬝ᵥ (theta *ᵥ z)).re + 2 * (star b ⬝ᵥ z).re)
      ∂LogdetLean.GramHafnian.circularGaussianVector d) =
      ((1 - theta).det.re)⁻¹ * Real.exp ((star b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)).re) := by
  rw [circularGaussianVector_integral_quadratic htheta
    (hermitian_eigenvalues_lt_one htheta hpos),
    complexGaussianTilt_inverse_quadratic htheta hpos b, complexGaussianTilt_det htheta]
  simp only [Complex.ofReal_re, Finset.prod_inv_distrib]

theorem circularGaussianVector_integrable_quadratic {d : ℕ}
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℂ) :
    Integrable (fun z : Fin d → ℂ ↦
      Real.exp ((star z ⬝ᵥ (theta *ᵥ z)).re + 2 * (star b ⬝ᵥ z).re))
      (LogdetLean.GramHafnian.circularGaussianVector d) := by
  apply Integrable.of_integral_ne_zero
  rw [circularGaussianVector_integral_quadratic htheta
    (hermitian_eigenvalues_lt_one htheta hpos)]
  apply (mul_pos _ (Real.exp_pos _)).ne'
  exact Finset.prod_pos fun i _ ↦ inv_pos.mpr
    (sub_pos.mpr (hermitian_eigenvalues_lt_one htheta hpos i))

end A3Research
