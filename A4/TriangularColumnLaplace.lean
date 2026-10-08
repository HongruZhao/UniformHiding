import A4.TriangularGaussianLaplace
import A4.WishartDensityGamma

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix

noncomputable section

namespace A4Research

/-- The complete exponent for one Bartlett column: one squared Gamma pivot
and a real Gaussian tail of arbitrary finite dimension. -/
def bartlettColumnTilt {d : ℕ} (c : ℝ) (theta : Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → ℝ) (t : ℝ) (z : Fin d → ℝ) : ℝ :=
  Real.exp (c * t + z ⬝ᵥ (theta *ᵥ z) + 2 * Real.sqrt t * (b ⬝ᵥ z))

theorem bartlettColumnTilt_factor {d : ℕ} (c : ℝ)
    (theta : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (t : ℝ) (z : Fin d → ℝ) :
    bartlettColumnTilt c theta b t z =
      Real.exp (c * t) *
        Real.exp (z ⬝ᵥ (theta *ᵥ z) + 2 * ((Real.sqrt t • b) ⬝ᵥ z)) := by
  rw [bartlettColumnTilt, ← Real.exp_add, smul_dotProduct]
  congr 1
  simp only [smul_eq_mul]
  ring

theorem bartlettColumn_scaled_inverse_quadratic {d : ℕ}
    (theta : Matrix (Fin d) (Fin d) ℝ) (b : Fin d → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (Real.sqrt t • b) ⬝ᵥ ((1 - theta)⁻¹ *ᵥ (Real.sqrt t • b)) =
      t * (b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  calc
    _ = Real.sqrt t ^ 2 * (b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)) := by ring
    _ = _ := by rw [Real.sq_sqrt ht]

theorem bartlettColumn_integrable_gaussian {d : ℕ} (c : ℝ)
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℝ) (t : ℝ) :
    Integrable (bartlettColumnTilt c theta b t)
      (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))) := by
  have hf := (gaussianHalfVector_integrable_quadratic htheta hpos
    (Real.sqrt t • b)).const_mul (Real.exp (c * t))
  exact hf.congr (Filter.Eventually.of_forall fun z =>
    (bartlettColumnTilt_factor c theta b t z).symm)

/-- The exact Gaussian-tail integration, before the real-shape pivot is
integrated. The resulting scalar rate is the block Schur complement. -/
theorem bartlettColumn_integral_gaussian {d : ℕ} (c : ℝ)
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ z : Fin d → ℝ, bartlettColumnTilt c theta b t z
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))) =
      Matrix.det (1 - theta) ^ (-1 / 2 : ℝ) *
        Real.exp ((c + b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)) * t) := by
  simp_rw [bartlettColumnTilt_factor]
  rw [integral_const_mul, gaussianHalfVector_integral_quadratic_det htheta hpos,
    bartlettColumn_scaled_inverse_quadratic theta b t ht]
  calc
    _ = Matrix.det (1 - theta) ^ (-1 / 2 : ℝ) *
        (Real.exp (c * t) * Real.exp (t * (b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)))) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

/-- A full Bartlett column is integrable under the exact SPD Schur-domain
condition, for every real positive Gamma shape. -/
theorem bartlettColumn_integrable {d : ℕ} {a c : ℝ} (ha : 0 < a)
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℝ)
    (hgap : c + b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b) < 1) :
    Integrable (fun q : ℝ × (Fin d → ℝ) => bartlettColumnTilt c theta b q.1 q.2)
      ((gammaMeasure a 1).prod (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2)))) := by
  let := isProbabilityMeasure_gammaMeasure ha (by norm_num : (0 : ℝ) < 1)
  have hm : AEStronglyMeasurable
      (fun q : ℝ × (Fin d → ℝ) => bartlettColumnTilt c theta b q.1 q.2)
      ((gammaMeasure a 1).prod (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2)))) := by
    apply Measurable.aestronglyMeasurable
    unfold bartlettColumnTilt dotProduct Matrix.mulVec
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (bartlettColumn_integrable_gaussian c htheta hpos b)
  · have hf := (gammaMeasure_integrable_exp ha (by norm_num) hgap).const_mul
      (Matrix.det (1 - theta) ^ (-1 / 2 : ℝ))
    apply hf.congr
    filter_upwards [gammaMeasure_ae_pos a 1] with t ht
    simp only [bartlettColumnTilt, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (bartlettColumn_integral_gaussian c htheta hpos b t ht.le).symm

/-- The complete Gamma--Gaussian column transform for arbitrary real shape.
Both the Fubini step and scalar boundary integrability are proved. -/
theorem bartlettColumn_integral {d : ℕ} {a c : ℝ} (ha : 0 < a)
    {theta : Matrix (Fin d) (Fin d) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℝ)
    (hgap : c + b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b) < 1) :
    (∫ q : ℝ × (Fin d → ℝ), bartlettColumnTilt c theta b q.1 q.2
      ∂(gammaMeasure a 1).prod (Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2)))) =
      Matrix.det (1 - theta) ^ (-1 / 2 : ℝ) *
        (1 - (c + b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b))) ^ (-a) := by
  let := isProbabilityMeasure_gammaMeasure ha (by norm_num : (0 : ℝ) < 1)
  rw [MeasureTheory.integral_prod _ (bartlettColumn_integrable ha htheta hpos b hgap)]
  have heq : (fun t : ℝ => ∫ z : Fin d → ℝ, bartlettColumnTilt c theta b t z
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 (1 / 2))) =ᵐ[gammaMeasure a 1]
      (fun t => Matrix.det (1 - theta) ^ (-1 / 2 : ℝ) *
        Real.exp ((c + b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)) * t)) := by
    filter_upwards [gammaMeasure_ae_pos a 1] with t ht
    exact bartlettColumn_integral_gaussian c htheta hpos b t ht.le
  rw [integral_congr_ae heq, integral_const_mul,
    gammaMeasure_integral_exp ha (by norm_num) hgap, one_div,
    ← Real.rpow_neg_eq_inv_rpow]

end A4Research
