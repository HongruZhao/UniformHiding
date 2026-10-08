import A3.ComplexGaussianLaplace
import A3.HermitianLaplaceUniqueness
import A3.ComplexGaussianVectorProbability
import A4.WishartDensityGamma

open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ComplexOrder

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def complexBartlettColumnTilt {d : ℕ} (c : ℝ)
    (theta : Matrix (Fin d) (Fin d) ℂ) (b : Fin d → ℂ)
    (t : ℝ) (z : Fin d → ℂ) : ℝ :=
  Real.exp (c * t + (star z ⬝ᵥ (theta *ᵥ z)).re +
    2 * Real.sqrt t * (star b ⬝ᵥ z).re)

theorem complexBartlettColumnTilt_factor {d : ℕ} (c : ℝ)
    (theta : Matrix (Fin d) (Fin d) ℂ) (b : Fin d → ℂ) (t : ℝ) (z : Fin d → ℂ) :
    complexBartlettColumnTilt c theta b t z = Real.exp (c * t) *
      Real.exp ((star z ⬝ᵥ (theta *ᵥ z)).re + 2 * (star (Real.sqrt t • b) ⬝ᵥ z).re) := by
  rw [complexBartlettColumnTilt, ← Real.exp_add, star_smul,
    show star (Real.sqrt t) = Real.sqrt t from rfl,
    smul_dotProduct, Complex.smul_re]
  congr 1
  simp only [smul_eq_mul]
  ring

theorem complexBartlettColumn_scaled_inverse_quadratic {d : ℕ}
    (theta : Matrix (Fin d) (Fin d) ℂ) (b : Fin d → ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (star (Real.sqrt t • b) ⬝ᵥ ((1 - theta)⁻¹ *ᵥ (Real.sqrt t • b))).re =
      t * (star b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)).re := by
  rw [star_smul, show star (Real.sqrt t) = Real.sqrt t from rfl,
    Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    Complex.smul_re, Complex.smul_re]
  simp only [smul_eq_mul]
  calc
    _ = Real.sqrt t ^ 2 * (star b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)).re := by ring
    _ = _ := by rw [Real.sq_sqrt ht]

theorem complexBartlettColumn_integrable_gaussian {d : ℕ} (c : ℝ)
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℂ) (t : ℝ) :
    Integrable (complexBartlettColumnTilt c theta b t)
      (LogdetLean.GramHafnian.circularGaussianVector d) := by
  exact ((circularGaussianVector_integrable_quadratic htheta hpos
    (Real.sqrt t • b)).const_mul (Real.exp (c * t))).congr
      (Filter.Eventually.of_forall fun z ↦ (complexBartlettColumnTilt_factor c theta b t z).symm)

theorem complexBartlettColumn_integral_gaussian {d : ℕ} (c : ℝ)
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℂ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ z : Fin d → ℂ, complexBartlettColumnTilt c theta b t z
      ∂LogdetLean.GramHafnian.circularGaussianVector d) =
      ((1 - theta).det.re)⁻¹ *
        Real.exp ((c + (star b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)).re) * t) := by
  simp_rw [complexBartlettColumnTilt_factor]
  rw [integral_const_mul, circularGaussianVector_integral_quadratic_det htheta hpos,
    complexBartlettColumn_scaled_inverse_quadratic theta b t ht]
  calc
    _ = ((1 - theta).det.re)⁻¹ *
        (Real.exp (c * t) * Real.exp (t * (star b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)).re)) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem complexBartlettColumn_integrable {d : ℕ} {a c : ℝ} (ha : 0 < a)
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℂ)
    (hgap : c + (star b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)).re < 1) :
    Integrable (fun q : ℝ × (Fin d → ℂ) ↦ complexBartlettColumnTilt c theta b q.1 q.2)
      ((gammaMeasure a 1).prod (LogdetLean.GramHafnian.circularGaussianVector d)) := by
  letI := isProbabilityMeasure_gammaMeasure ha (by norm_num : (0 : ℝ) < 1)
  have hm : AEStronglyMeasurable
      (fun q : ℝ × (Fin d → ℂ) ↦ complexBartlettColumnTilt c theta b q.1 q.2)
      ((gammaMeasure a 1).prod (LogdetLean.GramHafnian.circularGaussianVector d)) := by
    apply Measurable.aestronglyMeasurable
    unfold complexBartlettColumnTilt dotProduct Matrix.mulVec
    fun_prop
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall (complexBartlettColumn_integrable_gaussian c htheta hpos b)
  · have hf := (A4Research.gammaMeasure_integrable_exp ha (by norm_num) hgap).const_mul
      ((1 - theta).det.re)⁻¹
    apply hf.congr
    filter_upwards [A4Research.gammaMeasure_ae_pos a 1] with t ht
    simp only [complexBartlettColumnTilt, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (complexBartlettColumn_integral_gaussian c htheta hpos b t ht.le).symm

theorem complexBartlettColumn_integral {d : ℕ} {a c : ℝ} (ha : 0 < a)
    {theta : Matrix (Fin d) (Fin d) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) (b : Fin d → ℂ)
    (hgap : c + (star b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)).re < 1) :
    (∫ q : ℝ × (Fin d → ℂ), complexBartlettColumnTilt c theta b q.1 q.2
      ∂(gammaMeasure a 1).prod (LogdetLean.GramHafnian.circularGaussianVector d)) =
      ((1 - theta).det.re)⁻¹ *
        Real.rpow (1 - (c + (star b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)).re)) (-a) := by
  letI := isProbabilityMeasure_gammaMeasure ha (by norm_num : (0 : ℝ) < 1)
  rw [MeasureTheory.integral_prod _ (complexBartlettColumn_integrable ha htheta hpos b hgap)]
  have heq : (fun t : ℝ ↦ ∫ z : Fin d → ℂ, complexBartlettColumnTilt c theta b t z
      ∂LogdetLean.GramHafnian.circularGaussianVector d) =ᵐ[gammaMeasure a 1]
      (fun t ↦ ((1 - theta).det.re)⁻¹ *
        Real.exp ((c + (star b ⬝ᵥ ((1 - theta)⁻¹ *ᵥ b)).re) * t)) := by
    filter_upwards [A4Research.gammaMeasure_ae_pos a 1] with t ht
    exact complexBartlettColumn_integral_gaussian c htheta hpos b t ht.le
  rw [integral_congr_ae heq, integral_const_mul,
    A4Research.gammaMeasure_integral_exp ha (by norm_num) hgap, one_div,
    ← Real.rpow_neg_eq_inv_rpow]
  rfl

end A3Research
