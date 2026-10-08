import A3.ComplexGaussianLaplace
import A3.HermitianLaplaceUniqueness
import A3.GSVAESupport
import A3.ComplexGaussianVectorProbability

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem trace_complexGaussianGram {rows n : ℕ}
    (theta : Matrix (Fin n) (Fin n) ℂ) (X : Matrix (Fin rows) (Fin n) ℂ) :
    (theta * (X.conjTranspose * X)).trace =
      ∑ r, star (X r) ⬝ᵥ (theta.transpose *ᵥ X r) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  unfold Matrix.trace Matrix.diag Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro r _
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
    Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem circularGaussianVector_integral_quadratic_zero {n : ℕ}
    {theta : Matrix (Fin n) (Fin n) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (∫ z : Fin n → ℂ, Real.exp (star z ⬝ᵥ (theta *ᵥ z)).re
      ∂LogdetLean.GramHafnian.circularGaussianVector n) = ((1 - theta).det.re)⁻¹ := by
  simpa using circularGaussianVector_integral_quadratic_det htheta hpos 0

theorem standardComplexGaussianGram_laplace {rows n : ℕ}
    {theta : Matrix (Fin n) (Fin n) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (∫ X : Matrix (Fin rows) (Fin n) ℂ,
      Real.exp ((theta * (X.conjTranspose * X)).trace).re
      ∂LogdetLean.GramHafnian.LocalAnticoncentration.standardComplexGaussianRectangularMeasure rows n) =
      Real.rpow ((1 - theta).det.re) (-(rows : ℝ)) := by
  rw [LogdetLean.GramHafnian.UltimateHiding.DenseScore.standardComplexGaussianRectangularMeasure_eq_pi]
  have hpt : (1 - theta.transpose).PosDef := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_one] using hpos.transpose
  have hfun (X : Matrix (Fin rows) (Fin n) ℂ) :
      Real.exp ((theta * (X.conjTranspose * X)).trace).re =
        ∏ r, Real.exp (star (X r) ⬝ᵥ (theta.transpose *ᵥ X r)).re := by
    rw [trace_complexGaussianGram, Complex.re_sum, Real.exp_sum]
  simp_rw [hfun]
  change (∫ X : Fin rows → Fin n → ℂ,
    ∏ r, Real.exp (star (X r) ⬝ᵥ (theta.transpose *ᵥ X r)).re
      ∂Measure.pi (fun _ : Fin rows ↦ LogdetLean.GramHafnian.circularGaussianVector n)) = _
  rw [integral_fintype_prod_eq_prod (fun _ : Fin rows ↦
    fun z : Fin n → ℂ ↦ Real.exp (star z ⬝ᵥ (theta.transpose *ᵥ z)).re)]
  simp_rw [circularGaussianVector_integral_quadratic_zero htheta.transpose hpt]
  have hdet : (1 - theta.transpose).det = (1 - theta).det := by
    have htr : 1 - theta.transpose = (1 - theta).transpose := by
      ext i j
      simp [Matrix.transpose_apply, Matrix.one_apply, eq_comm]
    rw [htr, Matrix.det_transpose]
  simp only [hdet, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    _ = ((1 - theta).det.re) ^ (-(rows : ℤ)) := by simp
    _ = _ := (Real.rpow_neg_natCast _ rows).symm

def complexGaussianGramCoordinateLaw (rows n : ℕ) : Measure (HermitianCoordinates n ℂ) :=
  (LogdetLean.GramHafnian.LocalAnticoncentration.standardComplexGaussianRectangularMeasure rows n).map
    (fun X ↦ hermitianCoordinateProjection (X.conjTranspose * X))

theorem measurable_complexGaussianGramCoordinates (rows n : ℕ) :
    Measurable (fun X : Matrix (Fin rows) (Fin n) ℂ ↦
      hermitianCoordinateProjection (X.conjTranspose * X)) := by
  apply (measurable_hermitianCoordinateProjection n ℂ).comp
  have hc : Continuous (fun X : Matrix (Fin rows) (Fin n) ℂ ↦ X.conjTranspose * X) :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  exact hc.measurable

theorem complexGaussianGramCoordinateLaw_probability (rows n : ℕ) :
    IsProbabilityMeasure (complexGaussianGramCoordinateLaw rows n) := by
  unfold complexGaussianGramCoordinateLaw
  exact Measure.isProbabilityMeasure_map (measurable_complexGaussianGramCoordinates rows n).aemeasurable

theorem complexGaussianGramCoordinateLaw_laplace {rows n : ℕ}
    {theta : Matrix (Fin n) (Fin n) ℂ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (∫ x : HermitianCoordinates n ℂ,
      Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re
      ∂complexGaussianGramCoordinateLaw rows n) =
      Real.rpow ((1 - theta).det.re) (-(rows : ℝ)) := by
  unfold complexGaussianGramCoordinateLaw
  have hc : Continuous (fun x : HermitianCoordinates n ℂ ↦
      Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re) :=
    Real.continuous_exp.comp (Complex.continuous_re.comp
      (continuous_const.matrix_mul continuous_hermitianMatrixOfCoordinates).matrix_trace)
  rw [integral_map (measurable_complexGaussianGramCoordinates rows n).aemeasurable
    (show AEStronglyMeasurable (fun x : HermitianCoordinates n ℂ ↦
      Real.exp ((theta * hermitianMatrixOfCoordinates x).trace).re)
      ((LogdetLean.GramHafnian.LocalAnticoncentration.standardComplexGaussianRectangularMeasure rows n).map
        (fun X ↦ hermitianCoordinateProjection (X.conjTranspose * X))) from
      hc.measurable.aestronglyMeasurable)]
  change (∫ X, Real.exp ((theta * hermitianMatrixOfCoordinates
    (hermitianCoordinateProjection (X.conjTranspose * X))).trace).re
      ∂LogdetLean.GramHafnian.LocalAnticoncentration.standardComplexGaussianRectangularMeasure rows n) = _
  have heq (X : Matrix (Fin rows) (Fin n) ℂ) :
      hermitianMatrixOfCoordinates (hermitianCoordinateProjection (X.conjTranspose * X)) =
        X.conjTranspose * X :=
    hermitianMatrixOfCoordinates_projection _ (Matrix.isHermitian_conjTranspose_mul_self X)
  simp_rw [heq]
  exact standardComplexGaussianGram_laplace htheta hpos

end A3Research
