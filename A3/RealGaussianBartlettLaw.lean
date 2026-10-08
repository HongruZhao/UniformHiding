import A3.RealBartlettLaplace
import A3.RealHermitianLaplaceUniqueness
import A4.GaussianWishartBridge

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def realGaussianGramCoordinateLaw (rows n : ℕ) : Measure (HermitianCoordinates n ℝ) :=
  (A4Research.standardGaussianRows rows n).map
    (fun X ↦ hermitianCoordinateProjection (A4Research.standardGaussianGram X))

theorem measurable_realGaussianGramCoordinates (rows n : ℕ) :
    Measurable (fun X : Fin rows → Fin n → ℝ ↦
      hermitianCoordinateProjection (A4Research.standardGaussianGram X)) := by
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    unfold A4Research.standardGaussianGram
    fun_prop
  · apply measurable_pi_lambda
    intro ij
    unfold A4Research.standardGaussianGram
    fun_prop

theorem realGaussianGramCoordinateLaw_probability (rows n : ℕ) :
    IsProbabilityMeasure (realGaussianGramCoordinateLaw rows n) := by
  unfold realGaussianGramCoordinateLaw
  exact Measure.isProbabilityMeasure_map (measurable_realGaussianGramCoordinates rows n).aemeasurable

theorem realGaussianGramCoordinateLaw_laplace {rows n : ℕ}
    {theta : Matrix (Fin n) (Fin n) ℝ} (htheta : theta.IsHermitian)
    (hpos : (1 - theta).PosDef) :
    (∫ x : HermitianCoordinates n ℝ,
      Real.exp (theta * hermitianMatrixOfCoordinates x).trace
      ∂realGaussianGramCoordinateLaw rows n) = Real.rpow (1 - theta).det (-((rows : ℝ) / 2)) := by
  unfold realGaussianGramCoordinateLaw
  have hc : Continuous (fun x : HermitianCoordinates n ℝ ↦
      Real.exp (theta * hermitianMatrixOfCoordinates x).trace) :=
    Real.continuous_exp.comp
      (continuous_const.matrix_mul continuous_hermitianMatrixOfCoordinates).matrix_trace
  rw [integral_map (measurable_realGaussianGramCoordinates rows n).aemeasurable
    hc.measurable.aestronglyMeasurable]
  have heq (X : Fin rows → Fin n → ℝ) :
      hermitianMatrixOfCoordinates (hermitianCoordinateProjection
        (A4Research.standardGaussianGram X)) = A4Research.standardGaussianGram X :=
    hermitianMatrixOfCoordinates_projection _
      (Matrix.isHermitian_iff_isSymm.mpr (A4Research.standardGaussianGram_isSymm X))
  change (∫ X, Real.exp (theta * hermitianMatrixOfCoordinates
    (hermitianCoordinateProjection (A4Research.standardGaussianGram X))).trace
      ∂A4Research.standardGaussianRows rows n) = _
  simp_rw [heq]
  exact A4Research.standardGaussianGram_integral_etr
    (⟨theta, Matrix.isHermitian_iff_isSymm.mp htheta⟩ : MatsumotoPaper.Sym n) hpos

theorem realGaussianGramCoordinateLaw_eq_bartlett {rows n : ℕ} (hn : n ≤ rows) :
    realGaussianGramCoordinateLaw rows n = realBartlettGramCoordinateLaw n ((rows : ℝ) / 2) := by
  letI := realGaussianGramCoordinateLaw_probability rows n
  letI := realBartlettGramCoordinateLaw_probability (wishartBartlettShape_real_rows_pos hn)
  exact real_coordinate_law_eq_of_laplace
    (fun _ ht hp ↦ realGaussianGramCoordinateLaw_laplace ht hp)
    (fun _ ht hp ↦ realBartlettGramCoordinateLaw_laplace
      (wishartBartlettShape_real_rows_pos hn) ht hp)

end A3Research
