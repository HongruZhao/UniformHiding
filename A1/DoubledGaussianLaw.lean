import A1.DoubledGaussianSource
import A3.WishartGramDensity

open MeasureTheory ProbabilityTheory Matrix
open A3Research
open LogdetLean.GramHafnian.LocalAnticoncentration
open scoped BigOperators MatrixOrder ComplexOrder

noncomputable section
namespace A1Research

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def realHalfGaussianGramCoordinates {n r : ℕ} (X : Fin n → Fin r → ℝ) :
    HermitianCoordinates r ℝ :=
  hermitianCoordinateProjection ((Matrix.of X).transpose * Matrix.of X)

theorem measurable_realHalfGaussianGramCoordinates (n r : ℕ) :
    Measurable (realHalfGaussianGramCoordinates : (Fin n → Fin r → ℝ) → _) := by
  unfold realHalfGaussianGramCoordinates
  unfold hermitianCoordinateProjection
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop
  · apply measurable_pi_lambda
    intro ij
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    fun_prop

def scaleRealGaussianRows {n r : ℕ} (X : Fin n → Fin r → ℝ) : Fin n → Fin r → ℝ :=
  fun i j ↦ (Real.sqrt 2)⁻¹ * X i j

theorem measurable_scaleRealGaussianRows (n r : ℕ) :
    Measurable (scaleRealGaussianRows : (Fin n → Fin r → ℝ) → _) := by
  unfold scaleRealGaussianRows
  fun_prop

theorem map_scaleRealGaussianRows (n r : ℕ) :
    (A4Research.standardGaussianRows n r).map scaleRealGaussianRows =
      realHalfGaussianRows n r := by
  unfold A4Research.standardGaussianRows realHalfGaussianRows scaleRealGaussianRows
  rw [Measure.pi_map_pi (fun _ ↦ (show Measurable
    (fun x : Fin r → ℝ ↦ fun j ↦ (Real.sqrt 2)⁻¹ * x j) by fun_prop).aemeasurable)]
  congr 1
  funext i
  unfold A4Research.standardGaussianVector
  rw [Measure.pi_map_pi (fun _ ↦ (show Measurable
    (fun x : ℝ ↦ (Real.sqrt 2)⁻¹ * x) by fun_prop).aemeasurable)]
  simp only [A4Research.map_invSqrtTwo_gaussian]

theorem scaleRealGaussianRows_gram {n r : ℕ} (X : Fin n → Fin r → ℝ) :
    (Matrix.of (scaleRealGaussianRows X)).transpose * Matrix.of (scaleRealGaussianRows X) =
      A4Research.standardGaussianGram X := by
  have hc : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
    rw [← _root_.mul_inv_rev, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  ext i j
  change (∑ k : Fin n, ((Real.sqrt 2)⁻¹ * X k i) * ((Real.sqrt 2)⁻¹ * X k j)) =
    (∑ k : Fin n, X k i * X k j) / 2
  calc
    _ = ∑ k : Fin n, (1 / 2 : ℝ) * (X k i * X k j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_mul_mul_comm, hc]
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem map_realHalfGaussianGramCoordinates {n r : ℕ} :
    (realHalfGaussianRows n r).map realHalfGaussianGramCoordinates =
      realGaussianGramCoordinateLaw n r := by
  rw [← map_scaleRealGaussianRows n r,
    Measure.map_map (measurable_realHalfGaussianGramCoordinates n r)
      (measurable_scaleRealGaussianRows n r)]
  unfold realGaussianGramCoordinateLaw
  congr 1
  funext X
  exact congrArg hermitianCoordinateProjection (scaleRealGaussianRows_gram X)

def doubledRealGramMatrix {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℂ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ :=
  (doubledRealGaussianMatrix G).transpose * doubledRealGaussianMatrix G

def doubledRealGramCoordinates {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℂ) :
    HermitianCoordinates (2 * m) ℝ :=
  hermitianCoordinateProjection (doubledRealGramMatrix G)

theorem doubledRealGramMatrix_isSymm {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℂ) :
    (doubledRealGramMatrix G).IsSymm := by
  unfold doubledRealGramMatrix
  change ((doubledRealGaussianMatrix G).transpose * doubledRealGaussianMatrix G).transpose = _
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem measurable_doubledRealGramCoordinates (n m : ℕ) :
    Measurable (doubledRealGramCoordinates : Matrix (Fin n) (Fin m) ℂ → _) :=
  (measurable_realHalfGaussianGramCoordinates n (2 * m)).comp
    (measurable_doubledRealGaussianMatrix n m)

theorem map_doubledRealGramCoordinates {n m : ℕ} :
    (standardComplexGaussianRectangularMeasure n m).map doubledRealGramCoordinates =
      realGaussianGramCoordinateLaw n (2 * m) := by
  change (standardComplexGaussianRectangularMeasure n m).map
    (realHalfGaussianGramCoordinates ∘ doubledRealGaussianMatrix) = _
  rw [← Measure.map_map (measurable_realHalfGaussianGramCoordinates n (2 * m))
    (measurable_doubledRealGaussianMatrix n m), map_doubledRealGaussianMatrix,
    map_realHalfGaussianGramCoordinates]

/-- The exact doubled-real Gram source has the actual Wishart density on its
literal independent real symmetric coordinates, including the boundary row count. -/
theorem map_doubledRealGramCoordinates_eq_ambientDensity {n m : ℕ} (h2mn : 2 * m ≤ n) :
    (standardComplexGaussianRectangularMeasure n m).map doubledRealGramCoordinates =
      ENNReal.ofReal (wishartBartlettNormalization (2 * m) ℝ ((n : ℝ) / 2)
        (Real.sqrt Real.pi)⁻¹) • wishartAmbientMeasure (2 * m) ℝ ((n : ℝ) / 2) := by
  rw [map_doubledRealGramCoordinates]
  exact realGaussianGramCoordinateLaw_eq_ambientDensity h2mn

theorem ae_doubledRealGramMatrix_posDef {n m : ℕ} (h2mn : 2 * m ≤ n) :
    ∀ᵐ G ∂(standardComplexGaussianRectangularMeasure n m),
      (doubledRealGramMatrix G).PosDef := by
  letI : NullSingletonClass (gaussianReal 0 (1 / 2)) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hsource : ∀ᵐ X ∂(realHalfGaussianRows n (2 * m)),
      ((Matrix.of X).transpose * Matrix.of X).PosDef := by
    filter_upwards [A3Research.ae_det_leadingMinor_ne_zero n (2 * m) h2mn
      (gaussianReal 0 (1 / 2))] with X hX
    exact Matrix.PosDef.conjTranspose_mul_self (Matrix.of X)
      (A3Research.injective_mulVec_of_det_leadingMinor_ne_zero h2mn (Matrix.of X) hX)
  have hp : MeasurePreserving doubledRealGaussianMatrix
      (standardComplexGaussianRectangularMeasure n m) (realHalfGaussianRows n (2 * m)) :=
    ⟨measurable_doubledRealGaussianMatrix n m, map_doubledRealGaussianMatrix n m⟩
  exact hp.quasiMeasurePreserving.ae hsource

end A1Research
