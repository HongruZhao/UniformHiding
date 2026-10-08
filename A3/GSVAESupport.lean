import A3.GaussianMatrixRank

open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open Matrix MeasureTheory ProbabilityTheory
open LogdetLean.GramHafnian LogdetLean.GramHafnian.LocalAnticoncentration

noncomputable section
namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

local instance realMatrixMeasurable (rows n : Type*) :
    MeasurableSpace (Matrix rows n ℝ) := by
  unfold Matrix
  infer_instance

local instance realMatrixBorel (rows n : Type*) [Finite rows] [Finite n] :
    BorelSpace (Matrix rows n ℝ) :=
  inferInstanceAs (BorelSpace (rows → n → ℝ))

theorem a3_measurable_edelmanSuttonRealMatrixEmbedding (rows n : ℕ) :
    Measurable (edelmanSuttonRealMatrixEmbedding rows n) := by
  unfold edelmanSuttonRealMatrixEmbedding
  fun_prop

theorem standardComplexGaussianRectangularMeasure_eq_pi (rows n : ℕ) :
    standardComplexGaussianRectangularMeasure rows n =
      Measure.pi (fun _ : Fin rows ↦ Measure.pi fun _ : Fin n ↦ circularGaussian) := by
  unfold standardComplexGaussianRectangularMeasure circularGaussianVector
  change Measure.map id _ = _
  exact Measure.map_id

instance edelmanSuttonRealGaussianMatrixLaw_isProbabilityMeasure (rows n : ℕ) :
    IsProbabilityMeasure (edelmanSuttonRealGaussianMatrixLaw rows n) := by
  unfold edelmanSuttonRealGaussianMatrixLaw standardRealGaussianVectorMeasure
  change IsProbabilityMeasure
    ((Measure.pi fun _ : Fin rows ↦ Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).map
      (fun X : Fin rows → Fin n → ℝ ↦ Matrix.of fun i j ↦ (X i j : ℂ)))
  have hm : Measurable (fun X : Fin rows → Fin n → ℝ ↦
      Matrix.of fun i j ↦ (X i j : ℂ)) := by
    change Measurable (fun X : Fin rows → Fin n → ℝ ↦ fun i j ↦ (X i j : ℂ))
    fun_prop
  exact Measure.isProbabilityMeasure_map hm.aemeasurable

instance standardComplexGaussianRectangularMeasure_isProbabilityMeasure (rows n : ℕ) :
    IsProbabilityMeasure (standardComplexGaussianRectangularMeasure rows n) := by
  rw [standardComplexGaussianRectangularMeasure_eq_pi]
  change IsProbabilityMeasure
    (Measure.pi (fun _ : Fin rows ↦ Measure.pi fun _ : Fin n ↦ circularGaussian) :
      Measure (Fin rows → Fin n → ℂ))
  infer_instance

instance edelmanSuttonGaussianMatrixLaw_isProbabilityMeasure (rows n : ℕ) (beta : ℝ) :
    IsProbabilityMeasure (edelmanSuttonGaussianMatrixLaw rows n beta) := by
  unfold edelmanSuttonGaussianMatrixLaw
  split <;> infer_instance

instance edelmanSuttonGaussianPairLaw_isProbabilityMeasure (n a b : ℕ) (beta : ℝ) :
    IsProbabilityMeasure (edelmanSuttonGaussianPairLaw n a b beta) := by
  unfold edelmanSuttonGaussianPairLaw
  infer_instance

theorem measurableSet_posDef_conjTranspose_mul_self (rows n : ℕ) :
    MeasurableSet {X : Matrix (Fin rows) (Fin n) ℂ | (X.conjTranspose * X).PosDef} := by
  have heq : {X : Matrix (Fin rows) (Fin n) ℂ | (X.conjTranspose * X).PosDef} =
      {X | (X.conjTranspose * X).det ≠ 0} := by
    ext X
    exact (posSemidef_conjTranspose_mul_self X).posDef_iff_det_ne_zero
  rw [heq]
  have hm : Measurable (fun X : Matrix (Fin rows) (Fin n) ℂ ↦
      (X.conjTranspose * X).det) :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).matrix_det.measurable
  exact (hm.eq_const 0).setOf.compl

/-- Full column rank for the literal circular complex Gaussian source. -/
theorem ae_posDef_Gram_standardComplexGaussian (rows n : ℕ) (h : n ≤ rows) :
    ∀ᵐ X ∂(standardComplexGaussianRectangularMeasure rows n),
      (X.conjTranspose * X).PosDef := by
  rw [standardComplexGaussianRectangularMeasure_eq_pi]
  filter_upwards [A3Research.ae_det_leadingMinor_ne_zero rows n h circularGaussian] with X hX
  exact Matrix.PosDef.conjTranspose_mul_self X
    (A3Research.injective_mulVec_of_det_leadingMinor_ne_zero h X hX)

theorem det_leadingMinor_realEmbedding (rows n : ℕ) (h : n ≤ rows)
    (X : Matrix (Fin rows) (Fin n) ℝ) :
    (Matrix.of fun i j : Fin n ↦ edelmanSuttonRealMatrixEmbedding rows n X
        (Fin.castLE h i) j).det =
      (((Matrix.of fun i j : Fin n ↦ X (Fin.castLE h i) j).det : ℝ) : ℂ) := by
  have hm : (Matrix.of fun i j : Fin n ↦ X (Fin.castLE h i) j).map Complex.ofReal =
      Matrix.of (fun i j : Fin n ↦ edelmanSuttonRealMatrixEmbedding rows n X
        (Fin.castLE h i) j) := by
    ext i j
    rfl
  exact (congrArg Matrix.det hm).symm.trans (Complex.ofRealHom.map_det _).symm

/-- Full column rank for the literal embedded real Gaussian source. -/
theorem ae_posDef_Gram_edelmanSuttonRealGaussian (rows n : ℕ) (h : n ≤ rows) :
    ∀ᵐ X ∂(edelmanSuttonRealGaussianMatrixLaw rows n),
      (X.conjTranspose * X).PosDef := by
  unfold edelmanSuttonRealGaussianMatrixLaw
  apply (ae_map_iff (a3_measurable_edelmanSuttonRealMatrixEmbedding rows n).aemeasurable
    (measurableSet_posDef_conjTranspose_mul_self rows n)).mpr
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  filter_upwards [A3Research.ae_det_leadingMinor_ne_zero rows n h (gaussianReal 0 1)]
    with X hX
  have hdet : (Matrix.of fun i j : Fin n ↦ edelmanSuttonRealMatrixEmbedding rows n X
      (Fin.castLE h i) j).det ≠ 0 := by
    rw [det_leadingMinor_realEmbedding]
    exact Complex.ofReal_ne_zero.mpr hX
  exact Matrix.PosDef.conjTranspose_mul_self _
    (A3Research.injective_mulVec_of_det_leadingMinor_ne_zero h _ hdet)

/-- Both admitted beta cases have genuine positive definite Gram matrices almost surely. -/
theorem ae_posDef_Gram_edelmanSuttonGaussianMatrixLaw (rows n : ℕ) (h : n ≤ rows)
    (beta : ℝ) :
    ∀ᵐ X ∂(edelmanSuttonGaussianMatrixLaw rows n beta),
      (X.conjTranspose * X).PosDef := by
  unfold edelmanSuttonGaussianMatrixLaw
  split
  · exact ae_posDef_Gram_edelmanSuttonRealGaussian rows n h
  · exact ae_posDef_Gram_standardComplexGaussian rows n h

theorem ae_posDef_edelmanSuttonGrams (n a b : ℕ) (beta : ℝ) :
    ∀ᵐ omega ∂(edelmanSuttonGaussianPairLaw n a b beta),
      (edelmanSuttonFirstGram omega).PosDef ∧
        (edelmanSuttonSecondGram omega).PosDef := by
  have hfirst := ae_posDef_Gram_edelmanSuttonGaussianMatrixLaw (n + a) n (Nat.le_add_right n a) beta
  have hsecond := ae_posDef_Gram_edelmanSuttonGaussianMatrixLaw (n + b) n (Nat.le_add_right n b) beta
  unfold edelmanSuttonGaussianPairLaw
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hfirst,
    Measure.quasiMeasurePreserving_snd.ae hsecond] with omega h1 h2
  exact ⟨h1, h2⟩

/-- The exact A3 statistic lies in the open cube almost surely for its actual source law. -/
theorem ae_edelmanSuttonSquaredGSVCoordinates_mem_openUnitCube
    (n a b : ℕ) (beta : ℝ) :
    ∀ᵐ omega ∂(edelmanSuttonGaussianPairLaw n a b beta),
      edelmanSuttonSquaredGSVCoordinates n a b beta omega ∈ H6CoordinateAlgebra.openUnitCube n := by
  filter_upwards [ae_posDef_edelmanSuttonGrams n a b beta] with omega h
  exact edelmanSuttonSquaredGSVCoordinates_mem_openUnitCube beta omega h.1 h.2

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
