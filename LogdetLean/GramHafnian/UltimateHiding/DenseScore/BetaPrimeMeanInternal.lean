import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatrixInverseMeasurability
import LogdetLean.GramHafnian.UltimateHiding.WishartCore.Wishart.BoundedDerivativeSteinHaff
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.RealGaussianMomentCore

open MeasureTheory
open ProbabilityTheory
open scoped Matrix.Norms.Elementwise

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.Wishart

local instance betaMeanFunctionalNorm
    {p : Type*} [Fintype p] :
    Norm (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm

local instance betaMeanFunctionalSeminormedAddCommGroup
    {p : Type*} [Fintype p] :
    SeminormedAddCommGroup (Matrix p p ℝ →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup

theorem standardRealGaussianMatrixMeasure_isProbability_internal
    (rows cols : ℕ) :
    IsProbabilityMeasure (standardRealGaussianMatrixMeasure rows cols) := by
  unfold standardRealGaussianMatrixMeasure
  apply Measure.pi.instIsProbabilityMeasure

theorem halfGaussian_inverseWishart_trace_mean
    {k p : ℕ} (hgap : p + 1 < k) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹ ∂halfGaussianMatrix k p) =
      2 * (p : ℝ) / ((k : ℝ) - (p : ℝ) - 1) := by
  have h := steinHaff_halfGaussianMatrix_of_bounded_fderiv
    hgap (fun _ : Matrix (Fin p) (Fin p) ℝ ↦ (1 : ℝ))
    (contDiff_const : ContDiff ℝ 1 (fun _ : Matrix (Fin p) (Fin p) ℝ ↦ (1 : ℝ)))
    1 (by intro M; norm_num) 0 (by intro M; norm_num) (1 : Matrix (Fin p) (Fin p) ℝ)
    Matrix.isSymm_one
  have heq := h.2.2
  simp only [one_mul, Matrix.mul_one] at heq
  simp at heq
  have hcoeff : inverseGramScoreCoefficient (Fin k) (Fin p) =
      ((k : ℝ) - (p : ℝ) - 1) / 2 := by
    simp [inverseGramScoreCoefficient]
  have htraceOne : Matrix.trace
      (1 : Matrix (Fin p) (Fin p) ℝ) = (p : ℝ) := by
    simp [Matrix.trace]
  rw [hcoeff] at heq
  rw [integral_const_mul] at heq
  have hden : (0 : ℝ) < (k : ℝ) - (p : ℝ) - 1 := by
    have hgapR : ((p + 1 : ℕ) : ℝ) < (k : ℝ) := by
      exact_mod_cast hgap
    norm_num [Nat.cast_add] at hgapR ⊢
    linarith
  apply (eq_div_iff hden.ne').2
  nlinarith [heq]

def invSqrtTwoScaleMatrix (k p : ℕ) :
    Matrix (Fin k) (Fin p) ℝ → Matrix (Fin k) (Fin p) ℝ :=
  fun R i j ↦ (Real.sqrt 2)⁻¹ * R i j

theorem measurable_invSqrtTwoScaleMatrix (k p : ℕ) :
    Measurable (invSqrtTwoScaleMatrix k p) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact measurable_const.mul ((measurable_pi_apply j).comp (measurable_pi_apply i))

theorem map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure
    (k p : ℕ) :
    Measure.map (invSqrtTwoScaleMatrix k p)
        (standardRealGaussianMatrixMeasure k p) =
      halfGaussianMatrix k p := by
  let c : ℝ := (Real.sqrt 2)⁻¹
  let scaleVec : (Fin p → ℝ) → (Fin p → ℝ) :=
    fun x j ↦ c * x j
  have hrow : Measure.map scaleVec (standardRealGaussianVectorMeasure p) =
      Measure.pi (fun _ : Fin p ↦ gaussianReal 0 halfGaussianVariance) := by
    unfold standardRealGaussianVectorMeasure
    rw [Measure.pi_map_pi (fun _ ↦
      (show Measurable (fun x : ℝ ↦ c * x) by fun_prop).aemeasurable)]
    congr 1
    funext j
    simpa [c] using map_invSqrtTwo_gaussianReal_zero_one
  have houter :
      Measure.map (fun R : Fin k → Fin p → ℝ ↦ fun i ↦ scaleVec (R i))
          (Measure.pi fun _ : Fin k ↦ standardRealGaussianVectorMeasure p) =
        halfGaussianRowProduct k p := by
    rw [Measure.pi_map_pi (fun _ ↦
      (show Measurable scaleVec by fun_prop).aemeasurable)]
    simp_rw [hrow]
    rfl
  rw [← map_curriedMatrix_halfGaussianRowProduct k p]
  rw [← houter]
  rw [Measure.map_map (curriedMatrixMeasurableEquiv k p).measurable
    (show Measurable (fun R : Fin k → Fin p → ℝ ↦
      fun i ↦ scaleVec (R i)) by fun_prop)]
  apply Measure.map_congr
  filter_upwards [] with R
  ext i j
  rfl

theorem realWishartGram_invSqrtTwoScaleMatrix
    (k p : ℕ) (R : Matrix (Fin k) (Fin p) ℝ) :
    realWishartGram (invSqrtTwoScaleMatrix k p R) =
      (1 / 2 : ℝ) • realWishartGram R := by
  ext i j
  simp only [realWishartGram, Matrix.mul_apply, Matrix.transpose_apply,
    invSqrtTwoScaleMatrix, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by norm_num
  have hsquare : Real.sqrt 2 ^ 2 = 2 := by
    simpa [pow_two] using hsqrt
  field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  rw [hsquare]
  ring

theorem trace_inv_realWishartGram_invSqrtTwoScaleMatrix
    {k p : ℕ} (R : Matrix (Fin k) (Fin p) ℝ)
    (hunit : IsUnit (realWishartGram R).det) :
    Matrix.trace
        (realWishartGram (invSqrtTwoScaleMatrix k p R))⁻¹ =
      2 * Matrix.trace (realWishartGram R)⁻¹ := by
  rw [realWishartGram_invSqrtTwoScaleMatrix]
  letI : Invertible (1 / 2 : ℝ) :=
    invertibleOfNonzero (by norm_num)
  rw [Matrix.inv_smul (A := realWishartGram R) (1 / 2 : ℝ) hunit,
    Matrix.trace_smul]
  change (⅟ (1 / 2 : ℝ)) * Matrix.trace (realWishartGram R)⁻¹ =
    2 * Matrix.trace (realWishartGram R)⁻¹
  norm_num

theorem ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
    {k p : ℕ} (hp : p ≤ k) :
    ∀ᵐ R ∂standardRealGaussianMatrixMeasure k p,
      IsUnit (realWishartGram R).det := by
  have hhalf := ae_isUnit_det_realWishartGram_halfGaussianMatrix k p hp
  rw [← map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure] at hhalf
  have hmeas : MeasurableSet
      {R : Matrix (Fin k) (Fin p) ℝ |
        IsUnit (realWishartGram R).det} := by
    rw [show {R : Matrix (Fin k) (Fin p) ℝ |
        IsUnit (realWishartGram R).det} =
        {R | (realWishartGram R).det ≠ 0} by
      ext R
      simp [isUnit_iff_ne_zero]]
    have hGram : Measurable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦ realWishartGram R) := by
      unfold realWishartGram
      refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      fun_prop
    have hdet : Measurable
        (fun R : Matrix (Fin k) (Fin p) ℝ ↦ (realWishartGram R).det) := by
      have hdetMatrix : Measurable
          (fun A : Matrix (Fin p) (Fin p) ℝ ↦ A.det) := by
        simp_rw [Matrix.det_apply']
        fun_prop
      exact hdetMatrix.comp hGram
    exact (hdet.eq_const 0).setOf.compl
  have hscaled :=
    (ae_map_iff (measurable_invSqrtTwoScaleMatrix k p).aemeasurable
      hmeas).mp hhalf
  filter_upwards [hscaled] with R hR
  rw [realWishartGram_invSqrtTwoScaleMatrix, Matrix.det_smul] at hR
  exact isUnit_of_mul_isUnit_right hR

theorem integrable_trace_nonsingInv_realWishartGram_standardGaussian
    {k p : ℕ} (hgap : p + 1 < k) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace (realWishartGram R)⁻¹)
      (standardRealGaussianMatrixMeasure k p) := by
  let f : Matrix (Fin k) (Fin p) ℝ → ℝ :=
    fun R ↦ Matrix.trace (realWishartGram R)⁻¹
  have hhalf : Integrable f (halfGaussianMatrix k p) :=
    integrable_trace_nonsingInv_realWishartGram_halfGaussianMatrix hgap
  rw [← map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure] at hhalf
  have hcomp : Integrable (f ∘ invSqrtTwoScaleMatrix k p)
      (standardRealGaussianMatrixMeasure k p) :=
    (integrable_map_measure
      (measurable_trace_nonsingInv_realWishartGram k p).aestronglyMeasurable
      (measurable_invSqrtTwoScaleMatrix k p).aemeasurable).mp hhalf
  have hunit := ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
    (k := k) (p := p) (Nat.le_of_lt (lt_trans (Nat.lt_succ_self p) hgap))
  have heq : f ∘ invSqrtTwoScaleMatrix k p =ᵐ[
      standardRealGaussianMatrixMeasure k p] fun R ↦ 2 * f R := by
    filter_upwards [hunit] with R hR
    exact trace_inv_realWishartGram_invSqrtTwoScaleMatrix R hR
  have htwice : Integrable (fun R ↦ 2 * f R)
      (standardRealGaussianMatrixMeasure k p) := hcomp.congr heq
  have hscaled := htwice.const_mul (1 / 2 : ℝ)
  simpa [f] using hscaled

theorem standardGaussian_inverseWishart_trace_mean
    {k p : ℕ} (hgap : p + 1 < k) :
    (∫ R : Matrix (Fin k) (Fin p) ℝ,
        Matrix.trace (realWishartGram R)⁻¹
        ∂standardRealGaussianMatrixMeasure k p) =
      (p : ℝ) / ((k : ℝ) - (p : ℝ) - 1) := by
  let f : Matrix (Fin k) (Fin p) ℝ → ℝ :=
    fun R ↦ Matrix.trace (realWishartGram R)⁻¹
  have hhalf : (∫ R, f R ∂halfGaussianMatrix k p) =
      2 * (p : ℝ) / ((k : ℝ) - (p : ℝ) - 1) :=
    halfGaussian_inverseWishart_trace_mean hgap
  rw [← map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure] at hhalf
  rw [integral_map
    (measurable_invSqrtTwoScaleMatrix k p).aemeasurable
    (measurable_trace_nonsingInv_realWishartGram k p).aestronglyMeasurable] at hhalf
  have hunit := ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
    (k := k) (p := p) (Nat.le_of_lt (lt_trans (Nat.lt_succ_self p) hgap))
  have heq : f ∘ invSqrtTwoScaleMatrix k p =ᵐ[
      standardRealGaussianMatrixMeasure k p] fun R ↦ 2 * f R := by
    filter_upwards [hunit] with R hR
    exact trace_inv_realWishartGram_invSqrtTwoScaleMatrix R hR
  change (∫ R, (f ∘ invSqrtTwoScaleMatrix k p) R
      ∂standardRealGaussianMatrixMeasure k p) = _ at hhalf
  rw [integral_congr_ae heq, integral_const_mul] at hhalf
  change (∫ R, f R ∂standardRealGaussianMatrixMeasure k p) = _
  apply mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)
  calc
    2 * (∫ R, f R ∂standardRealGaussianMatrixMeasure k p) =
        2 * (p : ℝ) / ((k : ℝ) - (p : ℝ) - 1) := hhalf
    _ = 2 * ((p : ℝ) / ((k : ℝ) - (p : ℝ) - 1)) := by ring

theorem integral_standardRealGaussianVector_coordinate_mul
    {p : ℕ} (i j : Fin p) :
    (∫ x : Fin p → ℝ, x i * x j
        ∂standardRealGaussianVectorMeasure p) =
      if i = j then 1 else 0 := by
  classical
  let ei : Fin p → ℝ := Pi.single i 1
  let ej : Fin p → ℝ := Pi.single j 1
  have h := LogdetLean.GramHafnian.integral_realBilinearForms_standardGaussian
    ei ej
  have hsingle (l : Fin p) (x : Fin p → ℝ) :
      LogdetLean.GramHafnian.bilinearDot (Pi.single l 1) x = x l := by
    unfold LogdetLean.GramHafnian.bilinearDot
    rw [Finset.sum_eq_single l]
    · simp
    · intro b hb hbl
      simp [Pi.single_apply, hbl]
    · simp
  calc
    (∫ x : Fin p → ℝ, x i * x j
        ∂standardRealGaussianVectorMeasure p) =
        ∫ x : Fin p → ℝ,
          LogdetLean.GramHafnian.bilinearDot ei x *
            LogdetLean.GramHafnian.bilinearDot ej x
          ∂standardRealGaussianVectorMeasure p := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [show LogdetLean.GramHafnian.bilinearDot ei x = x i by
        exact hsingle i x,
        show LogdetLean.GramHafnian.bilinearDot ej x = x j by
        exact hsingle j x]
    _ = LogdetLean.GramHafnian.bilinearDot ei ej := h
    _ = if i = j then 1 else 0 := by
      rw [show LogdetLean.GramHafnian.bilinearDot ei ej = ej i by
        exact hsingle i ej]
      by_cases hij : i = j
      · subst j
        simp [ej]
      · simp [ej, Pi.single_apply, hij]

theorem integrable_standardRealGaussianVector_coordinate_mul
    {p : ℕ} (i j : Fin p) :
    Integrable (fun x : Fin p → ℝ ↦ x i * x j)
      (standardRealGaussianVectorMeasure p) := by
  classical
  let c : Fin 2 → Fin p := ![i, j]
  simpa [c] using
    (LogdetLean.GramHafnian.integrable_realColorProduct_standardGaussian c)

theorem integral_standardRealGaussianMatrix_coordinate_mul
    {rows p : ℕ} (a : Fin rows) (i j : Fin p) :
    (∫ R : Matrix (Fin rows) (Fin p) ℝ, R a i * R a j
        ∂standardRealGaussianMatrixMeasure rows p) =
      if i = j then 1 else 0 := by
  rw [← show Measure.map (curriedMatrixMeasurableEquiv rows p)
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
      standardRealGaussianMatrixMeasure rows p by
    unfold standardRealGaussianMatrixMeasure
    change Measure.map (id : (Fin rows → Fin p → ℝ) →
        (Fin rows → Fin p → ℝ))
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
      Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p
    exact Measure.map_id]
  rw [integral_map (curriedMatrixMeasurableEquiv rows p).measurable.aemeasurable
    (show AEStronglyMeasurable
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦ R a i * R a j)
      (Measure.map (curriedMatrixMeasurableEquiv rows p)
        (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p)) by
      fun_prop)]
  change (∫ R : Fin rows → Fin p → ℝ, R a i * R a j
      ∂Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) = _
  calc
    (∫ R : Fin rows → Fin p → ℝ, R a i * R a j
        ∂Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
        ∫ x : Fin p → ℝ, x i * x j
          ∂standardRealGaussianVectorMeasure p :=
      integral_comp_eval
        (μ := fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p)
        (i := a)
        (integrable_standardRealGaussianVector_coordinate_mul i j).aestronglyMeasurable
    _ = if i = j then 1 else 0 :=
      integral_standardRealGaussianVector_coordinate_mul i j

theorem integrable_standardRealGaussianMatrix_coordinate_mul
    {rows p : ℕ} (a : Fin rows) (i j : Fin p) :
    Integrable (fun R : Matrix (Fin rows) (Fin p) ℝ ↦ R a i * R a j)
      (standardRealGaussianMatrixMeasure rows p) := by
  rw [← show Measure.map (curriedMatrixMeasurableEquiv rows p)
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
      standardRealGaussianMatrixMeasure rows p by
    unfold standardRealGaussianMatrixMeasure
    change Measure.map (id : (Fin rows → Fin p → ℝ) →
        (Fin rows → Fin p → ℝ))
      (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p) =
      Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p
    exact Measure.map_id]
  apply (integrable_map_measure (by fun_prop)
    (curriedMatrixMeasurableEquiv rows p).measurable.aemeasurable).2
  change Integrable (fun R : Fin rows → Fin p → ℝ ↦ R a i * R a j)
    (Measure.pi fun _ : Fin rows ↦ standardRealGaussianVectorMeasure p)
  exact integrable_comp_eval (μ := fun _ : Fin rows ↦
      standardRealGaussianVectorMeasure p) (i := a)
    (integrable_standardRealGaussianVector_coordinate_mul i j)

theorem integral_realWishartGram_entry_standardGaussian
    (rows p : ℕ) (i j : Fin p) :
    (∫ R : Matrix (Fin rows) (Fin p) ℝ,
        realWishartGram R i j ∂standardRealGaussianMatrixMeasure rows p) =
      (rows : ℝ) * if i = j then 1 else 0 := by
  simp only [realWishartGram, Matrix.mul_apply, Matrix.transpose_apply]
  rw [integral_finset_sum]
  · simp_rw [integral_standardRealGaussianMatrix_coordinate_mul]
    simp
  · intro a ha
    exact integrable_standardRealGaussianMatrix_coordinate_mul a i j

theorem integrable_realWishartGram_entry_standardGaussian
    (rows p : ℕ) (i j : Fin p) :
    Integrable
      (fun R : Matrix (Fin rows) (Fin p) ℝ ↦ realWishartGram R i j)
      (standardRealGaussianMatrixMeasure rows p) := by
  simp only [realWishartGram, Matrix.mul_apply, Matrix.transpose_apply]
  exact integrable_finsetSum Finset.univ fun a _ ↦
    integrable_standardRealGaussianMatrix_coordinate_mul a i j

theorem trace_inv_realWishartGram_invSqrtTwoScaleMatrix_mul_const
    {k p : ℕ} (R : Matrix (Fin k) (Fin p) ℝ)
    (D : Matrix (Fin p) (Fin p) ℝ)
    (hunit : IsUnit (realWishartGram R).det) :
    Matrix.trace
        ((realWishartGram (invSqrtTwoScaleMatrix k p R))⁻¹ * D) =
      2 * Matrix.trace ((realWishartGram R)⁻¹ * D) := by
  rw [realWishartGram_invSqrtTwoScaleMatrix]
  letI : Invertible (1 / 2 : ℝ) :=
    invertibleOfNonzero (by norm_num)
  rw [Matrix.inv_smul (A := realWishartGram R) (1 / 2 : ℝ) hunit,
    Matrix.smul_mul, Matrix.trace_smul]
  change (⅟ (1 / 2 : ℝ)) * Matrix.trace ((realWishartGram R)⁻¹ * D) =
    2 * Matrix.trace ((realWishartGram R)⁻¹ * D)
  norm_num

theorem integrable_trace_nonsingInv_realWishartGram_mul_const_standardGaussian
    {k p : ℕ} (hgap : p + 1 < k)
    (D : Matrix (Fin p) (Fin p) ℝ) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦
        Matrix.trace ((realWishartGram R)⁻¹ * D))
      (standardRealGaussianMatrixMeasure k p) := by
  let f : Matrix (Fin k) (Fin p) ℝ → ℝ :=
    fun R ↦ Matrix.trace ((realWishartGram R)⁻¹ * D)
  have hhalf : Integrable f (halfGaussianMatrix k p) :=
    integrable_trace_nonsingInv_realWishartGram_mul_const_halfGaussianMatrix
      hgap D
  rw [← map_invSqrtTwoScaleMatrix_standardRealGaussianMatrixMeasure] at hhalf
  have hcomp : Integrable (f ∘ invSqrtTwoScaleMatrix k p)
      (standardRealGaussianMatrixMeasure k p) :=
    (integrable_map_measure
      (measurable_trace_nonsingInv_realWishartGram_mul_const D).aestronglyMeasurable
      (measurable_invSqrtTwoScaleMatrix k p).aemeasurable).mp hhalf
  have hunit := ae_isUnit_det_realWishartGram_standardRealGaussianMatrixMeasure
    (k := k) (p := p) (Nat.le_of_lt (lt_trans (Nat.lt_succ_self p) hgap))
  have heq : f ∘ invSqrtTwoScaleMatrix k p =ᵐ[
      standardRealGaussianMatrixMeasure k p] fun R ↦ 2 * f R := by
    filter_upwards [hunit] with R hR
    exact trace_inv_realWishartGram_invSqrtTwoScaleMatrix_mul_const R D hR
  have htwice : Integrable (fun R ↦ 2 * f R)
      (standardRealGaussianMatrixMeasure k p) := hcomp.congr heq
  have hscaled := htwice.const_mul (1 / 2 : ℝ)
  simpa [f] using hscaled

theorem trace_mul_single_eq_entry
    {p : ℕ} (M : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :
    Matrix.trace (M * Matrix.single j i 1) = M i j := by
  simpa using Matrix.trace_mul_single M j i (1 : ℝ)

theorem integrable_nonsingInv_realWishartGram_entry_standardGaussian
    {k p : ℕ} (hgap : p + 1 < k) (i j : Fin p) :
    Integrable
      (fun R : Matrix (Fin k) (Fin p) ℝ ↦ (realWishartGram R)⁻¹ i j)
      (standardRealGaussianMatrixMeasure k p) := by
  have h :=
    integrable_trace_nonsingInv_realWishartGram_mul_const_standardGaussian
      hgap (Matrix.single j i 1)
  apply h.congr
  filter_upwards [] with R
  exact trace_mul_single_eq_entry (realWishartGram R)⁻¹ i j

theorem integrable_trace_const_mul_realWishartGram_standardGaussian
    (rows p : ℕ) (D : Matrix (Fin p) (Fin p) ℝ) :
    Integrable
      (fun A : Matrix (Fin rows) (Fin p) ℝ ↦
        Matrix.trace (D * realWishartGram A))
      (standardRealGaussianMatrixMeasure rows p) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply integrable_finsetSum Finset.univ
  intro i hi
  apply integrable_finsetSum Finset.univ
  intro j hj
  exact (integrable_realWishartGram_entry_standardGaussian rows p j i).const_mul
    (D i j)

theorem integral_trace_const_mul_realWishartGram_standardGaussian
    (rows p : ℕ) (D : Matrix (Fin p) (Fin p) ℝ) :
    (∫ A : Matrix (Fin rows) (Fin p) ℝ,
        Matrix.trace (D * realWishartGram A)
        ∂standardRealGaussianMatrixMeasure rows p) =
      (rows : ℝ) * Matrix.trace D := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [integral_finsetSum]
  · have hi (i : Fin p) :
        (∫ A : Matrix (Fin rows) (Fin p) ℝ,
            ∑ j, D i j * realWishartGram A j i
            ∂standardRealGaussianMatrixMeasure rows p) =
          (rows : ℝ) * D i i := by
      rw [integral_finsetSum]
      · simp_rw [integral_const_mul,
          integral_realWishartGram_entry_standardGaussian]
        simp
        ring
      · intro j hj
        exact (integrable_realWishartGram_entry_standardGaussian rows p j i).const_mul
          (D i j)
    simp_rw [hi]
    rw [← Finset.mul_sum]
  · intro i hi
    exact integrable_finsetSum Finset.univ fun j _ ↦
      (integrable_realWishartGram_entry_standardGaussian rows p j i).const_mul
        (D i j)

theorem integrable_realMatrixBetaPrime_trace_source
    {N K : ℕ} (hgap : N + 1 < K - N) :
    Integrable
      (fun p : Matrix (Fin (N + 1)) (Fin N) ℝ ×
          Matrix (Fin (K - N)) (Fin N) ℝ ↦
        Matrix.trace (realMatrixBetaPrimeOfGaussianSource p))
      (realBetaPrimeGaussianSourceLaw N K) := by
  unfold realBetaPrimeGaussianSourceLaw realMatrixBetaPrimeOfGaussianSource
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply integrable_finsetSum Finset.univ
  intro i hi
  apply integrable_finsetSum Finset.univ
  intro j hj
  have hA := integrable_realWishartGram_entry_standardGaussian (N + 1) N j i
  have hB := integrable_nonsingInv_realWishartGram_entry_standardGaussian
    hgap i j
  simpa [Function.uncurry, mul_comm] using hA.mul_prod hB

theorem integral_realMatrixBetaPrime_trace_source
    {N K : ℕ} (hgap : N + 1 < K - N) :
    (∫ p : Matrix (Fin (N + 1)) (Fin N) ℝ ×
        Matrix (Fin (K - N)) (Fin N) ℝ,
        Matrix.trace (realMatrixBetaPrimeOfGaussianSource p)
        ∂realBetaPrimeGaussianSourceLaw N K) =
      (N + 1 : ℝ) *
        ((N : ℝ) / (((K - N : ℕ) : ℝ) - (N : ℝ) - 1)) := by
  letI : IsProbabilityMeasure
      (standardRealGaussianMatrixMeasure (N + 1) N) :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  letI : IsProbabilityMeasure
      (standardRealGaussianMatrixMeasure (K - N) N) :=
    standardRealGaussianMatrixMeasure_isProbability_internal _ _
  have hint := integrable_realMatrixBetaPrime_trace_source hgap
  unfold realBetaPrimeGaussianSourceLaw at hint ⊢
  rw [integral_prod_symm _ hint]
  simp_rw [realMatrixBetaPrimeOfGaussianSource,
    integral_trace_const_mul_realWishartGram_standardGaussian]
  rw [integral_const_mul,
    standardGaussian_inverseWishart_trace_mean hgap]
  norm_num [Nat.cast_add]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
