import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import Mathlib.Tactic

/-!
# Measurability of the finite matrix inverse and trace maps

The nonsingular matrix inverse used by the beta-prime model is a total
rational function (zero on the singular locus).  This file proves its
measurability directly from the determinant--adjugate formula, eliminating
what had only been a technical external interface.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

private theorem measurable_realMatrix_det (N : ℕ) :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A.det) := by
  simp only [Matrix.det_apply']
  fun_prop

private theorem measurable_complexMatrix_det (N : ℕ) :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℂ ↦ A.det) := by
  simp only [Matrix.det_apply']
  fun_prop

private theorem measurable_realMatrix_updateRow (N : ℕ)
    (j : Fin N) (b : Fin N → ℝ) :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A.updateRow j b) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun k ↦ ?_
  by_cases hij : i = j
  · simp [Matrix.updateRow_apply, hij]
  · simp only [Matrix.updateRow_apply, if_neg hij]
    exact (measurable_pi_apply k).comp (measurable_pi_apply i)

private theorem measurable_complexMatrix_updateRow (N : ℕ)
    (j : Fin N) (b : Fin N → ℂ) :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℂ ↦ A.updateRow j b) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun k ↦ ?_
  by_cases hij : i = j
  · simp [Matrix.updateRow_apply, hij]
  · simp only [Matrix.updateRow_apply, if_neg hij]
    exact (measurable_pi_apply k).comp (measurable_pi_apply i)

private theorem measurable_realMatrix_adjugate (N : ℕ) :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A.adjugate) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.adjugate_apply]
  exact (measurable_realMatrix_det N).comp
    (measurable_realMatrix_updateRow N j (Pi.single i 1))

private theorem measurable_complexMatrix_adjugate (N : ℕ) :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℂ ↦ A.adjugate) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.adjugate_apply]
  exact (measurable_complexMatrix_det N).comp
    (measurable_complexMatrix_updateRow N j (Pi.single i 1))

/-- Total inverse of a finite real matrix is measurable. -/
theorem measurable_realMatrix_inv (N : ℕ) :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A⁻¹) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv]
  exact (measurable_inv.comp (measurable_realMatrix_det N)).mul
    ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (measurable_realMatrix_adjugate N)))

/-- Total inverse of a finite complex matrix is measurable. -/
theorem measurable_complexMatrix_inv (N : ℕ) :
    Measurable (fun A : Matrix (Fin N) (Fin N) ℂ ↦ A⁻¹) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv]
  exact (measurable_inv.comp (measurable_complexMatrix_det N)).mul
    ((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp (measurable_complexMatrix_adjugate N)))

private theorem measurable_realMatrix_mul
    {X : Type*} [MeasurableSpace X]
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    {A : X → Matrix l m ℝ} {B : X → Matrix m n ℝ}
    (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x ↦ A x * B x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun q _ ↦
    ((measurable_pi_apply q).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply q).comp hB))

private theorem measurable_complexMatrix_mul_dense
    {X : Type*} [MeasurableSpace X]
    {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]
    {A : X → Matrix l m ℂ} {B : X → Matrix m n ℂ}
    (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x ↦ A x * B x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun q _ ↦
    ((measurable_pi_apply q).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply q).comp hB))

private theorem measurable_realMatrix_pow
    {X : Type*} [MeasurableSpace X] {N : ℕ}
    {A : X → Matrix (Fin N) (Fin N) ℝ} (hA : Measurable A) :
    ∀ r : ℕ, Measurable (fun x ↦ (A x) ^ r) := by
  intro r
  induction r with
  | zero => simpa using
      (measurable_const : Measurable
        (fun _ : X ↦ (1 : Matrix (Fin N) (Fin N) ℝ)))
  | succ r hr =>
      simpa [pow_succ] using measurable_realMatrix_mul hr hA

private theorem measurable_complexMatrix_pow
    {X : Type*} [MeasurableSpace X] {N : ℕ}
    {A : X → Matrix (Fin N) (Fin N) ℂ} (hA : Measurable A) :
    ∀ r : ℕ, Measurable (fun x ↦ (A x) ^ r) := by
  intro r
  induction r with
  | zero => simpa using
      (measurable_const : Measurable
        (fun _ : X ↦ (1 : Matrix (Fin N) (Fin N) ℂ)))
  | succ r hr =>
      simpa [pow_succ] using measurable_complexMatrix_mul_dense hr hA

private theorem measurable_realMatrix_trace
    {X : Type*} [MeasurableSpace X] {N : ℕ}
    {A : X → Matrix (Fin N) (Fin N) ℝ} (hA : Measurable A) :
    Measurable (fun x ↦ Matrix.trace (A x)) := by
  simp only [Matrix.trace]
  exact Finset.measurable_sum _ fun i _ ↦
    (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hA)

private theorem measurable_complexMatrix_trace_re
    {X : Type*} [MeasurableSpace X] {N : ℕ}
    {A : X → Matrix (Fin N) (Fin N) ℂ} (hA : Measurable A) :
    Measurable (fun x ↦ (Matrix.trace (A x)).re) := by
  have ht : Measurable (fun x ↦ Matrix.trace (A x)) := by
    simp only [Matrix.trace]
    exact Finset.measurable_sum _ fun i _ ↦
      (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hA)
  fun_prop

private theorem measurable_realWishartGram_from_source
    {rows N : ℕ} :
    Measurable (fun A : Matrix (Fin rows) (Fin N) ℝ ↦
      Wishart.realWishartGram A) := by
  unfold Wishart.realWishartGram
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

/-- The finite trace-power vector of the real beta-prime Gaussian source is
measurable; no random-matrix theorem is used. -/
theorem measurable_realBetaPrimeTracePowerVector_internal
    (r N K : ℕ) :
    Measurable (realBetaPrimeTracePowerVector r N K) := by
  let Source :=
    Matrix (Fin (N + 1)) (Fin N) ℝ × Matrix (Fin (K - N)) (Fin N) ℝ
  have hA : Measurable (fun p : Source ↦ Wishart.realWishartGram p.1) :=
    measurable_realWishartGram_from_source.comp measurable_fst
  have hB : Measurable (fun p : Source ↦ Wishart.realWishartGram p.2) :=
    measurable_realWishartGram_from_source.comp measurable_snd
  have hBinv : Measurable
      (fun p : Source ↦ (Wishart.realWishartGram p.2)⁻¹) :=
    (measurable_realMatrix_inv N).comp hB
  have hY : Measurable (fun p : Source ↦ realMatrixBetaPrimeOfGaussianSource p) := by
    simpa [realMatrixBetaPrimeOfGaussianSource] using
      measurable_realMatrix_mul hBinv hA
  refine measurable_pi_lambda _ fun j ↦ ?_
  exact measurable_realMatrix_trace
    (measurable_realMatrix_pow hY (j.1 + 1))

/-- The finite trace-power vector of the concrete COE statistic is
measurable; this is a direct rational-matrix calculation. -/
theorem measurable_concreteCOETracePowerVector_internal
    (r N K : ℕ) :
    Measurable (concreteCOETracePowerVector r N K) := by
  have hC : Measurable
      (unscaleCOECorner (N := N) K) := measurable_unscaleCOECorner N K
  have hCstar : Measurable
      (fun A : Dense.ConcreteMatrixState N ↦
        (unscaleCOECorner K A).conjTranspose) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    simp only [Matrix.conjTranspose_apply]
    fun_prop
  have hCstarC : Measurable
      (fun A : Dense.ConcreteMatrixState N ↦
        (unscaleCOECorner K A).conjTranspose * unscaleCOECorner K A) :=
    measurable_complexMatrix_mul_dense hCstar hC
  have hden : Measurable
      (fun A : Dense.ConcreteMatrixState N ↦
        1 - (unscaleCOECorner K A).conjTranspose * unscaleCOECorner K A) := by
    refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
    exact measurable_const.sub
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hCstarC))
  have hdenInv : Measurable
      (fun A : Dense.ConcreteMatrixState N ↦
        (1 - (unscaleCOECorner K A).conjTranspose *
          unscaleCOECorner K A)⁻¹) :=
    (measurable_complexMatrix_inv N).comp hden
  have hCZ : Measurable (fun A : Dense.ConcreteMatrixState N ↦
      unscaleCOECorner K A *
        (1 - (unscaleCOECorner K A).conjTranspose *
          unscaleCOECorner K A)⁻¹) :=
    measurable_complexMatrix_mul_dense hC hdenInv
  have hZ : Measurable (concreteCOEZ (N := N) K) := by
    change @Measurable (Dense.ConcreteMatrixState N)
      (Matrix (Fin N) (Fin N) ℂ)
      (denseScoreComplexSquareMatrixMeasurableSpace N)
      (denseScoreComplexSquareMatrixMeasurableSpace N)
      (concreteCOEZ (N := N) K)
    change Measurable (fun A : Dense.ConcreteMatrixState N ↦
      (unscaleCOECorner K A *
        (1 - (unscaleCOECorner K A).conjTranspose *
          unscaleCOECorner K A)⁻¹) *
        (unscaleCOECorner K A).conjTranspose)
    exact measurable_complexMatrix_mul_dense hCZ hCstar
  refine measurable_pi_lambda _ fun j ↦ ?_
  exact measurable_complexMatrix_trace_re
    (measurable_complexMatrix_pow hZ (j.1 + 1))

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
