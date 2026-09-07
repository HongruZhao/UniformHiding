import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredRankOneDensityScores
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatrixInverseMeasurability
import Mathlib.Tactic

/-!
# Measurability of the explicit first two centered scores

These are finite rational-matrix calculations.  They are separated from the
moment estimates so that low-order product integrability can use the existing
moment packages without assuming any measurability or Fubini interface.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem measurable_complexMatrix_conjTranspose
    {X : Type*} [MeasurableSpace X] {N : ℕ}
    {A : X → Matrix (Fin N) (Fin N) ℂ} (hA : Measurable A) :
    Measurable (fun x ↦ (A x).conjTranspose) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [Matrix.conjTranspose_apply]
  fun_prop

private theorem measurable_complexMatrix_one_sub
    {X : Type*} [MeasurableSpace X] {N : ℕ}
    {A : X → Matrix (Fin N) (Fin N) ℂ} (hA : Measurable A) :
    Measurable (fun x ↦ 1 - A x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact measurable_const.sub
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA))

/-- The total rational matrix statistic `Z` is measurable. -/
theorem measurable_concreteCOEZ_internal (N K : ℕ) :
    Measurable (concreteCOEZ (N := N) K) := by
  have hC : Measurable (unscaleCOECorner (N := N) K) :=
    measurable_unscaleCOECorner N K
  have hCstar : Measurable (fun A : ConcreteMatrixState N ↦
      (unscaleCOECorner K A).conjTranspose) :=
    measurable_complexMatrix_conjTranspose hC
  have hCstarC : Measurable (fun A : ConcreteMatrixState N ↦
      (unscaleCOECorner K A).conjTranspose * unscaleCOECorner K A) :=
    measurable_complexMatrix_mul hCstar hC
  have hden : Measurable (fun A : ConcreteMatrixState N ↦
      1 - (unscaleCOECorner K A).conjTranspose * unscaleCOECorner K A) :=
    measurable_complexMatrix_one_sub hCstarC
  have hdenInv : Measurable (fun A : ConcreteMatrixState N ↦
      (1 - (unscaleCOECorner K A).conjTranspose *
        unscaleCOECorner K A)⁻¹) :=
    (measurable_complexMatrix_inv N).comp hden
  have hCZ : Measurable (fun A : ConcreteMatrixState N ↦
      unscaleCOECorner K A *
        (1 - (unscaleCOECorner K A).conjTranspose *
          unscaleCOECorner K A)⁻¹) :=
    measurable_complexMatrix_mul hC hdenInv
  change Measurable (fun A : ConcreteMatrixState N ↦
    (unscaleCOECorner K A *
      (1 - (unscaleCOECorner K A).conjTranspose *
        unscaleCOECorner K A)⁻¹) *
      (unscaleCOECorner K A).conjTranspose)
  exact measurable_complexMatrix_mul hCZ hCstar

/-- The total rational matrix statistic `T` is measurable. -/
theorem measurable_concreteCOET_internal (N K : ℕ) :
    Measurable (concreteCOET (N := N) K) := by
  have hC : Measurable (unscaleCOECorner (N := N) K) :=
    measurable_unscaleCOECorner N K
  have hCstar : Measurable (fun A : ConcreteMatrixState N ↦
      (unscaleCOECorner K A).conjTranspose) :=
    measurable_complexMatrix_conjTranspose hC
  have hCCstar : Measurable (fun A : ConcreteMatrixState N ↦
      unscaleCOECorner K A * (unscaleCOECorner K A).conjTranspose) :=
    measurable_complexMatrix_mul hC hCstar
  have hden : Measurable (fun A : ConcreteMatrixState N ↦
      1 - unscaleCOECorner K A *
        (unscaleCOECorner K A).conjTranspose) :=
    measurable_complexMatrix_one_sub hCCstar
  have hdenInv : Measurable (fun A : ConcreteMatrixState N ↦
      (1 - unscaleCOECorner K A *
        (unscaleCOECorner K A).conjTranspose)⁻¹) :=
    (measurable_complexMatrix_inv N).comp hden
  change Measurable (fun A : ConcreteMatrixState N ↦
    (1 - unscaleCOECorner K A *
      (unscaleCOECorner K A).conjTranspose)⁻¹ *
        unscaleCOECorner K A)
  exact measurable_complexMatrix_mul hdenInv hC

/-- The scaled Hermitian statistic `Y` is measurable as a total matrix map. -/
theorem measurable_concreteCOEY_internal (N K : ℕ) :
    Measurable (concreteCOEY N K) := by
  have hZ := measurable_concreteCOEZ_internal N K
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [concreteCOEY, Matrix.smul_apply]
  fun_prop

/-- The auxiliary matrix `W=I+Y/c` is measurable. -/
theorem measurable_concreteCOEWMatrix_internal (N K : ℕ) :
    Measurable (concreteCOEWMatrix N K) := by
  have hY := measurable_concreteCOEY_internal N K
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [concreteCOEWMatrix, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply]
  fun_prop

/-- The auxiliary matrix `R=sqrt(c)T` is measurable. -/
theorem measurable_concreteCOERMatrix_internal (N K : ℕ) :
    Measurable (concreteCOERMatrix N K) := by
  have hT := measurable_concreteCOET_internal N K
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  simp only [concreteCOERMatrix, Matrix.smul_apply]
  fun_prop

private theorem measurable_centeredProjection_entry_on_product
    (N : ℕ) (i j : Fin N) :
    Measurable (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      complexCenteredRankOneProjection N Av.2 i j) := by
  unfold complexCenteredRankOneProjection
  exact (((measurable_pi_apply j).comp
    ((measurable_pi_apply i).comp
      ((measurable_complexRankOneProjection N).comp measurable_snd))).sub
        measurable_const)

private theorem measurable_complexCenteredProjectiveTracePair_product
    (N K : ℕ) :
    Measurable (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair Av.2 (concreteCOEY N K Av.1)) := by
  have hY : Measurable (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCOEY N K Av.1) :=
    (measurable_concreteCOEY_internal N K).comp measurable_fst
  unfold complexCenteredProjectiveTracePair complexProjectiveTracePair
  exact (Finset.measurable_sum _ fun i _ ↦
      Finset.measurable_sum _ fun j _ ↦
        (((measurable_pi_apply j).comp
          ((measurable_pi_apply i).comp
            ((measurable_complexRankOneProjection N).comp measurable_snd))).mul
          ((measurable_pi_apply i).comp
            ((measurable_pi_apply j).comp hY)))).sub
    (measurable_const.mul
      (Finset.measurable_sum _ fun i _ ↦
        (measurable_pi_apply i).comp ((measurable_pi_apply i).comp hY)))

/-- The concrete explicit first centered score is jointly measurable. -/
theorem measurable_concreteCenteredRankOneFirstDensityScore_product
    (N K : ℕ) :
    Measurable (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCenteredRankOneFirstDensityScore N K Av.2 Av.1) := by
  have hpair := measurable_complexCenteredProjectiveTracePair_product N K
  unfold concreteCenteredRankOneFirstDensityScore
    concreteCenteredRankOneFirstDensityScoreComplex
  exact Complex.continuous_re.measurable.comp (measurable_const.mul hpair)

private theorem measurable_complexCenteredProjectiveSandwich_product
    (N K : ℕ) :
    Measurable (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      complexCenteredProjectiveSandwich Av.2
        (concreteCOEWMatrix N K Av.1) (concreteCOEY N K Av.1)) := by
  have hW : Measurable (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCOEWMatrix N K Av.1) :=
    (measurable_concreteCOEWMatrix_internal N K).comp measurable_fst
  have hY : Measurable (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCOEY N K Av.1) :=
    (measurable_concreteCOEY_internal N K).comp measurable_fst
  unfold complexCenteredProjectiveSandwich
  exact Finset.measurable_sum _ fun a _ ↦
    Finset.measurable_sum _ fun b _ ↦
      Finset.measurable_sum _ fun c _ ↦
        Finset.measurable_sum _ fun d _ ↦
          (((measurable_centeredProjection_entry_on_product N a b).mul
              ((measurable_pi_apply c).comp
                ((measurable_pi_apply b).comp hW))).mul
              (measurable_centeredProjection_entry_on_product N c d)).mul
            ((measurable_pi_apply a).comp
              ((measurable_pi_apply d).comp hY))

private theorem measurable_complexCenteredProjectiveConjugateSandwich_product
    (N K : ℕ) :
    Measurable (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      complexCenteredProjectiveConjugateSandwich Av.2
        (concreteCOERMatrix N K Av.1)) := by
  have hR : Measurable (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCOERMatrix N K Av.1) :=
    (measurable_concreteCOERMatrix_internal N K).comp measurable_fst
  unfold complexCenteredProjectiveConjugateSandwich
  exact Finset.measurable_sum _ fun a _ ↦
    Finset.measurable_sum _ fun b _ ↦
      Finset.measurable_sum _ fun c _ ↦
        Finset.measurable_sum _ fun d _ ↦
          (((measurable_centeredProjection_entry_on_product N a b).mul
              ((measurable_pi_apply c).comp
                ((measurable_pi_apply b).comp hR))).mul
              (measurable_centeredProjection_entry_on_product N d c)).mul
            (by
              have hr := (measurable_pi_apply d).comp
                ((measurable_pi_apply a).comp hR)
              fun_prop)

/-- The concrete explicit second centered score is jointly measurable. -/
theorem measurable_concreteCenteredRankOneSecondDensityScore_product
    (N K : ℕ) :
    Measurable (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCenteredRankOneSecondDensityScore N K Av.2 Av.1) := by
  have hpair := measurable_complexCenteredProjectiveTracePair_product N K
  have hsand := measurable_complexCenteredProjectiveSandwich_product N K
  have hconj :=
    measurable_complexCenteredProjectiveConjugateSandwich_product N K
  unfold concreteCenteredRankOneSecondDensityScore
    concreteCenteredRankOneSecondDensityScoreComplex
  apply Complex.continuous_re.measurable.comp
  rw [show (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      (4 : ℂ) *
        (complexCenteredProjectiveTracePair Av.2
              (concreteCOEY N K Av.1) ^ 2 -
          complexCenteredProjectiveSandwich Av.2
              (concreteCOEWMatrix N K Av.1) (concreteCOEY N K Av.1) -
          complexCenteredProjectiveConjugateSandwich Av.2
              (concreteCOERMatrix N K Av.1))) =
      (fun _ : ConcreteMatrixState N × ComplexUnitSphere N ↦ (4 : ℂ)) *
        ((((fun Av ↦ complexCenteredProjectiveTracePair Av.2
              (concreteCOEY N K Av.1)) *
            (fun Av ↦ complexCenteredProjectiveTracePair Av.2
              (concreteCOEY N K Av.1))) -
          (fun Av ↦ complexCenteredProjectiveSandwich Av.2
            (concreteCOEWMatrix N K Av.1) (concreteCOEY N K Av.1))) -
          (fun Av ↦ complexCenteredProjectiveConjugateSandwich Av.2
            (concreteCOERMatrix N K Av.1))) by
    funext Av
    simp only [Pi.mul_apply, Pi.sub_apply, pow_two]]
  exact measurable_const.mul (((hpair.mul hpair).sub hsand).sub hconj)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
