import A1.GaussianFrameLaw

open Matrix MeasureTheory
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section
namespace A1Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem firstColumns_overlap_cornerTranspose {n m : ℕ} (hmn : m ≤ n)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (firstColumns hmn U).transpose * firstColumns hmn U =
      FriedmanMelloA1.s hmn (FriedmanMelloA1.S (UnitaryGroup.transpose U)) := by
  ext i j
  rfl

theorem measurable_frameTransposeOverlap (n m : ℕ) :
    Measurable (fun Q : Matrix (Fin n) (Fin m) ℂ ↦ Q.transpose * Q) :=
  (continuous_id.matrix_transpose.matrix_mul continuous_id).measurable

theorem measurable_coeCorner {n m : ℕ} (hmn : m ≤ n) :
    Measurable (fun U : Matrix.unitaryGroup (Fin n) ℂ ↦
      FriedmanMelloA1.s hmn (FriedmanMelloA1.S U)) := by
  have hS : Measurable (fun U : Matrix.unitaryGroup (Fin n) ℂ ↦
      (U : Matrix (Fin n) (Fin n) ℂ) *
        (U : Matrix (Fin n) (Fin n) ℂ).transpose) :=
    (continuous_subtype_val.matrix_mul
      continuous_subtype_val.matrix_transpose).measurable
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  exact (measurable_pi_apply (Fin.castLE hmn j)).comp
    ((measurable_pi_apply (Fin.castLE hmn i)).comp hS)

theorem measurable_normalizedTransposeGram (n m : ℕ) :
    Measurable (normalizedTransposeGram : Matrix (Fin n) (Fin m) ℂ →
      Matrix (Fin m) (Fin m) ℂ) := by
  have heq : (normalizedTransposeGram : Matrix (Fin n) (Fin m) ℂ →
      Matrix (Fin m) (Fin m) ℂ) =
      (fun Q : Matrix (Fin n) (Fin m) ℂ ↦ Q.transpose * Q) ∘ gaussianPolarFrame := by
    funext G
    exact (gaussianPolarFrame_overlap_eq_normalizedTransposeGram G).symm
  rw [heq]
  exact (measurable_frameTransposeOverlap n m).comp (measurable_gaussianPolarFrame n m)

/-- The full matrix law of the actual Gaussian normalized transpose Gram is the full
matrix law of the leading COE block from the original A1 target. -/
theorem normalizedTransposeGramLaw_eq_haar_coeCorner {n m : ℕ} (hmn : m ≤ n) :
    (standardComplexGaussianRectangularMeasure n m).map normalizedTransposeGram =
      (unitaryHaarProbabilityMeasure n).map (fun U ↦
        FriedmanMelloA1.s hmn (FriedmanMelloA1.S U)) := by
  let overlap : Matrix (Fin n) (Fin m) ℂ → Matrix (Fin m) (Fin m) ℂ :=
    fun Q ↦ Q.transpose * Q
  let corner : Matrix.unitaryGroup (Fin n) ℂ → Matrix (Fin m) (Fin m) ℂ :=
    fun U ↦ FriedmanMelloA1.s hmn (FriedmanMelloA1.S U)
  have heq : normalizedTransposeGram = overlap ∘ (gaussianPolarFrame (n := n) (m := m)) := by
    funext G
    exact (gaussianPolarFrame_overlap_eq_normalizedTransposeGram G).symm
  calc
    (standardComplexGaussianRectangularMeasure n m).map normalizedTransposeGram =
        (gaussianPolarFrameLaw n m).map overlap := by
      unfold gaussianPolarFrameLaw
      rw [Measure.map_map (measurable_frameTransposeOverlap n m)
        (measurable_gaussianPolarFrame n m), heq]
    _ = (unitaryHaarProbabilityMeasure n).map (overlap ∘ firstColumns hmn) := by
      rw [gaussianPolarFrameLaw_eq_haar hmn,
        Measure.map_map (measurable_frameTransposeOverlap n m) (measurable_firstColumns hmn)]
    _ = (unitaryHaarProbabilityMeasure n).map (corner ∘ UnitaryGroup.transpose) := by
      rfl
    _ = (unitaryHaarProbabilityMeasure n).map corner := by
      rw [← Measure.map_map (measurable_coeCorner hmn)
        (measurePreserving_unitaryTranspose n).measurable,
        (measurePreserving_unitaryTranspose n).map_eq]

end A1Research
