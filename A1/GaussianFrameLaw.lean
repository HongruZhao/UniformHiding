import A1.GaussianFrameInvariance
import A1.HaarBridgeStiefel
import A1.NormalizedTransposeGram

open MeasureTheory Matrix
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable section
namespace A1Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem measurable_rectangular_matrix_mul {X : Type*} [MeasurableSpace X]
    {n k m : ℕ} (f : X → Matrix (Fin n) (Fin k) ℂ)
    (g : X → Matrix (Fin k) (Fin m) ℂ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x ↦ f x * g x) := by
  refine measurable_pi_lambda _ fun i ↦ measurable_pi_lambda _ fun j ↦ ?_
  change Measurable (fun x ↦ ∑ l : Fin k, f x i l * g x l j)
  refine Finset.measurable_sum _ fun l _ ↦ ?_
  have h1 : Measurable (fun x ↦ f x i l) :=
    (measurable_pi_apply l).comp ((measurable_pi_apply i).comp hf)
  have h2 : Measurable (fun x ↦ g x l j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply l).comp hg)
  exact h1.mul h2

theorem continuous_gaussianGramSqrt (n m : ℕ) :
    Continuous (fun G : Matrix (Fin n) (Fin m) ℂ ↦ CFC.sqrt (G.conjTranspose * G)) := by
  apply CFC.continuousOn_sqrt.comp_continuous
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
  intro G
  exact (Matrix.posSemidef_conjTranspose_mul_self G).nonneg

theorem measurable_gaussianPolarFrame (n m : ℕ) :
    Measurable (gaussianPolarFrame : Matrix (Fin n) (Fin m) ℂ →
      Matrix (Fin n) (Fin m) ℂ) := by
  have hi := (measurable_complexMatrix_nonsing_inv m).comp
    (continuous_gaussianGramSqrt n m).measurable
  exact measurable_rectangular_matrix_mul _ _ measurable_id hi

def gaussianPolarFrameLaw (n m : ℕ) : Measure (Matrix (Fin n) (Fin m) ℂ) :=
  (standardComplexGaussianRectangularMeasure n m).map gaussianPolarFrame

instance gaussianPolarFrameLaw_probability (n m : ℕ) :
    IsProbabilityMeasure (gaussianPolarFrameLaw n m) :=
  Measure.isProbabilityMeasure_map (measurable_gaussianPolarFrame n m).aemeasurable

theorem measurableSet_stiefel (n m : ℕ) :
    MeasurableSet {Q : Matrix (Fin n) (Fin m) ℂ | Q.conjTranspose * Q = 1} := by
  have hg : Measurable (fun Q : Matrix (Fin n) (Fin m) ℂ ↦ Q.conjTranspose * Q) :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).measurable
  exact (hg.eq_const (1 : Matrix (Fin m) (Fin m) ℂ)).setOf

theorem gaussianPolarFrameLaw_orthonormal {n m : ℕ} (hmn : m ≤ n) :
    ∀ᵐ Q ∂gaussianPolarFrameLaw n m, Q.conjTranspose * Q = 1 := by
  apply (ae_map_iff (measurable_gaussianPolarFrame n m).aemeasurable
    (measurableSet_stiefel n m)).mpr
  filter_upwards [ae_posDef_Gram_standardComplexGaussian n m hmn] with G hG
  exact gaussianPolarFrame_gram G hG

theorem gaussianPolarFrameLaw_invariant {n m : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    (gaussianPolarFrameLaw n m).map (fun Q ↦ (U : Matrix (Fin n) (Fin n) ℂ) * Q) =
      gaussianPolarFrameLaw n m := by
  have haction : Measurable (fun Q : Matrix (Fin n) (Fin m) ℂ ↦
      (U : Matrix (Fin n) (Fin n) ℂ) * Q) :=
    (measurePreserving_unitaryGaussianMatrix U).measurable
  have heq : (fun Q : Matrix (Fin n) (Fin m) ℂ ↦
      (U : Matrix (Fin n) (Fin n) ℂ) * Q) ∘ gaussianPolarFrame =
      gaussianPolarFrame ∘ (fun G ↦ (U : Matrix (Fin n) (Fin n) ℂ) * G) := by
    funext G
    exact (gaussianPolarFrame_unitary_mul U G).symm
  unfold gaussianPolarFrameLaw
  rw [Measure.map_map haction (measurable_gaussianPolarFrame n m), heq,
    ← Measure.map_map (measurable_gaussianPolarFrame n m) haction,
    (measurePreserving_unitaryGaussianMatrix U).map_eq]

/-- The actual Gaussian polar frame has the exact leading-column Haar law. -/
theorem gaussianPolarFrameLaw_eq_haar {n m : ℕ} (hmn : m ≤ n) :
    gaussianPolarFrameLaw n m =
      (unitaryHaarProbabilityMeasure n).map (firstColumns hmn) :=
  stiefel_probability_eq_haar_firstColumns hmn _
    (gaussianPolarFrameLaw_orthonormal hmn) gaussianPolarFrameLaw_invariant

theorem gaussianPolarFrame_overlap_eq_normalizedTransposeGram {n m : ℕ}
    (G : Matrix (Fin n) (Fin m) ℂ) :
    (gaussianPolarFrame G).transpose * gaussianPolarFrame G = normalizedTransposeGram G :=
  gaussianPolarFrame_overlap G

end A1Research
