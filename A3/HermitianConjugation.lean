import A3.HermitianCoordinates
import A3.FlagCompactness
import A3.Shared.CompactDeterminant

open scoped Matrix Matrix.Norms.Elementwise
open MeasureTheory

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

def hermitianMatrixConjugationLinearMap (U : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) K →ₗ[ℝ] Matrix (Fin n) (Fin n) K where
  toFun := fun H ↦ U * H * U.conjTranspose
  map_add' := fun _ _ ↦ by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' := fun _ _ ↦ by simp [Matrix.mul_smul, Matrix.smul_mul]

def hermitianCoordinateConjugationLinearMap (U : Matrix (Fin n) (Fin n) K) :
    HermitianCoordinates n K →ₗ[ℝ] HermitianCoordinates n K :=
  (hermitianCoordinateProjectionLinearMap n K).comp
    ((hermitianMatrixConjugationLinearMap U).comp
      (hermitianMatrixOfCoordinatesLinearMap n K))

theorem hermitianCoordinateConjugation_reconstruct (U : Matrix (Fin n) (Fin n) K)
    (x : HermitianCoordinates n K) :
    hermitianMatrixOfCoordinates (hermitianCoordinateConjugationLinearMap U x) =
      U * hermitianMatrixOfCoordinates x * U.conjTranspose :=
  hermitianMatrixOfCoordinates_projection _
    (Matrix.isHermitian_mul_mul_conjTranspose U
      (hermitianMatrixOfCoordinates_isHermitian x))

theorem hermitianCoordinateConjugation_one (n : ℕ) (K : Type*) [RCLike K] :
    hermitianCoordinateConjugationLinearMap (1 : Matrix (Fin n) (Fin n) K) = 1 := by
  apply LinearMap.ext
  intro x
  change hermitianCoordinateProjection
    (1 * hermitianMatrixOfCoordinates x * (1 : Matrix (Fin n) (Fin n) K).conjTranspose) = x
  simpa only [Matrix.conjTranspose_one, one_mul, mul_one] using
    hermitianCoordinateProjection_ofCoordinates x

theorem hermitianCoordinateConjugation_mul (U V : Matrix (Fin n) (Fin n) K) :
    hermitianCoordinateConjugationLinearMap (U * V) =
      hermitianCoordinateConjugationLinearMap U * hermitianCoordinateConjugationLinearMap V := by
  apply LinearMap.ext
  intro x
  change hermitianCoordinateProjection
    ((U * V) * hermitianMatrixOfCoordinates x * (U * V).conjTranspose) =
      hermitianCoordinateProjection (U * hermitianMatrixOfCoordinates
        (hermitianCoordinateConjugationLinearMap V x) * U.conjTranspose)
  rw [hermitianCoordinateConjugation_reconstruct, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

def hermitianConjugationRepresentation (n : ℕ) (K : Type*) [RCLike K] :
    Matrix.unitaryGroup (Fin n) K →*
      (HermitianCoordinates n K →ₗ[ℝ] HermitianCoordinates n K) where
  toFun := fun U ↦ hermitianCoordinateConjugationLinearMap U.val
  map_one' := hermitianCoordinateConjugation_one n K
  map_mul' := fun U V ↦ hermitianCoordinateConjugation_mul U.val V.val

theorem continuous_hermitianConjugationRepresentation_apply (x : HermitianCoordinates n K) :
    Continuous (fun U : Matrix.unitaryGroup (Fin n) K ↦
      hermitianConjugationRepresentation n K U x) := by
  change Continuous (fun U : Matrix.unitaryGroup (Fin n) K ↦
    hermitianCoordinateProjection (U.val * hermitianMatrixOfCoordinates x * U.val.conjTranspose))
  exact continuous_hermitianCoordinateProjection.comp (by fun_prop)

theorem continuous_det_hermitianConjugationRepresentation :
    Continuous (fun U : Matrix.unitaryGroup (Fin n) K ↦
      LinearMap.det (hermitianConjugationRepresentation n K U)) := by
  classical
  let b := Module.finBasis ℝ (HermitianCoordinates n K)
  have hm : Continuous (fun U : Matrix.unitaryGroup (Fin n) K ↦
      LinearMap.toMatrix b b (hermitianConjugationRepresentation n K U)) := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    simp only [LinearMap.toMatrix_apply]
    exact (continuous_apply i).comp
      (b.continuous_coe_repr.comp (continuous_hermitianConjugationRepresentation_apply (b j)))
  have heq : (fun U : Matrix.unitaryGroup (Fin n) K ↦
      LinearMap.det (hermitianConjugationRepresentation n K U)) =
      fun U ↦ (LinearMap.toMatrix b b (hermitianConjugationRepresentation n K U)).det := by
    funext U
    exact (LinearMap.det_toMatrix b _).symm
  rw [heq]
  exact hm.matrix_det

/-- Actual unitary conjugation preserves flat independent Hermitian coordinates. -/
theorem abs_det_hermitianConjugationRepresentation (U : Matrix.unitaryGroup (Fin n) K) :
    |LinearMap.det (hermitianConjugationRepresentation n K U)| = 1 :=
  abs_eq_one_compact_character (LinearMap.det.comp (hermitianConjugationRepresentation n K))
    continuous_det_hermitianConjugationRepresentation U

end A3Research
