import A3.HermitianOrbitTangent
import A3.HermitianConjugation

open scoped BigOperators Matrix Matrix.Norms.Elementwise

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

def hermitianOrbitMatrix (U : Matrix.unitaryGroup (Fin n) K) (lambda : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) K :=
  U.val * Matrix.diagonal (fun i ↦ (lambda i : K)) * U.val.conjTranspose

theorem hermitianOrbitMatrix_isHermitian (U : Matrix.unitaryGroup (Fin n) K)
    (lambda : Fin n → ℝ) : (hermitianOrbitMatrix U lambda).IsHermitian := by
  apply Matrix.isHermitian_mul_mul_conjTranspose
  apply Matrix.isHermitian_diagonal_of_self_adjoint
  funext i
  simp

def hermitianOrbitCoordinates (U : Matrix.unitaryGroup (Fin n) K) (lambda : Fin n → ℝ) :
    HermitianCoordinates n K := hermitianCoordinateProjection (hermitianOrbitMatrix U lambda)

@[simp] theorem hermitianOrbitCoordinates_reconstruct (U : Matrix.unitaryGroup (Fin n) K)
    (lambda : Fin n → ℝ) :
    hermitianMatrixOfCoordinates (hermitianOrbitCoordinates U lambda) =
      hermitianOrbitMatrix U lambda :=
  hermitianMatrixOfCoordinates_projection _ (hermitianOrbitMatrix_isHermitian U lambda)

def hermitianCayleyOrbitChart (U : Matrix.unitaryGroup (Fin n) K)
    (x : HermitianCoordinates n K) : HermitianCoordinates n K :=
  hermitianOrbitCoordinates (U * hermitianAngularCayley x.2) x.1

def hermitianCayleyOrbitChartDerivative (U : Matrix.unitaryGroup (Fin n) K)
    (x : HermitianCoordinates n K) :
    HermitianCoordinates n K →L[ℝ] HermitianCoordinates n K :=
  (hermitianConjugationRepresentation n K (U * hermitianAngularCayley x.2)).toContinuousLinearMap.comp
    ((hermitianDiagonalDifferential x.1).toContinuousLinearMap.comp
      (hermitianOrbitSourceDifferential x.2).toContinuousLinearMap)

theorem abs_det_hermitianCayleyOrbitChartDerivative (U : Matrix.unitaryGroup (Fin n) K)
    (x : HermitianCoordinates n K) :
    |LinearMap.det (hermitianCayleyOrbitChartDerivative U x).toLinearMap| =
      hermitianAngularDensity x.2 * hermitianVandermonde x.1 ^ Module.finrank ℝ K := by
  change |LinearMap.det ((hermitianConjugationRepresentation n K
    (U * hermitianAngularCayley x.2)).comp
      ((hermitianDiagonalDifferential x.1).comp (hermitianOrbitSourceDifferential x.2)))| = _
  rw [LinearMap.det_comp, LinearMap.det_comp, abs_mul, abs_mul,
    abs_det_hermitianConjugationRepresentation, one_mul,
    hermitianOrbitSourceDifferential_det, abs_det_hermitianDiagonalDifferential]
  exact mul_comm _ _

theorem hermitianCayleyOrbitChartDerivative_det_ne_zero (U : Matrix.unitaryGroup (Fin n) K)
    (x : HermitianCoordinates n K) (ha : 0 < hermitianAngularDensity x.2)
    (hlambda : Function.Injective x.1) :
    LinearMap.det (hermitianCayleyOrbitChartDerivative U x).toLinearMap ≠ 0 := by
  have hv : 0 < hermitianVandermonde x.1 := by
    apply Finset.prod_pos
    intro ij _
    exact abs_pos.mpr (sub_ne_zero.mpr (fun h ↦ (ne_of_lt ij.2).symm (hlambda h)))
  have h : 0 < hermitianAngularDensity x.2 *
      hermitianVandermonde x.1 ^ Module.finrank ℝ K := mul_pos ha (pow_pos hv _)
  rw [← abs_det_hermitianCayleyOrbitChartDerivative U x] at h
  exact abs_pos.mp h

theorem hermitianSkewCommutator_reconstruct (H : Matrix (Fin n) (Fin n) K)
    (hH : H.conjTranspose = -H) (lambda v : Fin n → ℝ) :
    hermitianMatrixOfCoordinates (hermitianDiagonalDifferential lambda
      (v, fun ij ↦ H ij.1.1 ij.1.2)) =
      H * Matrix.diagonal (fun i ↦ (lambda i : K)) -
        Matrix.diagonal (fun i ↦ (lambda i : K)) * H +
          Matrix.diagonal (fun i ↦ (v i : K)) := by
  let D : Matrix (Fin n) (Fin n) K := Matrix.diagonal (fun i ↦ (lambda i : K))
  let R : Matrix (Fin n) (Fin n) K := Matrix.diagonal (fun i ↦ (v i : K))
  have hD : D.IsHermitian := by
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    funext i
    simp
  have hR : R.IsHermitian := by
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    funext i
    simp
  have hC : (H * D - D * H + R).IsHermitian := by
    change (H * D - D * H + R).conjTranspose = H * D - D * H + R
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hH, hD.eq, hR.eq]
    noncomm_ring
  have hp : hermitianCoordinateProjection (H * D - D * H + R) =
      hermitianDiagonalDifferential lambda (v, fun ij ↦ H ij.1.1 ij.1.2) := by
    apply Prod.ext
    · funext i
      change RCLike.re ((H * D - D * H + R) i i) = v i
      simp only [D, R, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal,
        Matrix.diagonal_mul, Matrix.diagonal_apply_eq]
      rw [show H i i * (lambda i : K) - (lambda i : K) * H i i + (v i : K) = v i by ring]
      simp
    · funext ij
      change (H * D - D * H + R) ij.1.1 ij.1.2 =
        (lambda ij.1.2 - lambda ij.1.1) • H ij.1.1 ij.1.2
      simp [D, R, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal,
        Matrix.diagonal_mul, ne_of_lt ij.2, RCLike.real_smul_eq_coe_mul]
      ring
  rw [← hp]
  exact hermitianMatrixOfCoordinates_projection _ hC

end A3Research
