import A3.MatrixProductDerivativeRCLike
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! The derivative of the literal nonsingular matrix inverse, obtained
from its smooth polynomial formula and the local inverse identity. -/

open Filter
open scoped Topology Matrix.Norms.Elementwise ContDiff

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace A3Research

variable {K : Type*} [RCLike K]

def matrixInverseDerivativeRCLike {N : ℕ} (A : Matrix (Fin N) (Fin N) K) :
    Matrix (Fin N) (Fin N) K →L[ℝ] Matrix (Fin N) (Fin N) K :=
  -((mulLeftLinearMap (Fin N) ℝ A⁻¹).toContinuousLinearMap.comp
      (mulRightLinearMap (Fin N) ℝ A⁻¹).toContinuousLinearMap)

@[simp] theorem matrixInverseDerivativeRCLike_apply {N : ℕ}
    (A D : Matrix (Fin N) (Fin N) K) :
    matrixInverseDerivativeRCLike A D = -(A⁻¹ * D * A⁻¹) := by
  simp [matrixInverseDerivativeRCLike, Matrix.mul_assoc]

theorem hasFDerivAt_matrix_nonsing_inv_rclike {N : ℕ} (A : Matrix (Fin N) (Fin N) K)
    (hdet : A.det ≠ 0) :
    HasFDerivAt (fun B : Matrix (Fin N) (Fin N) K => B⁻¹)
      (matrixInverseDerivativeRCLike A) A := by
  let invMap := fun B : Matrix (Fin N) (Fin N) K => B⁻¹
  have hi : ContDiffAt ℝ 1 invMap A :=
    contDiffAt_matrix_nonsing_inv contDiffAt_id hdet
  have hd : DifferentiableAt ℝ invMap A := hi.differentiableAt_one
  have hprod := hasFDerivAt_matrix_mul_rclike (hasFDerivAt_id A) hd.hasFDerivAt
  have he : ∀ᶠ B : Matrix (Fin N) (Fin N) K in 𝓝 A, B.det ≠ 0 :=
    (contDiff_matrix_det (contDiff_id (𝕜 := ℝ) (n := 1))).continuous.continuousAt.eventually_ne hdet
  have heq : (fun _ : Matrix (Fin N) (Fin N) K => (1 : Matrix (Fin N) (Fin N) K)) =ᶠ[𝓝 A]
      (fun B => B * invMap B) := by
    filter_upwards [he] with B hB
    exact (Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB)).symm
  have hz := (hprod.congr_of_eventuallyEq heq).unique
    (hasFDerivAt_const (1 : Matrix (Fin N) (Fin N) K) A)
  have hder : fderiv ℝ invMap A = matrixInverseDerivativeRCLike A := by
    apply ContinuousLinearMap.ext
    intro D
    have hv := congrArg (fun L : Matrix (Fin N) (Fin N) K →L[ℝ] Matrix (Fin N) (Fin N) K => L D) hz
    change D * A⁻¹ + A * fderiv ℝ invMap A D = 0 at hv
    have hm := congrArg (fun B : Matrix (Fin N) (Fin N) K => A⁻¹ * B) hv
    simp only [Matrix.mul_add, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet), one_mul, Matrix.mul_zero] at hm
    simp only [matrixInverseDerivativeRCLike_apply]
    exact eq_neg_of_add_eq_zero_right hm
  rw [← hder]
  exact hd.hasFDerivAt

end A3Research
