import A3.Shared.MatrixProductSmooth
import Mathlib.Analysis.Calculus.FDeriv.Congr

/-! The derivative of the literal nonsingular matrix inverse, obtained
from its smooth polynomial formula and the local inverse identity. -/

open Filter
open scoped Topology Matrix.Norms.Elementwise ContDiff

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace A3Research

def matrixInverseDerivative {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  -((mulLeftLinearMap (Fin N) ℝ A⁻¹).toContinuousLinearMap.comp
      (mulRightLinearMap (Fin N) ℝ A⁻¹).toContinuousLinearMap)

@[simp] theorem matrixInverseDerivative_apply {N : ℕ}
    (A D : Matrix (Fin N) (Fin N) ℂ) :
    matrixInverseDerivative A D = -(A⁻¹ * D * A⁻¹) := by
  simp [matrixInverseDerivative, Matrix.mul_assoc]

theorem hasFDerivAt_matrix_nonsing_inv {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (hdet : A.det ≠ 0) :
    HasFDerivAt (fun B : Matrix (Fin N) (Fin N) ℂ => B⁻¹)
      (matrixInverseDerivative A) A := by
  let invMap := fun B : Matrix (Fin N) (Fin N) ℂ => B⁻¹
  have hi : ContDiffAt ℝ 1 invMap A :=
    contDiffAt_matrix_nonsing_inv contDiffAt_id hdet
  have hd : DifferentiableAt ℝ invMap A := hi.differentiableAt_one
  have hprod := hasFDerivAt_matrix_mul (hasFDerivAt_id A) hd.hasFDerivAt
  have he : ∀ᶠ B : Matrix (Fin N) (Fin N) ℂ in 𝓝 A, B.det ≠ 0 :=
    (contDiff_matrix_det (contDiff_id (𝕜 := ℝ) (n := 1))).continuous.continuousAt.eventually_ne hdet
  have heq : (fun _ : Matrix (Fin N) (Fin N) ℂ => (1 : Matrix (Fin N) (Fin N) ℂ)) =ᶠ[𝓝 A]
      (fun B => B * invMap B) := by
    filter_upwards [he] with B hB
    exact (Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB)).symm
  have hz := (hprod.congr_of_eventuallyEq heq).unique
    (hasFDerivAt_const (1 : Matrix (Fin N) (Fin N) ℂ) A)
  have hder : fderiv ℝ invMap A = matrixInverseDerivative A := by
    apply ContinuousLinearMap.ext
    intro D
    have hv := congrArg (fun L : Matrix (Fin N) (Fin N) ℂ →L[ℝ] Matrix (Fin N) (Fin N) ℂ => L D) hz
    change D * A⁻¹ + A * fderiv ℝ invMap A D = 0 at hv
    have hm := congrArg (fun B : Matrix (Fin N) (Fin N) ℂ => A⁻¹ * B) hv
    simp only [Matrix.mul_add, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet), one_mul, Matrix.mul_zero] at hm
    simp only [matrixInverseDerivative_apply]
    exact eq_neg_of_add_eq_zero_right hm
  rw [← hder]
  exact hd.hasFDerivAt

end A3Research
