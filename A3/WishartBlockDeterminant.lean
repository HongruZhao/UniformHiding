import A3.Definitions

noncomputable section

namespace A3Research

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

def wishartLowerBlockMap (A : E →ₗ[ℝ] E) (B : E →ₗ[ℝ] F) (D : F →ₗ[ℝ] F) :
    E × F →ₗ[ℝ] E × F :=
  (A.comp (LinearMap.fst ℝ E F)).prod
    ((B.comp (LinearMap.fst ℝ E F)) + (D.comp (LinearMap.snd ℝ E F)))

@[simp] theorem wishartLowerBlockMap_apply (A : E →ₗ[ℝ] E) (B : E →ₗ[ℝ] F)
    (D : F →ₗ[ℝ] F) (x : E × F) :
    wishartLowerBlockMap A B D x = (A x.1, B x.1 + D x.2) := rfl

/-- Off-diagonal differential blocks do not contribute to the real Jacobian. -/
theorem det_wishartLowerBlockMap (A : E →ₗ[ℝ] E) (B : E →ₗ[ℝ] F) (D : F →ₗ[ℝ] F) :
    (wishartLowerBlockMap A B D).det = A.det * D.det := by
  let e := Module.finBasis ℝ E
  let f := Module.finBasis ℝ F
  have hmatrix : LinearMap.toMatrix (e.prod f) (e.prod f) (wishartLowerBlockMap A B D) =
      Matrix.fromBlocks (LinearMap.toMatrix e e A) 0
        (LinearMap.toMatrix e f B) (LinearMap.toMatrix f f D) := by
    ext i j
    cases i <;> cases j <;>
      simp [LinearMap.toMatrix_apply, wishartLowerBlockMap, Module.Basis.prod_apply,
        Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr,
        Module.Basis.prod_apply_inl_fst, Module.Basis.prod_apply_inr_fst,
        Module.Basis.prod_apply_inl_snd, Module.Basis.prod_apply_inr_snd]
  rw [← LinearMap.det_toMatrix (e.prod f), hmatrix, Matrix.det_fromBlocks_zero₁₂,
    LinearMap.det_toMatrix, LinearMap.det_toMatrix]

end A3Research
