import A1.SymmetricCongruenceMeasure

open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder
open Matrix

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace A1Research

/-- The exact fixed-covariance Jacobian used by the literal transpose-Gram normalization. -/
theorem abs_det_symmetricRealCongruence_sqrt_transpose {m : ℕ}
    {T : Matrix (Fin m) (Fin m) ℂ} (hT : T.PosDef) :
    |LinearMap.det (symmetricRealCongruenceLinearMap (CFC.sqrt T).transpose)| =
      T.det.re ^ (m + 1) := by
  have hL : (CFC.sqrt T).PosDef := hT.isStrictlyPositive.sqrt.posDef
  rw [abs_det_symmetricRealCongruenceLinearMap_posDef hL.transpose, Matrix.det_transpose]
  have he := abs_det_symmetricRealCongruenceLinearMap_posDef_square hL
  rw [abs_det_symmetricRealCongruenceLinearMap_posDef hL,
    CFC.sqrt_mul_sqrt_self T hT.posSemidef.nonneg] at he
  exact he

end A1Research
