import A3.Shared.MatrixProductSmooth
import Mathlib.Analysis.RCLike.Basic

open scoped BigOperators ContDiff Matrix.Norms.Elementwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research
variable {K : Type*} [RCLike K]

section Derivative

variable {E ι κ ν : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [Fintype κ] [Fintype ν]

def matrixMulDerivativeRCLike (A : Matrix ι κ K) (B : Matrix κ ν K)
    (f' : E →L[ℝ] Matrix ι κ K) (g' : E →L[ℝ] Matrix κ ν K) :
    E →L[ℝ] Matrix ι ν K :=
  (mulRightLinearMap ι ℝ B).toContinuousLinearMap.comp f' +
    (mulLeftLinearMap ν ℝ A).toContinuousLinearMap.comp g'

@[simp] theorem matrixMulDerivativeRCLike_apply (A : Matrix ι κ K) (B : Matrix κ ν K)
    (f' : E →L[ℝ] Matrix ι κ K) (g' : E →L[ℝ] Matrix κ ν K) (v : E) :
    matrixMulDerivativeRCLike A B f' g' v = f' v * B + A * g' v := rfl

theorem hasFDerivAt_matrix_mul_rclike {f : E → Matrix ι κ K} {g : E → Matrix κ ν K}
    {f' : E →L[ℝ] Matrix ι κ K} {g' : E →L[ℝ] Matrix κ ν K} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => f y * g y) (matrixMulDerivativeRCLike (f x) (g x) f' g') x := by
  refine hasFDerivAt_pi'.mpr fun i => hasFDerivAt_pi'.mpr fun j => ?_
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    (hasFDerivAt_pi'.mp (hasFDerivAt_pi'.mp hf i) l).mul
      (hasFDerivAt_pi'.mp (hasFDerivAt_pi'.mp hg l) j))
  change HasFDerivAt (fun y => ∑ l, f y i l * g y l j) _ x
  convert! hsum using 1
  ext v
  change (f' v * g x + f x * g' v) i j = _
  simp [Matrix.mul_apply, Finset.sum_add_distrib, mul_comm, add_comm,
    add_left_comm, add_assoc]
  rfl

end Derivative


end A3Research
