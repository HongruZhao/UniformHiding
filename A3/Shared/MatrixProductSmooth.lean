import A3.Shared.MatrixInverseSmooth
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! Finite matrix products in the coordinate norms used by the charts. -/

open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

section Smooth

variable {𝕜 K E ι κ ν : Type*} [NontriviallyNormedField 𝕜] [NormedField K]
  [NormedAlgebra 𝕜 K] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Fintype ι] [Fintype κ] [Fintype ν] {k : ℕ∞ω}

theorem contDiff_matrix_mul {f : E → Matrix ι κ K} {g : E → Matrix κ ν K}
    (hf : ContDiff 𝕜 k f) (hg : ContDiff 𝕜 k g) :
    ContDiff 𝕜 k (fun x => f x * g x) := by
  refine contDiff_pi' fun i => contDiff_pi' fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun l _ =>
    (contDiff_pi.mp (contDiff_pi.mp hf i) l).mul
      (contDiff_pi.mp (contDiff_pi.mp hg l) j)

theorem contDiffAt_matrix_mul {f : E → Matrix ι κ K} {g : E → Matrix κ ν K} {x : E}
    (hf : ContDiffAt 𝕜 k f x) (hg : ContDiffAt 𝕜 k g x) :
    ContDiffAt 𝕜 k (fun y => f y * g y) x := by
  refine contDiffAt_pi' fun i => contDiffAt_pi' fun j => ?_
  simp only [Matrix.mul_apply]
  exact ContDiffAt.sum fun l _ =>
    (contDiffAt_pi.mp (contDiffAt_pi.mp hf i) l).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp hg l) j)

end Smooth

section Derivative

variable {E ι κ ν : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [Fintype κ] [Fintype ν]

def matrixMulDerivative (A : Matrix ι κ ℂ) (B : Matrix κ ν ℂ)
    (f' : E →L[ℝ] Matrix ι κ ℂ) (g' : E →L[ℝ] Matrix κ ν ℂ) :
    E →L[ℝ] Matrix ι ν ℂ :=
  (mulRightLinearMap ι ℝ B).toContinuousLinearMap.comp f' +
    (mulLeftLinearMap ν ℝ A).toContinuousLinearMap.comp g'

@[simp] theorem matrixMulDerivative_apply (A : Matrix ι κ ℂ) (B : Matrix κ ν ℂ)
    (f' : E →L[ℝ] Matrix ι κ ℂ) (g' : E →L[ℝ] Matrix κ ν ℂ) (v : E) :
    matrixMulDerivative A B f' g' v = f' v * B + A * g' v := rfl

theorem hasFDerivAt_matrix_mul {f : E → Matrix ι κ ℂ} {g : E → Matrix κ ν ℂ}
    {f' : E →L[ℝ] Matrix ι κ ℂ} {g' : E →L[ℝ] Matrix κ ν ℂ} {x : E}
    (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' x) :
    HasFDerivAt (fun y => f y * g y) (matrixMulDerivative (f x) (g x) f' g') x := by
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
