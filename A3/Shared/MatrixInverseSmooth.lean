import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Normed

/-! Smoothness of finite matrix algebra for the pointwise matrix norm.
These proofs expand determinants and adjugates into their finite polynomial
formulas, so no operator-norm instance or manifold-volume result is needed. -/

open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace A3Research

variable {𝕜 K E ι : Type*} [NontriviallyNormedField 𝕜] [NormedField K]
  [NormedAlgebra 𝕜 K] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [Fintype ι] [DecidableEq ι] {k : ℕ∞ω}

theorem contDiff_matrix_det {f : E → Matrix ι ι K} (hf : ContDiff 𝕜 k f) :
    ContDiff 𝕜 k (fun x => (f x).det) := by
  simp only [Matrix.det_apply']
  refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => contDiff_pi.mp (contDiff_pi.mp hf (σ i)) i

theorem contDiffAt_matrix_det {f : E → Matrix ι ι K} {x : E}
    (hf : ContDiffAt 𝕜 k f x) : ContDiffAt 𝕜 k (fun y => (f y).det) x := by
  simp only [Matrix.det_apply']
  refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul ?_
  exact contDiffAt_prod fun i _ => contDiffAt_pi.mp (contDiffAt_pi.mp hf (σ i)) i

theorem contDiff_matrix_adjugate {f : E → Matrix ι ι K} (hf : ContDiff 𝕜 k f) :
    ContDiff 𝕜 k (fun x => (f x).adjugate) := by
  refine contDiff_pi' fun i => contDiff_pi' fun j => ?_
  simp only [Matrix.adjugate_apply]
  apply contDiff_matrix_det
  refine contDiff_pi' fun r => contDiff_pi' fun c => ?_
  by_cases hr : r = j
  · simp only [Matrix.updateRow_apply, hr, if_true]
    exact contDiff_const
  · simp only [Matrix.updateRow_apply, hr, if_false]
    exact contDiff_pi.mp (contDiff_pi.mp hf r) c

theorem contDiffAt_matrix_adjugate {f : E → Matrix ι ι K} {x : E}
    (hf : ContDiffAt 𝕜 k f x) : ContDiffAt 𝕜 k (fun y => (f y).adjugate) x := by
  refine contDiffAt_pi' fun i => contDiffAt_pi' fun j => ?_
  simp only [Matrix.adjugate_apply]
  apply contDiffAt_matrix_det
  refine contDiffAt_pi' fun r => contDiffAt_pi' fun c => ?_
  by_cases hr : r = j
  · simp only [Matrix.updateRow_apply, hr, if_true]
    exact contDiffAt_const
  · simp only [Matrix.updateRow_apply, hr, if_false]
    exact contDiffAt_pi.mp (contDiffAt_pi.mp hf r) c

theorem contDiffAt_matrix_nonsing_inv {f : E → Matrix ι ι K} {x : E}
    (hf : ContDiffAt 𝕜 k f x) (hdet : (f x).det ≠ 0) :
    ContDiffAt 𝕜 k (fun y => (f y)⁻¹) x := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  exact ((contDiffAt_matrix_det hf).inv hdet).smul (contDiffAt_matrix_adjugate hf)

theorem contDiffOn_matrix_nonsing_inv {f : E → Matrix ι ι K} {s : Set E}
    (hf : ContDiff 𝕜 k f) (hdet : ∀ x ∈ s, (f x).det ≠ 0) :
    ContDiffOn 𝕜 k (fun y => (f y)⁻¹) s :=
  fun x hx => (contDiffAt_matrix_nonsing_inv hf.contDiffAt (hdet x hx)).contDiffWithinAt

end A3Research
