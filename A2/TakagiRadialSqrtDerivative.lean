import A2.MatrixProductSmooth
import A2.TakagiOrbit
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped BigOperators ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option backward.isDefEq.respectTransparency false

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

def takagiRadialSqrtMatrix {N : ℕ} (lambda : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (fun i => (Real.sqrt (lambda i) : ℂ))

def takagiRadialSqrtDerivative {N : ℕ} (lambda : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] Matrix (Fin N) (Fin N) ℂ :=
  ({ toFun := fun v => Matrix.diagonal (fun i => (v i / (2 * Real.sqrt (lambda i)) : ℂ))
     map_add' := by
       intro v w
       ext i j
       by_cases h : i = j <;> simp [Matrix.diagonal_apply, h, add_div]
     map_smul' := by
       intro a v
       ext i j
       by_cases h : i = j <;>
         simp [Matrix.diagonal_apply, h, Complex.real_smul, mul_div_assoc]
    } : (Fin N → ℝ) →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ).toContinuousLinearMap

@[simp] theorem takagiRadialSqrtDerivative_apply {N : ℕ}
    (lambda v : Fin N → ℝ) :
    takagiRadialSqrtDerivative lambda v =
      Matrix.diagonal (fun i => (v i / (2 * Real.sqrt (lambda i)) : ℂ)) := rfl

theorem contDiffAt_takagiRadialSqrtMatrix {N : ℕ} {k : ℕ∞ω}
    (lambda : Fin N → ℝ) (hpos : ∀ i, 0 < lambda i) :
    ContDiffAt ℝ k (@takagiRadialSqrtMatrix N) lambda := by
  refine contDiffAt_pi' fun i => contDiffAt_pi' fun j => ?_
  by_cases h : i = j
  · subst j
    simp only [takagiRadialSqrtMatrix, Matrix.diagonal_apply_eq]
    have hp : ContDiffAt ℝ k (fun mu : Fin N → ℝ => mu i) lambda :=
      (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp lambda
      (hp.sqrt (hpos i).ne')
  · simp only [takagiRadialSqrtMatrix, Matrix.diagonal_apply_ne _ h]
    exact contDiffAt_const

theorem hasFDerivAt_takagiRadialSqrtMatrix {N : ℕ}
    (lambda : Fin N → ℝ) (hpos : ∀ i, 0 < lambda i) :
    HasFDerivAt (@takagiRadialSqrtMatrix N) (takagiRadialSqrtDerivative lambda) lambda := by
  refine hasFDerivAt_pi'.mpr fun i => hasFDerivAt_pi'.mpr fun j => ?_
  by_cases h : i = j
  · subst j
    have hreal := (hasFDerivAt_apply (𝕜 := ℝ) i lambda).sqrt (hpos i).ne'
    have hc := Complex.ofRealCLM.hasFDerivAt.comp lambda hreal
    simp only [takagiRadialSqrtMatrix, Matrix.diagonal_apply_eq]
    convert! hc using 1
    ext v
    change (takagiRadialSqrtDerivative lambda v) i i =
      Complex.ofReal ((1 / (2 * Real.sqrt (lambda i))) * v i)
    rw [takagiRadialSqrtDerivative_apply, Matrix.diagonal_apply_eq]
    simp [div_eq_mul_inv, mul_comm]
  · simp only [takagiRadialSqrtMatrix, Matrix.diagonal_apply_ne _ h]
    convert! (hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) lambda) using 1
    ext v
    change (Matrix.diagonal (fun i => (v i / (2 * Real.sqrt (lambda i)) : ℂ))) i j = 0
    exact Matrix.diagonal_apply_ne _ h

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
