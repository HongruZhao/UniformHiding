import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COELikelihoodAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFlowGeometry
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Internal fourth Bell identity for the literal centered likelihood

The fourth density-score identity is ordinary one-variable calculus once the
literal determinant likelihood is known to be positive near the origin.  This
file proves that calculus in the kernel.  In particular, it replaces the old
pointwise external interface by:

* smoothness of the finite matrix-determinant path;
* local smoothness of its real power on the positive COE support; and
* the fourth-order Faà di Bruno identity for `exp ∘ log`.

There is no probability, integration, or score estimate in this module.
-/

open Function
open scoped Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

@[fun_prop]
private theorem contDiff_complex_star_real_domain {f : ℝ → ℂ}
    (hf : ContDiff ℝ ⊤ f) : ContDiff ℝ ⊤ (fun x ↦ star (f x)) := by
  convert Complex.conjCLE.contDiff.comp hf using 1
  funext x
  simp only [Function.comp_apply, Complex.conjCLE_apply, Complex.star_def]

@[fun_prop]
private theorem contDiff_complex_ofReal_real_domain {f : ℝ → ℝ}
    (hf : ContDiff ℝ ⊤ f) : ContDiff ℝ ⊤ (fun x ↦ (f x : ℂ)) := by
  convert Complex.ofRealCLM.contDiff.comp hf using 1
  funext x
  simp only [Function.comp_apply, Complex.ofRealCLM_apply]

/-- In one real variable, the scalar iterated derivative inherits the usual
loss of differentiability from the iterated Fréchet derivative. -/
private theorem contDiffAt_iteratedDeriv_right_real {f : ℝ → ℝ}
    {n : WithTop ℕ∞} {m i : ℕ} {x : ℝ} (hf : ContDiffAt ℝ n f x)
    (hmi : m + i ≤ n) : ContDiffAt ℝ m (iteratedDeriv i f) x := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin i) ℝ).symm.contDiff.contDiffAt.comp x
    (hf.iteratedFDeriv_right hmi)

/-- Fourth-order scalar Faà di Bruno, specialized to the exponential and
written as the density Bell polynomial used by the score development. -/
private theorem iteratedDeriv_four_exp_comp_at (g : ℝ → ℝ) {x : ℝ}
    (hg : ContDiffAt ℝ 4 g x) :
    iteratedDeriv 4 (Real.exp ∘ g) x =
      Real.exp (g x) * densityBellFour
        (iteratedDeriv 1 g x) (iteratedDeriv 2 g x)
        (iteratedDeriv 3 g x) (iteratedDeriv 4 g x) := by
  have h3 : iteratedDeriv 3 (Real.exp ∘ g) =ᶠ[𝓝 x] fun y ↦
      Real.exp (g y) * deriv g y ^ 3 +
      3 * Real.exp (g y) * iteratedDeriv 2 g y * deriv g y +
      Real.exp (g y) * iteratedDeriv 3 g y := by
    filter_upwards [hg.eventually (by norm_num)] with y hy
    rw [iteratedDeriv_comp_three Real.contDiff_exp.contDiffAt
      (hy.of_le (by norm_num))]
    simp only [iteratedDeriv_eq_iterate, Real.iter_deriv_exp,
      Real.deriv_exp]
  rw [show 4 = 3 + 1 by norm_num, iteratedDeriv_succ, h3.deriv_eq]
  have hg0 : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hg1 : DifferentiableAt ℝ (iteratedDeriv 1 g) x :=
    (contDiffAt_iteratedDeriv_right_real hg (m := 1) (i := 1)
      (by norm_num)).differentiableAt (by norm_num)
  have hg2 : DifferentiableAt ℝ (iteratedDeriv 2 g) x :=
    (contDiffAt_iteratedDeriv_right_real hg (m := 1) (i := 2)
      (by norm_num)).differentiableAt (by norm_num)
  have hg3 : DifferentiableAt ℝ (iteratedDeriv 3 g) x :=
    (contDiffAt_iteratedDeriv_right_real hg (m := 1) (i := 3)
      (by norm_num)).differentiableAt (by norm_num)
  have he : HasDerivAt (fun y ↦ Real.exp (g y))
      (Real.exp (g x) * deriv g x) x := hg0.hasDerivAt.exp
  have hd1 : HasDerivAt (deriv g) (deriv (deriv g) x) x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hg1.hasDerivAt
  have hd2 : HasDerivAt (deriv (deriv g))
      (deriv (deriv (deriv g)) x) x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hg2.hasDerivAt
  have hd3 : HasDerivAt (deriv (deriv (deriv g)))
      (deriv (deriv (deriv (deriv g))) x) x := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hg3.hasDerivAt
  have hcalc := ((he.mul (hd1.pow 3)).add
      (((he.const_mul 3).mul hd2).mul hd1)).add (he.mul hd3)
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hfun :
      (fun y ↦ Real.exp (g y) * deriv g y ^ 3 +
        3 * Real.exp (g y) * deriv (deriv g) y * deriv g y +
        Real.exp (g y) * deriv (deriv (deriv g)) y) =
      ((fun y ↦ Real.exp (g y)) * deriv g ^ 3 +
        (fun y ↦ 3 * Real.exp (g y)) * deriv (deriv g) * deriv g +
        (fun y ↦ Real.exp (g y)) * deriv (deriv (deriv g))) := by
    funext y
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
  rw [hfun, hcalc.deriv]
  simp only [Pi.mul_apply, Pi.pow_apply, densityBellFour]
  norm_num
  ring

/-- The literal determinant likelihood is `C⁴` at the origin on the open
COE support. -/
theorem concreteCenteredLikelihoodCore_contDiffAt_four
    {N K : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    ContDiffAt ℝ 4 (fun t ↦ concreteCenteredLikelihoodCore K v t A) 0 := by
  have hbase : 0 < concreteCOEBaseDeterminant K A :=
    (RCLike.lt_iff_re_im.mp hsupport.det_pos).1
  have hdet : ContDiff ℝ ⊤
      (fun t ↦ concreteCOECenteredInverseDeterminant K v t A) := by
    simp only [concreteCOECenteredInverseDeterminant]
    simp_rw [transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate hN]
    simp only [concreteOrbitalMatrixUpdate, concreteOrbitalFactor,
      Matrix.det_apply, Matrix.sub_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
    apply Complex.reCLM.contDiff.comp
    fun_prop
  have hratio : ContDiffAt ℝ 4
      (fun t ↦ concreteCOECenteredInverseDeterminant K v t A /
        concreteCOEBaseDeterminant K A) 0 :=
    (hdet.of_le (by norm_num)).contDiffAt.div_const _
  have hratio_zero :
      concreteCOECenteredInverseDeterminant K v 0 A /
        concreteCOEBaseDeterminant K A = 1 := by
    have heq : concreteCOECenteredInverseDeterminant K v 0 A =
        concreteCOEBaseDeterminant K A := by
      simp [concreteCOECenteredInverseDeterminant,
        concreteCOEBaseDeterminant, transposeCongruenceFlow,
        transposeCongruence]
    rw [heq, div_self hbase.ne']
  have hrpow : ContDiffAt ℝ 4
      (fun t ↦ Real.rpow
        (concreteCOECenteredInverseDeterminant K v t A /
          concreteCOEBaseDeterminant K A)
        (coeCornerDensityExponent N K)) 0 :=
    hratio.rpow_const_of_ne (by simp [hratio_zero])
  unfold concreteCenteredLikelihoodCore
  simpa only [if_neg hbase.ne'] using hrpow

/-- The literal likelihood is normalized to one at the origin on support. -/
theorem concreteCenteredLikelihoodCore_zero_on_support
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredLikelihoodCore K v 0 A = 1 := by
  have hbase : concreteCOEBaseDeterminant K A ≠ 0 :=
    ((RCLike.lt_iff_re_im.mp hsupport.det_pos).1).ne'
  unfold concreteCenteredLikelihoodCore
  rw [if_neg hbase]
  have heq : concreteCOECenteredInverseDeterminant K v 0 A =
      concreteCOEBaseDeterminant K A := by
    simp [concreteCOECenteredInverseDeterminant,
      concreteCOEBaseDeterminant, transposeCongruenceFlow,
      transposeCongruence]
  rw [heq, div_self hbase]
  exact Real.one_rpow _

/-- Kernel proof of the formerly external pointwise Bell-four identity. -/
theorem coeCorner_centeredDensityScore_four_eq_Bell_external_derived
    {N K : ℕ} (hN : 1 ≤ N) (_hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (_hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredDensityScore 4 N K v A =
      densityBellFour
        (concreteCenteredLogScore 1 N K v A)
        (concreteCenteredLogScore 2 N K v A)
        (concreteCenteredLogScore 3 N K v A)
        (concreteCenteredLogScore 4 N K v A) := by
  let f : ℝ → ℝ := fun t ↦ concreteCenteredLikelihoodCore K v t A
  let g : ℝ → ℝ := fun t ↦ Real.log (f t)
  have hf : ContDiffAt ℝ 4 f 0 :=
    concreteCenteredLikelihoodCore_contDiffAt_four hN v A hsupport
  have hf0 : f 0 = 1 :=
    concreteCenteredLikelihoodCore_zero_on_support v A hsupport
  have hg : ContDiffAt ℝ 4 g 0 := hf.log (by simp [hf0])
  have hpos : ∀ᶠ t in 𝓝 0, 0 < f t :=
    continuousAt_const.eventually_lt hf.continuousAt (by simp [hf0])
  have hfg : f =ᶠ[𝓝 0] Real.exp ∘ g := by
    filter_upwards [hpos] with t ht
    simp only [Function.comp_apply, g]
    exact (Real.exp_log ht).symm
  have hbell := iteratedDeriv_four_exp_comp_at g hg
  rw [← hfg.iteratedDeriv_eq 4] at hbell
  simp only [g, hf0, Real.log_one, Real.exp_zero] at hbell
  simpa [concreteCenteredDensityScore, concreteCenteredLogScore, f, g] using hbell

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
