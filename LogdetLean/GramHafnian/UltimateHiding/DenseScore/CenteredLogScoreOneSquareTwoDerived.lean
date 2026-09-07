import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCenteredLogScoreMomentExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_ExactMomentEndpointA4
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCorrelatedPath
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MatrixInverseMeasurability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFlowGeometry
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-!
# The mixed first/second centered log-score moment from pure moments

This module removes the mixed-moment input
`centeredLogScore_oneSquareTwo_momentPackage_external` from the dependency
closure of its consumers.  The proof has two parts.

First, the literal centered log likelihood is jointly measurable.  Its first
and second parameter derivatives are represented by measurable limits of
finite-difference quotients; the literal path is `C^2` at zero, so these
limits agree with `concreteCenteredEll 1` and `concreteCenteredEll 2`.

Second, the pointwise Young inequality

`|ellOne^2 * ellTwo| <= (ellOne^4 + ellTwo^2) / 2`

derives both `L^1` membership and the same sharp `O(N^2)` norm budget from
the two retained pure-moment packages.
-/

open MeasureTheory Filter Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

set_option maxHeartbeats 1000000

section DerivativeSurrogates

variable {X : Type*} [MeasurableSpace X]

/-- A total measurable forward-difference representative of the derivative.
At differentiability points it agrees with `deriv`. -/
private def derivApprox (F : X × ℝ → ℝ) (p : X × ℝ) : ℝ :=
  limUnder atTop (fun n : ℕ =>
    let h : ℝ := 1 / ((n : ℝ) + 1)
    h⁻¹ * (F (p.1, p.2 + h) - F p))

private theorem measurable_derivApprox {F : X × ℝ → ℝ}
    (hF : Measurable F) : Measurable (derivApprox F) := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  dsimp only
  fun_prop

private theorem derivApprox_eq_deriv {F : X × ℝ → ℝ} (p : X × ℝ)
    (hF : DifferentiableAt ℝ (fun t => F (p.1, t)) p.2) :
    derivApprox F p = deriv (fun t => F (p.1, t)) p.2 := by
  apply Tendsto.limUnder_eq
  have hs := hF.hasDerivAt.tendsto_slope_zero
  apply hs.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · filter_upwards with n
    exact ne_of_gt (by positivity)

private theorem derivApprox_eq_iteratedDeriv_one {F : X × ℝ → ℝ}
    (p : X × ℝ)
    (hF : DifferentiableAt ℝ (fun t => F (p.1, t)) p.2) :
    derivApprox F p =
      iteratedDeriv 1 (fun t => F (p.1, t)) p.2 := by
  rw [derivApprox_eq_deriv p hF, iteratedDeriv_eq_iterate]
  rfl

private def derivApproxTwo (F : X × ℝ → ℝ) : X × ℝ → ℝ :=
  derivApprox (derivApprox F)

private theorem measurable_derivApproxTwo {F : X × ℝ → ℝ}
    (hF : Measurable F) : Measurable (derivApproxTwo F) :=
  measurable_derivApprox (measurable_derivApprox hF)

private theorem derivApproxTwo_eq_iteratedDeriv_two {F : X × ℝ → ℝ}
    (p : X × ℝ)
    (hF : ContDiffAt ℝ 2 (fun t => F (p.1, t)) p.2) :
    derivApproxTwo F p =
      iteratedDeriv 2 (fun t => F (p.1, t)) p.2 := by
  let f : ℝ → ℝ := fun t => F (p.1, t)
  have hdiffEventually :
      ∀ᶠ t in 𝓝 p.2, DifferentiableAt ℝ f t := by
    filter_upwards [hF.eventually (by norm_num)] with t ht
    exact ht.differentiableAt (by norm_num)
  have heq : (fun t => derivApprox F (p.1, t)) =ᶠ[𝓝 p.2]
      deriv f := by
    filter_upwards [hdiffEventually] with t ht
    exact derivApprox_eq_deriv (p.1, t) ht
  have hderivDiff : DifferentiableAt ℝ (deriv f) p.2 := by
    have hcd : ContDiffAt ℝ 1 (deriv f) p.2 :=
      hF.derivWithin (m := 1) (by norm_num)
    exact hcd.differentiableAt (by norm_num)
  have happDiff : DifferentiableAt ℝ
      (fun t => derivApprox F (p.1, t)) p.2 :=
    heq.differentiableAt_iff.mpr hderivDiff
  rw [derivApproxTwo, derivApprox_eq_deriv p happDiff]
  rw [heq.deriv_eq]
  rw [iteratedDeriv_eq_iterate]
  rfl

/-- Third measurable finite-difference surrogate. -/
private def derivApproxThree (F : X × ℝ → ℝ) : X × ℝ → ℝ :=
  derivApprox (derivApproxTwo F)

private theorem measurable_derivApproxThree {F : X × ℝ → ℝ}
    (hF : Measurable F) : Measurable (derivApproxThree F) :=
  measurable_derivApprox (measurable_derivApproxTwo hF)

/-- Fourth measurable finite-difference surrogate. -/
private def derivApproxFour (F : X × ℝ → ℝ) : X × ℝ → ℝ :=
  derivApprox (derivApproxThree F)

private theorem measurable_derivApproxFour {F : X × ℝ → ℝ}
    (hF : Measurable F) : Measurable (derivApproxFour F) :=
  measurable_derivApprox (measurable_derivApproxThree hF)

/-- In one real variable, an iterated scalar derivative inherits the usual
loss of differentiability from the iterated Frechet derivative. -/
private theorem contDiffAt_iteratedDeriv_right_real {f : ℝ → ℝ}
    {n : WithTop ℕ∞} {m i : ℕ} {x : ℝ} (hf : ContDiffAt ℝ n f x)
    (hmi : m + i ≤ n) : ContDiffAt ℝ m (iteratedDeriv i f) x := by
  rw [iteratedDeriv_eq_equiv_comp]
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin i) ℝ).symm.contDiff.contDiffAt.comp x
    (hf.iteratedFDeriv_right hmi)

private theorem derivApproxThree_eq_iteratedDeriv_three
    {F : X × ℝ → ℝ} (p : X × ℝ)
    (hF : ContDiffAt ℝ 3 (fun t => F (p.1, t)) p.2) :
    derivApproxThree F p =
      iteratedDeriv 3 (fun t => F (p.1, t)) p.2 := by
  let f : ℝ → ℝ := fun t => F (p.1, t)
  have hsmoothEventually :
      ∀ᶠ t in 𝓝 p.2, ContDiffAt ℝ 2 f t :=
    by
      filter_upwards [hF.eventually (by norm_num)] with t ht
      exact ht.of_le (by norm_num)
  have heq : (fun t => derivApproxTwo F (p.1, t)) =ᶠ[𝓝 p.2]
      iteratedDeriv 2 f := by
    filter_upwards [hsmoothEventually] with t ht
    exact derivApproxTwo_eq_iteratedDeriv_two (p.1, t) ht
  have htargetDiff : DifferentiableAt ℝ (iteratedDeriv 2 f) p.2 :=
    (contDiffAt_iteratedDeriv_right_real hF (m := 1) (i := 2)
      (by norm_num)).differentiableAt (by norm_num)
  have happDiff : DifferentiableAt ℝ
      (fun t => derivApproxTwo F (p.1, t)) p.2 :=
    heq.differentiableAt_iff.mpr htargetDiff
  rw [derivApproxThree, derivApprox_eq_deriv p happDiff]
  rw [heq.deriv_eq]
  change deriv (iteratedDeriv 2 f) p.2 = iteratedDeriv 3 f p.2
  exact congrFun (iteratedDeriv_succ (n := 2) (f := f)).symm p.2

private theorem derivApproxFour_eq_iteratedDeriv_four
    {F : X × ℝ → ℝ} (p : X × ℝ)
    (hF : ContDiffAt ℝ 4 (fun t => F (p.1, t)) p.2) :
    derivApproxFour F p =
      iteratedDeriv 4 (fun t => F (p.1, t)) p.2 := by
  let f : ℝ → ℝ := fun t => F (p.1, t)
  have hsmoothEventually :
      ∀ᶠ t in 𝓝 p.2, ContDiffAt ℝ 3 f t :=
    by
      filter_upwards [hF.eventually (by norm_num)] with t ht
      exact ht.of_le (by norm_num)
  have heq : (fun t => derivApproxThree F (p.1, t)) =ᶠ[𝓝 p.2]
      iteratedDeriv 3 f := by
    filter_upwards [hsmoothEventually] with t ht
    exact derivApproxThree_eq_iteratedDeriv_three (p.1, t) ht
  have htargetDiff : DifferentiableAt ℝ (iteratedDeriv 3 f) p.2 :=
    (contDiffAt_iteratedDeriv_right_real hF (m := 1) (i := 3)
      (by norm_num)).differentiableAt (by norm_num)
  have happDiff : DifferentiableAt ℝ
      (fun t => derivApproxThree F (p.1, t)) p.2 :=
    heq.differentiableAt_iff.mpr htargetDiff
  rw [derivApproxFour, derivApprox_eq_deriv p happDiff]
  rw [heq.deriv_eq]
  change deriv (iteratedDeriv 3 f) p.2 = iteratedDeriv 4 f p.2
  exact congrFun (iteratedDeriv_succ (n := 3) (f := f)).symm p.2

end DerivativeSurrogates

/-! ## Joint measurability and local smoothness of the literal likelihood -/

private def centeredLogLikelihoodJoint (N K : ℕ) :
    ((ConcreteMatrixState N × ComplexUnitSphere N) × ℝ) → ℝ :=
  fun p => Real.log (concreteCenteredLikelihoodCore K p.1.2 p.2 p.1.1)

/-- A definitionally measurable closed form, equal to the literal likelihood
through the centered-flow geometry theorem. -/
private def centeredLogLikelihoodJointMeasurableVersion (N K : ℕ) :
    ((ConcreteMatrixState N × ComplexUnitSphere N) × ℝ) → ℝ := by
  classical
  exact fun p =>
    let C := unscaleCOECorner K p.1.1
    let Ct := concreteOrbitalMatrixUpdate N (-p.2) p.1.2 C
    let base := (Matrix.det (1 - C.conjTranspose * C)).re
    let moved := (Matrix.det (1 - Ct.conjTranspose * Ct)).re
    Real.log (if base = 0 then 1 else
      Real.rpow (moved / base) (coeCornerDensityExponent N K))

private theorem centeredLogLikelihoodJoint_eq_version
    {N K : ℕ} (hN : 1 ≤ N) :
    centeredLogLikelihoodJoint N K =
      centeredLogLikelihoodJointMeasurableVersion N K := by
  funext p
  simp only [centeredLogLikelihoodJoint,
    centeredLogLikelihoodJointMeasurableVersion,
    concreteCenteredLikelihoodCore,
    concreteCOEBaseDeterminant,
    concreteCOECenteredInverseDeterminant]
  rw [transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate hN]
  rfl

private theorem measurable_matrix_conjTranspose
    {X : Type*} [MeasurableSpace X] {N : ℕ}
    {A : X → Matrix (Fin N) (Fin N) ℂ} (hA : Measurable A) :
    Measurable (fun x => (A x).conjTranspose) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.conjTranspose_apply]
  fun_prop

private theorem measurable_matrix_det_comp
    {X : Type*} [MeasurableSpace X] {N : ℕ}
    {A : X → Matrix (Fin N) (Fin N) ℂ} (hA : Measurable A) :
    Measurable (fun x => Matrix.det (A x)) := by
  simp only [Matrix.det_apply']
  fun_prop

private theorem measurable_matrix_sub
    {X : Type*} [MeasurableSpace X] {N : ℕ}
    {A B : X → Matrix (Fin N) (Fin N) ℂ}
    (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun x => A x - B x) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  simp only [Matrix.sub_apply]
  fun_prop

private theorem measurable_real_rpow_const (a : ℝ) :
    Measurable (fun x : ℝ => Real.rpow x a) := by
  by_cases ha : a = 0
  · subst a
    have hfun : (fun x : ℝ => Real.rpow x 0) = fun _ => (1 : ℝ) := by
      funext x
      rw [Real.rpow_eq_pow, Real.rpow_zero]
    rw [hfun]
    exact measurable_const
  · have hfun : (fun x : ℝ => Real.rpow x a) = fun x =>
        if 0 ≤ x then
          if x = 0 then 0 else Real.exp (Real.log x * a)
        else Real.exp (Real.log x * a) * Real.cos (a * Real.pi) := by
      funext x
      by_cases hx : 0 ≤ x
      · rw [if_pos hx, Real.rpow_eq_pow,
          Real.rpow_def_of_nonneg hx, if_neg ha]
      · rw [if_neg hx, Real.rpow_eq_pow,
          Real.rpow_def_of_neg (lt_of_not_ge hx)]
    rw [hfun]
    exact Measurable.ite (measurableSet_le measurable_const measurable_id)
      (Measurable.ite (measurableSet_eq_fun measurable_id measurable_const)
        measurable_const (by fun_prop)) (by fun_prop)

private theorem measurable_centeredLogLikelihoodJointMeasurableVersion
    (N K : ℕ) :
    Measurable (centeredLogLikelihoodJointMeasurableVersion N K) := by
  unfold centeredLogLikelihoodJointMeasurableVersion
  have hupdate : Measurable fun p :
      (ConcreteMatrixState N × ComplexUnitSphere N) × ℝ =>
      concreteOrbitalMatrixUpdate N (-p.2) p.1.2
        (unscaleCOECorner K p.1.1) := by
    have hA : Measurable fun p :
        (ConcreteMatrixState N × ComplexUnitSphere N) × ℝ =>
        unscaleCOECorner K p.1.1 :=
      (measurable_unscaleCOECorner N K).comp
        (measurable_fst.comp measurable_fst)
    have hfactor : Measurable fun p :
        (ConcreteMatrixState N × ComplexUnitSphere N) × ℝ =>
        concreteOrbitalFactor N (-p.2) p.1.2 := by
      refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
      simp only [concreteOrbitalFactor, Matrix.smul_apply, Matrix.add_apply,
        Matrix.one_apply, complexRankOneProjection]
      fun_prop
    have hleft := measurable_complexMatrix_mul hfactor hA
    have hright := measurable_complexMatrix_transpose hfactor
    exact measurable_complexMatrix_mul hleft hright
  have hC : Measurable fun p :
      (ConcreteMatrixState N × ComplexUnitSphere N) × ℝ =>
      unscaleCOECorner K p.1.1 :=
    (measurable_unscaleCOECorner N K).comp
      (measurable_fst.comp measurable_fst)
  have hbase : Measurable fun p :
      (ConcreteMatrixState N × ComplexUnitSphere N) × ℝ =>
      (Matrix.det (1 - (unscaleCOECorner K p.1.1).conjTranspose *
        unscaleCOECorner K p.1.1)).re := by
    have hCstar := measurable_matrix_conjTranspose hC
    have hprod := measurable_complexMatrix_mul hCstar hC
    have hmat : Measurable fun p :
        (ConcreteMatrixState N × ComplexUnitSphere N) × ℝ =>
        (1 : ConcreteMatrixState N) -
          (unscaleCOECorner K p.1.1).conjTranspose *
            unscaleCOECorner K p.1.1 :=
      measurable_matrix_sub measurable_const hprod
    exact Complex.measurable_re.comp (measurable_matrix_det_comp hmat)
  have hmoved : Measurable fun p :
      (ConcreteMatrixState N × ComplexUnitSphere N) × ℝ =>
      (Matrix.det (1 -
        (concreteOrbitalMatrixUpdate N (-p.2) p.1.2
          (unscaleCOECorner K p.1.1)).conjTranspose *
        concreteOrbitalMatrixUpdate N (-p.2) p.1.2
          (unscaleCOECorner K p.1.1))).re := by
    have hstar := measurable_matrix_conjTranspose hupdate
    have hprod := measurable_complexMatrix_mul hstar hupdate
    have hmat : Measurable fun p :
        (ConcreteMatrixState N × ComplexUnitSphere N) × ℝ =>
        (1 : ConcreteMatrixState N) -
          (concreteOrbitalMatrixUpdate N (-p.2) p.1.2
            (unscaleCOECorner K p.1.1)).conjTranspose *
          concreteOrbitalMatrixUpdate N (-p.2) p.1.2
            (unscaleCOECorner K p.1.1) :=
      measurable_matrix_sub measurable_const hprod
    exact Complex.measurable_re.comp (measurable_matrix_det_comp hmat)
  have hratio : Measurable fun p :
      (ConcreteMatrixState N × ComplexUnitSphere N) × ℝ =>
      ((Matrix.det (1 -
          (concreteOrbitalMatrixUpdate N (-p.2) p.1.2
            (unscaleCOECorner K p.1.1)).conjTranspose *
          concreteOrbitalMatrixUpdate N (-p.2) p.1.2
            (unscaleCOECorner K p.1.1))).re /
        (Matrix.det (1 - (unscaleCOECorner K p.1.1).conjTranspose *
          unscaleCOECorner K p.1.1)).re) := hmoved.div hbase
  have hrpow : Measurable fun p :
      (ConcreteMatrixState N × ComplexUnitSphere N) × ℝ =>
      Real.rpow
        ((Matrix.det (1 -
          (concreteOrbitalMatrixUpdate N (-p.2) p.1.2
            (unscaleCOECorner K p.1.1)).conjTranspose *
          concreteOrbitalMatrixUpdate N (-p.2) p.1.2
            (unscaleCOECorner K p.1.1))).re /
        (Matrix.det (1 - (unscaleCOECorner K p.1.1).conjTranspose *
          unscaleCOECorner K p.1.1)).re)
        (coeCornerDensityExponent N K) :=
    (measurable_real_rpow_const (coeCornerDensityExponent N K)).comp hratio
  exact Real.measurable_log.comp <| Measurable.ite
    (measurableSet_eq_fun hbase measurable_const)
    measurable_const hrpow

private theorem measurable_centeredLogLikelihoodJoint
    {N K : ℕ} (hN : 1 ≤ N) :
    Measurable (centeredLogLikelihoodJoint N K) := by
  rw [centeredLogLikelihoodJoint_eq_version hN]
  exact measurable_centeredLogLikelihoodJointMeasurableVersion N K

@[fun_prop]
private theorem contDiffAt_complex_star
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun y => star (f y)) x := by
  have heq : (fun y => star (f y)) = Complex.conjCLE ∘ f := by
    funext y
    rw [Function.comp_apply, Complex.conjCLE_apply]
    exact congrFun Complex.star_def (f y)
  rw [heq]
  exact Complex.conjCLE.contDiff.contDiffAt.comp x hf

@[fun_prop]
private theorem contDiffAt_complex_ofReal
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} {n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun y => (f y : ℂ)) x := by
  have heq : (fun y => (f y : ℂ)) = Complex.ofRealCLM ∘ f := by
    funext y
    simp only [Function.comp_apply, Complex.ofRealCLM_apply]
  rw [heq]
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp x hf

private theorem centeredLogLikelihoodJoint_contDiffAt_two
    {N K : ℕ} (hN : 1 ≤ N)
    (p : ConcreteMatrixState N × ComplexUnitSphere N) :
    ContDiffAt ℝ 2 (fun t => centeredLogLikelihoodJoint N K (p, t)) 0 := by
  rw [centeredLogLikelihoodJoint_eq_version hN]
  simp only [centeredLogLikelihoodJointMeasurableVersion]
  split_ifs with hbase
  · fun_prop
  · let C := unscaleCOECorner K p.1
    let a := coeCornerDensityExponent N K
    let ratio : ℝ → ℝ := fun t =>
      (Matrix.det (1 -
        (concreteOrbitalMatrixUpdate N (-t) p.2 C).conjTranspose *
          concreteOrbitalMatrixUpdate N (-t) p.2 C)).re /
        (Matrix.det (1 - C.conjTranspose * C)).re
    change ContDiffAt ℝ 2
      (fun t => Real.log (Real.rpow (ratio t) a)) 0
    have hratio0 : ratio 0 = 1 := by
      simp [ratio, C, concreteOrbitalMatrixUpdate, concreteOrbitalFactor,
        hbase]
    have hratioCD : ContDiffAt ℝ 2 ratio 0 := by
      dsimp only [ratio, C]
      have hmovedComplex : ContDiffAt ℝ 2 (fun t : ℝ =>
          Matrix.det (1 -
            (concreteOrbitalMatrixUpdate N (-t) p.2
              (unscaleCOECorner K p.1)).conjTranspose *
            concreteOrbitalMatrixUpdate N (-t) p.2
              (unscaleCOECorner K p.1))) 0 := by
        simp only [Matrix.det_apply', Matrix.sub_apply, Matrix.one_apply,
          Matrix.mul_apply, Matrix.conjTranspose_apply,
          concreteOrbitalMatrixUpdate, concreteOrbitalFactor,
          complexRankOneProjection, Matrix.transpose_apply,
          Matrix.smul_apply, Matrix.add_apply]
        fun_prop
      have hmovedReal : ContDiffAt ℝ 2 (fun t : ℝ =>
          (Matrix.det (1 -
            (concreteOrbitalMatrixUpdate N (-t) p.2
              (unscaleCOECorner K p.1)).conjTranspose *
            concreteOrbitalMatrixUpdate N (-t) p.2
              (unscaleCOECorner K p.1))).re) 0 := by
        exact (Complex.reCLM.contDiff.contDiffAt).comp 0 hmovedComplex
      exact hmovedReal.div_const
        ((Matrix.det (1 -
          (unscaleCOECorner K p.1).conjTranspose *
            unscaleCOECorner K p.1)).re)
    have hpos : ∀ᶠ t in 𝓝 0, 0 < ratio t := by
      have hzero : 0 < ratio 0 := by rw [hratio0]; norm_num
      exact hratioCD.continuousAt.eventually (lt_mem_nhds hzero)
    have heq :
        (fun t => Real.log (Real.rpow (ratio t) a)) =ᶠ[𝓝 0]
          (fun t => Real.log (ratio t) * a) := by
      filter_upwards [hpos] with t ht
      rw [Real.rpow_eq_pow, Real.rpow_def_of_pos ht, Real.log_exp]
    have hlog : ContDiffAt ℝ 2 (fun t => Real.log (ratio t)) 0 :=
      hratioCD.log (by rw [hratio0]; norm_num)
    exact (hlog.mul contDiffAt_const).congr_of_eventuallyEq heq

/-- The same totalized likelihood path is locally `C^4` at zero for every
matrix/vector parameter.  No support assumption is needed: when the base
determinant vanishes the totalized path is constant, and otherwise its
determinant ratio equals one at zero. -/
private theorem centeredLogLikelihoodJoint_contDiffAt_four
    {N K : ℕ} (hN : 1 ≤ N)
    (p : ConcreteMatrixState N × ComplexUnitSphere N) :
    ContDiffAt ℝ 4 (fun t => centeredLogLikelihoodJoint N K (p, t)) 0 := by
  rw [centeredLogLikelihoodJoint_eq_version hN]
  simp only [centeredLogLikelihoodJointMeasurableVersion]
  split_ifs with hbase
  · fun_prop
  · let C := unscaleCOECorner K p.1
    let a := coeCornerDensityExponent N K
    let ratio : ℝ → ℝ := fun t =>
      (Matrix.det (1 -
        (concreteOrbitalMatrixUpdate N (-t) p.2 C).conjTranspose *
          concreteOrbitalMatrixUpdate N (-t) p.2 C)).re /
        (Matrix.det (1 - C.conjTranspose * C)).re
    change ContDiffAt ℝ 4
      (fun t => Real.log (Real.rpow (ratio t) a)) 0
    have hratio0 : ratio 0 = 1 := by
      simp [ratio, C, concreteOrbitalMatrixUpdate, concreteOrbitalFactor,
        hbase]
    have hratioCD : ContDiffAt ℝ 4 ratio 0 := by
      dsimp only [ratio, C]
      have hmovedComplex : ContDiffAt ℝ 4 (fun t : ℝ =>
          Matrix.det (1 -
            (concreteOrbitalMatrixUpdate N (-t) p.2
              (unscaleCOECorner K p.1)).conjTranspose *
            concreteOrbitalMatrixUpdate N (-t) p.2
              (unscaleCOECorner K p.1))) 0 := by
        simp only [Matrix.det_apply', Matrix.sub_apply, Matrix.one_apply,
          Matrix.mul_apply, Matrix.conjTranspose_apply,
          concreteOrbitalMatrixUpdate, concreteOrbitalFactor,
          complexRankOneProjection, Matrix.transpose_apply,
          Matrix.smul_apply, Matrix.add_apply]
        fun_prop
      have hmovedReal : ContDiffAt ℝ 4 (fun t : ℝ =>
          (Matrix.det (1 -
            (concreteOrbitalMatrixUpdate N (-t) p.2
              (unscaleCOECorner K p.1)).conjTranspose *
            concreteOrbitalMatrixUpdate N (-t) p.2
              (unscaleCOECorner K p.1))).re) 0 := by
        exact (Complex.reCLM.contDiff.contDiffAt).comp 0 hmovedComplex
      exact hmovedReal.div_const
        ((Matrix.det (1 -
          (unscaleCOECorner K p.1).conjTranspose *
            unscaleCOECorner K p.1)).re)
    have hpos : ∀ᶠ t in 𝓝 0, 0 < ratio t := by
      have hzero : 0 < ratio 0 := by rw [hratio0]; norm_num
      exact hratioCD.continuousAt.eventually (lt_mem_nhds hzero)
    have heq :
        (fun t => Real.log (Real.rpow (ratio t) a)) =ᶠ[𝓝 0]
          (fun t => Real.log (ratio t) * a) := by
      filter_upwards [hpos] with t ht
      rw [Real.rpow_eq_pow, Real.rpow_def_of_pos ht, Real.log_exp]
    have hlog : ContDiffAt ℝ 4 (fun t => Real.log (ratio t)) 0 :=
      hratioCD.log (by rw [hratio0]; norm_num)
    exact (hlog.mul contDiffAt_const).congr_of_eventuallyEq heq

/-- The literal first centered log-score is measurable; no score-moment
input is used. -/
theorem measurable_concreteCenteredEll_one
    {N K : ℕ} (hN : 1 ≤ N) :
    Measurable (concreteCenteredEll 1 N K) := by
  have hmeas := measurable_derivApprox
    (measurable_centeredLogLikelihoodJoint (N := N) (K := K) hN)
  have heq : concreteCenteredEll 1 N K = fun p =>
      derivApprox (centeredLogLikelihoodJoint N K) (p, 0) := by
    funext p
    symm
    rw [derivApprox_eq_iteratedDeriv_one]
    · rfl
    · exact (centeredLogLikelihoodJoint_contDiffAt_two hN p).differentiableAt
        (by norm_num)
  rw [heq]
  exact hmeas.comp (measurable_id.prodMk measurable_const)

/-- The literal second centered log-score is measurable; no score-moment
input is used. -/
theorem measurable_concreteCenteredEll_two
    {N K : ℕ} (hN : 1 ≤ N) :
    Measurable (concreteCenteredEll 2 N K) := by
  have hmeas := measurable_derivApproxTwo
    (measurable_centeredLogLikelihoodJoint (N := N) (K := K) hN)
  have heq : concreteCenteredEll 2 N K = fun p =>
      derivApproxTwo (centeredLogLikelihoodJoint N K) (p, 0) := by
    funext p
    symm
    rw [derivApproxTwo_eq_iteratedDeriv_two]
    · rfl
    · exact centeredLogLikelihoodJoint_contDiffAt_two hN p
  rw [heq]
  exact hmeas.comp (measurable_id.prodMk measurable_const)

/-- The literal third centered log-score is measurable.  This is obtained
from a measurable third finite-difference limit and the total `C^4` path
calculus above; no moment input is used. -/
theorem measurable_concreteCenteredEll_three
    {N K : ℕ} (hN : 1 ≤ N) :
    Measurable (concreteCenteredEll 3 N K) := by
  have hmeas := measurable_derivApproxThree
    (measurable_centeredLogLikelihoodJoint (N := N) (K := K) hN)
  have heq : concreteCenteredEll 3 N K = fun p =>
      derivApproxThree (centeredLogLikelihoodJoint N K) (p, 0) := by
    funext p
    unfold concreteCenteredEll
    symm
    have hfour := centeredLogLikelihoodJoint_contDiffAt_four
      (K := K) hN p
    have hthree : ContDiffAt ℝ (3 : WithTop ℕ∞)
        (fun t => centeredLogLikelihoodJoint N K (p, t)) 0 :=
      hfour.of_le (by norm_num)
    exact derivApproxThree_eq_iteratedDeriv_three (p, 0) hthree
  rw [heq]
  exact hmeas.comp (measurable_id.prodMk measurable_const)

/-- The literal fourth centered log-score is measurable by the analogous
fourth finite-difference representation. -/
theorem measurable_concreteCenteredEll_four
    {N K : ℕ} (hN : 1 ≤ N) :
    Measurable (concreteCenteredEll 4 N K) := by
  have hmeas := measurable_derivApproxFour
    (measurable_centeredLogLikelihoodJoint (N := N) (K := K) hN)
  have heq : concreteCenteredEll 4 N K = fun p =>
      derivApproxFour (centeredLogLikelihoodJoint N K) (p, 0) := by
    funext p
    unfold concreteCenteredEll
    symm
    exact derivApproxFour_eq_iteratedDeriv_four (p, 0)
      (centeredLogLikelihoodJoint_contDiffAt_four (K := K) hN p)
  rw [heq]
  exact hmeas.comp (measurable_id.prodMk measurable_const)

/-! ## The derived mixed-moment reducer -/

/-- The mixed first/second log-score package follows internally from the
retained first-fourth and second-square packages. -/
theorem centeredLogScore_oneSquareTwo_momentPackage_of_twoSquare
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hTwo :
      MemLp (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
          (concreteCenteredScoreProductLaw N K) ∧
        (16 * N ≤ K →
          lpNorm (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
              (concreteCenteredScoreProductLaw N K) ≤
            centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2)) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 2 *
      concreteCenteredEll 2 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 2 *
          concreteCenteredEll 2 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  let μ := concreteCenteredScoreProductLaw N K
  let f : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p => concreteCenteredEll 1 N K p ^ 4
  let g : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p => concreteCenteredEll 2 N K p ^ 2
  let mixed : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p => concreteCenteredEll 1 N K p ^ 2 *
      concreteCenteredEll 2 N K p
  let majorant : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    (1 / 2 : ℝ) • f + (1 / 2 : ℝ) • g
  have hf : MemLp f 1 μ := by
    exact centeredLogScore_oneFourth_memLp_one_proved_A1A2A3A4 hN hgap
  have hg : MemLp g 1 μ := by
    exact hTwo.1
  have hmajorant : MemLp majorant 1 μ := by
    exact (hf.const_smul (1 / 2 : ℝ)).add
      (hg.const_smul (1 / 2 : ℝ))
  have hmixedMeas : AEStronglyMeasurable mixed μ := by
    have hOne := measurable_concreteCenteredEll_one (N := N) (K := K) hN
    have hTwo := measurable_concreteCenteredEll_two (N := N) (K := K) hN
    exact ((hOne.pow_const 2).mul hTwo).aestronglyMeasurable
  have hYoung : ∀ p, ‖mixed p‖ ≤ majorant p := by
    intro p
    simp only [mixed, majorant, f, g, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
      (sq_nonneg (concreteCenteredEll 1 N K p))]
    nlinarith [sq_nonneg
      (concreteCenteredEll 1 N K p ^ 2 -
        |concreteCenteredEll 2 N K p|),
      sq_abs (concreteCenteredEll 2 N K p)]
  have hMajorantNonneg : ∀ p, 0 ≤ majorant p := by
    intro p
    simp only [majorant, f, g, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    positivity
  have hYoungNorm : ∀ p, ‖mixed p‖ ≤ ‖majorant p‖ := by
    intro p
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hMajorantNonneg p)] using
      hYoung p
  have hmixed : MemLp mixed 1 μ :=
    hmajorant.of_le hmixedMeas (Eventually.of_forall hYoungNorm)
  constructor
  · exact hmixed
  · intro hdense
    have hfBound : lpNorm f 1 μ ≤
        centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
      exact centeredLogScore_oneFourth_lpNorm_one_le_proved_A1A2A3A4 hN hdense
    have hgBound : lpNorm g 1 μ ≤
        centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
      exact hTwo.2 hdense
    have hmono : lpNorm mixed 1 μ ≤ lpNorm majorant 1 μ :=
      lpNorm_mono_real hmajorant hYoung
    have hadd : lpNorm majorant 1 μ ≤
        lpNorm ((1 / 2 : ℝ) • f) 1 μ +
          lpNorm ((1 / 2 : ℝ) • g) 1 μ := by
      exact lpNorm_add_le (hf.const_smul (1 / 2 : ℝ)) (by norm_num)
    have hscaleF : lpNorm ((1 / 2 : ℝ) • f) 1 μ =
        (1 / 2 : ℝ) * lpNorm f 1 μ := by
      rw [lpNorm_const_smul]
      norm_num
    have hscaleG : lpNorm ((1 / 2 : ℝ) • g) 1 μ =
        (1 / 2 : ℝ) * lpNorm g 1 μ := by
      rw [lpNorm_const_smul]
      norm_num
    change lpNorm mixed 1 μ ≤ _
    calc
      lpNorm mixed 1 μ ≤ lpNorm majorant 1 μ := hmono
      _ ≤ lpNorm ((1 / 2 : ℝ) • f) 1 μ +
          lpNorm ((1 / 2 : ℝ) • g) 1 μ := hadd
      _ = (1 / 2 : ℝ) * lpNorm f 1 μ +
          (1 / 2 : ℝ) * lpNorm g 1 μ := by rw [hscaleF, hscaleG]
      _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
        nlinarith

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
