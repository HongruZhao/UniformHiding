import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7CentralShiftCocycle
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
import Mathlib.Tactic.FunProp

/-!
# Fixed-state projective Hessian functional for H7

The projective average is packaged as one continuous linear functional on
the Hessian space.  Therefore differentiating the average is ordinary
finite-dimensional Frechet calculus, not differentiation under an integral.
-/

open Function MeasureTheory
open scoped Matrix Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

-- Keep the one-dimensional derivative structure on the normed-algebra path;
-- this import graph also exposes propositionally equal ordered-ring and
-- inner-product instances for the same real scalar operations.
attribute [local instance 2000] Real.normedAddCommGroup
  NormedAlgebra.toNormedSpace

private abbrev H7AlgebraRealHasDerivAt
    (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ Real.normedAddCommGroup.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℝ).toModule _ _ f f' x

private abbrev H7HessianSpace (V : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] :=
  ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ V) ℝ

/- The pointwise-topology instances on operator spaces coexist with their
operator-norm instances in Mathlib.  Fix the latter locally so the Bochner
integral and Frechet calculus use one definitionally coherent topology. -/
private noncomputable local instance h7HessianSpaceNormed
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (H7HessianSpace V) :=
  ContinuousMultilinearMap.normedAddCommGroup

private noncomputable local instance h7HessianDualNormed
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    NormedAddCommGroup (H7HessianSpace V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

section Curry

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private noncomputable def h7HessianCurryOne :
    ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ V) ℝ →L[ℝ]
      (V →L[ℝ] ℝ) :=
  (continuousMultilinearCurryFin1 ℝ V ℝ).toContinuousLinearEquiv.toContinuousLinearMap

private noncomputable def h7HessianCurryTwo :
    H7HessianSpace V →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ V
      (ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ V) ℝ)
      (V →L[ℝ] ℝ) h7HessianCurryOne).comp
    ((continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin 2 ↦ V) ℝ).toContinuousLinearEquiv.toContinuousLinearMap)

/-- Evaluation of a Hessian twice in a fixed vector, as a continuous linear
functional of the Hessian. -/
private noncomputable def h7HessianDiagonalEval (q : V) :
    H7HessianSpace V →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ q).comp <|
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) q).comp h7HessianCurryTwo

@[simp]
private theorem h7HessianDiagonalEval_apply
    (q : V) (D : H7HessianSpace V) :
    h7HessianDiagonalEval q D = D ![q, q] := by
  change D (Fin.cons q (Fin.snoc 0 q)) = D ![q, q]
  congr 1
  funext i
  fin_cases i <;> rfl

end Curry

private theorem continuous_h7HessianDiagonalEval_centered (N : ℕ) :
    Continuous (fun v : ComplexUnitSphere N ↦
      h7HessianDiagonalEval
        (concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v))) := by
  let q : ComplexUnitSphere N → ConcreteMatrixRealCoordinates N := fun v ↦
    concreteMatrixRealCoordinates (concreteCenteredOrbitalDirection N v)
  have hq : Continuous q := by
    simpa only [q] using continuous_concreteCenteredOrbitalCoordinates N
  have houter : Continuous (fun v : ComplexUnitSphere N ↦
      ContinuousLinearMap.apply ℝ ℝ (q v)) :=
    (ContinuousLinearMap.apply ℝ ℝ).continuous.comp hq
  have hinnerApply : Continuous (fun v : ComplexUnitSphere N ↦
      ContinuousLinearMap.apply ℝ
        (ConcreteMatrixRealCoordinates N →L[ℝ] ℝ) (q v)) :=
    (ContinuousLinearMap.apply ℝ
      (ConcreteMatrixRealCoordinates N →L[ℝ] ℝ)).continuous.comp hq
  have hinner : Continuous (fun v : ComplexUnitSphere N ↦
      (ContinuousLinearMap.apply ℝ
        (ConcreteMatrixRealCoordinates N →L[ℝ] ℝ) (q v)).comp
          h7HessianCurryTwo) := by
    exact hinnerApply.clm_comp continuous_const
  exact houter.clm_comp hinner

private theorem integrable_h7HessianDiagonalEval_centered
    {N : ℕ} (hN : 1 ≤ N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      h7HessianDiagonalEval
        (concreteMatrixRealCoordinates
          (concreteCenteredOrbitalDirection N v)))
      (complexUnitSphereProbabilityMeasure N) := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  simpa only [integrableOn_univ] using
    (continuous_h7HessianDiagonalEval_centered N).continuousOn.integrableOn_compact
      (μ := complexUnitSphereProbabilityMeasure N) isCompact_univ

/-- Fixed-state projective average as a continuous linear functional of a
Hessian. -/
noncomputable def h7ProjectiveHessianAverageCLM (N : ℕ) :
    H7HessianSpace (ConcreteMatrixRealCoordinates N) →L[ℝ] ℝ :=
  ∫ v : ComplexUnitSphere N,
    h7HessianDiagonalEval
      (concreteMatrixRealCoordinates
        (concreteCenteredOrbitalDirection N v))
    ∂(complexUnitSphereProbabilityMeasure N)

theorem h7ProjectiveHessianAverageCLM_apply
    {N : ℕ} (hN : 1 ≤ N)
    (D : H7HessianSpace (ConcreteMatrixRealCoordinates N)) :
    h7ProjectiveHessianAverageCLM N D =
      ∫ v : ComplexUnitSphere N,
        D ![concreteMatrixRealCoordinates
              (concreteCenteredOrbitalDirection N v),
            concreteMatrixRealCoordinates
              (concreteCenteredOrbitalDirection N v)]
        ∂(complexUnitSphereProbabilityMeasure N) := by
  calc
    h7ProjectiveHessianAverageCLM N D =
        (∫ v : ComplexUnitSphere N,
          h7HessianDiagonalEval
            (concreteMatrixRealCoordinates
              (concreteCenteredOrbitalDirection N v))
          ∂(complexUnitSphereProbabilityMeasure N)) D := rfl
    _ = ∫ v : ComplexUnitSphere N,
          h7HessianDiagonalEval
            (concreteMatrixRealCoordinates
              (concreteCenteredOrbitalDirection N v)) D
          ∂(complexUnitSphereProbabilityMeasure N) :=
      ContinuousLinearMap.integral_apply
        (integrable_h7HessianDiagonalEval_centered hN) D
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact h7HessianDiagonalEval_apply _ _

/-- The averaged Hessian of the literal coordinate likelihood along the
central coordinate line. -/
def h7ProjectiveHessianPath {N : ℕ} (K : ℕ)
    (A : ConcreteMatrixState N) (s : ℝ) : ℝ :=
  h7ProjectiveHessianAverageCLM N <|
    iteratedFDeriv ℝ 2 (h16CoordinateLikelihoodCore K A)
      (s • concreteMatrixRealCoordinates (1 : ConcreteMatrixState N))

private theorem h16CoordinateCubicValue_eq_raw_of_contDiffAt_top
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (x y z : ConcreteMatrixRealCoordinates N) :
    h16CoordinateCubicValue K A x y z =
      iteratedFDeriv ℝ 3 (h16CoordinateLikelihoodCore K A) 0 ![x, y, z] := by
  let D := iteratedFDeriv ℝ 3 (h16CoordinateLikelihoodCore K A) 0
  have hf := h16CoordinateLikelihoodCore_contDiffAt_top A hsupport
  have hxy : D ![y, x, z] = D ![x, y, z] := by
    have h := hf.iteratedFDeriv_comp_perm ![x, y, z]
      (Equiv.swap (0 : Fin 3) (1 : Fin 3))
    have hv : (![x, y, z] ∘ (Equiv.swap (0 : Fin 3) (1 : Fin 3))) =
        ![y, x, z] := by
      funext j
      fin_cases j <;> rfl
    change D (![x, y, z] ∘ (Equiv.swap (0 : Fin 3) (1 : Fin 3))) =
      D ![x, y, z] at h
    rw [hv] at h
    exact h
  have hxz : D ![x, z, y] = D ![x, y, z] := by
    have h := hf.iteratedFDeriv_comp_perm ![x, y, z]
      (Equiv.swap (1 : Fin 3) (2 : Fin 3))
    have hv : (![x, y, z] ∘ (Equiv.swap (1 : Fin 3) (2 : Fin 3))) =
        ![x, z, y] := by
      funext j
      fin_cases j <;> rfl
    change D (![x, y, z] ∘ (Equiv.swap (1 : Fin 3) (2 : Fin 3))) =
      D ![x, y, z] at h
    rw [hv] at h
    exact h
  have hyzx : D ![y, z, x] = D ![x, y, z] := by
    have h := hf.iteratedFDeriv_comp_perm ![x, y, z]
      ((Equiv.swap (1 : Fin 3) (2 : Fin 3)).trans
        (Equiv.swap (0 : Fin 3) (1 : Fin 3)))
    have hv : (![x, y, z] ∘
        ((Equiv.swap (1 : Fin 3) (2 : Fin 3)).trans
          (Equiv.swap (0 : Fin 3) (1 : Fin 3)))) = ![y, z, x] := by
      funext j
      fin_cases j <;> rfl
    change D (![x, y, z] ∘
        ((Equiv.swap (1 : Fin 3) (2 : Fin 3)).trans
          (Equiv.swap (0 : Fin 3) (1 : Fin 3)))) = D ![x, y, z] at h
    rw [hv] at h
    exact h
  have hzxy : D ![z, x, y] = D ![x, y, z] := by
    have h := hf.iteratedFDeriv_comp_perm ![x, y, z]
      ((Equiv.swap (0 : Fin 3) (1 : Fin 3)).trans
        (Equiv.swap (1 : Fin 3) (2 : Fin 3)))
    have hv : (![x, y, z] ∘
        ((Equiv.swap (0 : Fin 3) (1 : Fin 3)).trans
          (Equiv.swap (1 : Fin 3) (2 : Fin 3)))) = ![z, x, y] := by
      funext j
      fin_cases j <;> rfl
    change D (![x, y, z] ∘
        ((Equiv.swap (0 : Fin 3) (1 : Fin 3)).trans
          (Equiv.swap (1 : Fin 3) (2 : Fin 3)))) = D ![x, y, z] at h
    rw [hv] at h
    exact h
  have hzyx : D ![z, y, x] = D ![x, y, z] := by
    have h := hf.iteratedFDeriv_comp_perm ![x, y, z]
      (Equiv.swap (0 : Fin 3) (2 : Fin 3))
    have hv : (![x, y, z] ∘ (Equiv.swap (0 : Fin 3) (2 : Fin 3))) =
        ![z, y, x] := by
      funext j
      fin_cases j <;> rfl
    change D (![x, y, z] ∘ (Equiv.swap (0 : Fin 3) (2 : Fin 3))) =
      D ![x, y, z] at h
    rw [hv] at h
    exact h
  unfold h16CoordinateCubicValue h16SymmetrizedThirdFrechetValue
    h16CoordinateThirdFrechetDifferential
  change (D ![x, y, z] + D ![x, z, y] + D ![y, x, z] +
      D ![y, z, x] + D ![z, x, y] + D ![z, y, x]) / 6 = _
  rw [hxy, hxz, hyzx, hzxy, hzyx]
  ring

/-- The derivative of the fixed projective Hessian path is exactly the mixed
partial of the literal symmetric third Frechet differential. -/
theorem h7ProjectiveHessianPath_hasDerivAt
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    H7AlgebraRealHasDerivAt (h7ProjectiveHessianPath K A)
      (∫ v : ComplexUnitSphere N,
        (h7CoordinateDifferential K A).form
          (concreteMatrixRealCoordinates (1 : ConcreteMatrixState N))
          (concreteMatrixRealCoordinates
            (concreteCenteredOrbitalDirection N v))
          (concreteMatrixRealCoordinates
            (concreteCenteredOrbitalDirection N v))
        ∂(complexUnitSphereProbabilityMeasure N)) 0 := by
  let f := h16CoordinateLikelihoodCore K A
  let i := concreteMatrixRealCoordinates (1 : ConcreteMatrixState N)
  let D₂ := iteratedFDeriv ℝ 2 f
  have hf : ContDiffAt ℝ 3 f 0 :=
    (h16CoordinateLikelihoodCore_contDiffAt_top A hsupport).of_le (by norm_num)
  have hD₂ : DifferentiableAt ℝ D₂ 0 :=
    hf.differentiableAt_iteratedFDeriv (by norm_num)
  have hsmul : HasDerivAt (fun s : ℝ ↦ s • i) i 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const i)
  have hD₂' : DifferentiableAt ℝ D₂ ((0 : ℝ) • i) := by
    simpa only [zero_smul] using hD₂
  have hline₀ := hD₂'.hasFDerivAt.comp_hasDerivAt 0 hsmul
  have havg₀ := (h7ProjectiveHessianAverageCLM N).hasFDerivAt.comp_hasDerivAt
    0 hline₀
  have havg : H7AlgebraRealHasDerivAt (h7ProjectiveHessianPath K A)
      (h7ProjectiveHessianAverageCLM N ((fderiv ℝ D₂ 0) i)) 0 := by
    apply (havg₀.congr_deriv (by rw [zero_smul])).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun s ↦ by
      rfl
  have hder :
      h7ProjectiveHessianAverageCLM N ((fderiv ℝ D₂ 0) i) =
        ∫ v : ComplexUnitSphere N,
          (h7CoordinateDifferential K A).form i
            (concreteMatrixRealCoordinates
              (concreteCenteredOrbitalDirection N v))
            (concreteMatrixRealCoordinates
              (concreteCenteredOrbitalDirection N v))
          ∂(complexUnitSphereProbabilityMeasure N) := by
    rw [h7ProjectiveHessianAverageCLM_apply hN]
    apply integral_congr_ae
    filter_upwards [] with v
    let q := concreteMatrixRealCoordinates
      (concreteCenteredOrbitalDirection N v)
    have hcurry : ((fderiv ℝ D₂ 0) i) ![q, q] =
        iteratedFDeriv ℝ 3 f 0 ![i, q, q] := by
      change ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin 3 ↦ ConcreteMatrixRealCoordinates N) ℝ)
          (iteratedFDeriv ℝ 3 f 0)) i ![q, q] = _
      rfl
    rw [hcurry]
    rw [show (h7CoordinateDifferential K A).form i q q =
        h16CoordinateCubicValue K A i q q by
      exact h7CoordinateDifferential_apply A i q q]
    exact (h16CoordinateCubicValue_eq_raw_of_contDiffAt_top
      A hsupport i q q).symm
  apply havg.congr_deriv
  exact hder

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
