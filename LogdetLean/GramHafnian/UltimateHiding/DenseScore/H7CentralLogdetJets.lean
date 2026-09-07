import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7CentralScalar
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-!
# Trace jets of the literal H7 central log determinant

This file differentiates the finite matrix determinant on the identity line.
It uses only the determinant Leibniz formula, inversion in a finite-dimensional
normed matrix algebra, and the support-matrix algebra.
-/

open Function Matrix Polynomial
open scoped Matrix Topology ComplexConjugate ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxRecDepth 4000

open LogdetLean.GramHafnian.UltimateHiding.Dense

private theorem h7_eval_det_one_add_X_smul
    {N : ℕ} (R : ConcreteMatrixState N) (z : ℂ) :
    (Matrix.det
      (1 + (Polynomial.X : ℂ[X]) • R.map Polynomial.C)).eval z =
      Matrix.det (1 + z • R : ConcreteMatrixState N) := by
  rw [eval_det, matPolyEquiv_eval_eq_map]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, if_pos, Polynomial.eval_one, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
      smul_eq_mul, one_mul]
  · simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, hij, if_neg, if_false, Polynomial.eval_zero,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
      Polynomial.eval_C, smul_eq_mul, one_mul, zero_add, add_zero]

local instance h7CentralJetsMatrixNormedAddCommGroup {N : ℕ} :
    NormedAddCommGroup (ConcreteMatrixState N) :=
  Matrix.linftyOpNormedAddCommGroup

local instance h7CentralJetsMatrixNormedSpace {N : ℕ} :
    NormedSpace ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

local instance h7CentralJetsMatrixRealNormedSpace {N : ℕ} :
    NormedSpace ℝ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

local instance h7CentralJetsMatrixAddCommGroup {N : ℕ} :
    AddCommGroup (ConcreteMatrixState N) :=
  h7CentralJetsMatrixNormedAddCommGroup.toAddCommGroup

local instance h7CentralJetsMatrixModule {N : ℕ} :
    Module ℂ (ConcreteMatrixState N) :=
  h7CentralJetsMatrixNormedSpace.toModule

local instance h7CentralJetsMatrixRealModule {N : ℕ} :
    Module ℝ (ConcreteMatrixState N) :=
  h7CentralJetsMatrixRealNormedSpace.toModule

local instance h7CentralJetsMatrixPseudoMetricSpace {N : ℕ} :
    PseudoMetricSpace (ConcreteMatrixState N) :=
  h7CentralJetsMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance h7CentralJetsMatrixUniformSpace {N : ℕ} :
    UniformSpace (ConcreteMatrixState N) :=
  h7CentralJetsMatrixPseudoMetricSpace.toUniformSpace

local instance h7CentralJetsMatrixTopologicalSpace {N : ℕ} :
    TopologicalSpace (ConcreteMatrixState N) :=
  h7CentralJetsMatrixUniformSpace.toTopologicalSpace

local instance h7CentralJetsMatrixNormedRing {N : ℕ} :
    NormedRing (ConcreteMatrixState N) := Matrix.linftyOpNormedRing

private theorem h7_contDiff_complex_ofReal {f : ℝ → ℝ}
    (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun x : ℝ => (f x : ℂ)) := by
  convert Complex.ofRealCLM.contDiff.comp hf using 1
  funext x
  simp only [Function.comp_apply, Complex.ofRealCLM_apply]

local instance h7CentralJetsMatrixNormedAlgebra {N : ℕ} :
    NormedAlgebra ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra

local instance h7CentralJetsMatrixRealNormedAlgebra {N : ℕ} :
    NormedAlgebra ℝ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra

private def h7CentralJetsTraceCLM (N : ℕ) :
    ConcreteMatrixState N →L[ℝ] ℂ :=
  (Matrix.traceLinearMap (Fin N) ℝ ℂ).toContinuousLinearMap

/-- The input-side resolvent kernel `(I-CᴴC)⁻¹ CᴴC`. -/
def h7CentralInputKernel {N : ℕ} (K : ℕ)
    (A : ConcreteMatrixState N) : ConcreteMatrixState N :=
  let C := unscaleCOECorner K A
  (1 - C.conjTranspose * C)⁻¹ * (C.conjTranspose * C)

private theorem h7_hasDerivAt_one_add_smul_nonsingInv
    {N : ℕ} (Z : ConcreteMatrixState N) (x : ℝ)
    (hunit : IsUnit
      (1 + (((x : ℝ) : ℂ)) • Z : ConcreteMatrixState N)) :
    HasDerivAt
      (fun s : ℝ =>
        (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹)
      (-((1 + (((x : ℝ) : ℂ)) • Z)⁻¹ * Z *
        (1 + (((x : ℝ) : ℂ)) • Z)⁻¹)) x := by
  have hinner : HasDerivAt
      (fun s : ℝ =>
        (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)) Z x := by
    simpa only [id_eq, Complex.ofReal_one, one_smul] using
      ((hasDerivAt_id x).ofReal_comp.smul_const Z).const_add 1
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit
  have hcomp := hinv.comp_hasDerivAt x hinner
  have hinvEq :
      (1 + (((x : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ =
        (↑(hunit.unit⁻¹) : ConcreteMatrixState N) := by
    calc
      (1 + (((x : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ =
          Ring.inverse (1 + (((x : ℝ) : ℂ)) • Z) :=
        nonsing_inv_eq_ringInverse _
      _ = Ring.inverse (hunit.unit : ConcreteMatrixState N) :=
        congrArg Ring.inverse hunit.unit_spec.symm
      _ = (↑(hunit.unit⁻¹) : ConcreteMatrixState N) := Ring.inverse_unit _
  convert hcomp using 1 <;> try rfl
  · funext s
    simp only [Function.comp_apply, nonsing_inv_eq_ringInverse]
  · simp only [ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.mulLeftRight_apply]
    rw [hinvEq]

private theorem h7_hasDerivAt_det_one_add_smul
    {N : ℕ} (Z : ConcreteMatrixState N) (x : ℝ)
    (hunit : IsUnit
      (1 + (((x : ℝ) : ℂ)) • Z : ConcreteMatrixState N)) :
    deriv
      (fun s : ℝ => (Matrix.det
        (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re) x =
      (Matrix.det (1 + (((x : ℝ) : ℂ)) • Z) *
        Matrix.trace
          ((1 + (((x : ℝ) : ℂ)) • Z)⁻¹ * Z)).re := by
  let Fx : ConcreteMatrixState N :=
    1 + (((x : ℝ) : ℂ)) • Z
  let R : ConcreteMatrixState N := Fx⁻¹ * Z
  let P : ℂ[X] := Matrix.det
    (1 + (Polynomial.X : ℂ[X]) • R.map Polynomial.C)
  have hP := P.hasDerivAt (0 : ℂ)
  have hP' : P.derivative.eval 0 = Matrix.trace R := by
    exact Matrix.derivative_det_one_add_X_smul R
  rw [hP'] at hP
  have hpolyFun :
      (fun z : ℂ => P.eval z) =
      (fun z : ℂ => Matrix.det
        (1 + z • R : ConcreteMatrixState N)) := by
    funext z
    unfold P
    exact h7_eval_det_one_add_X_smul R z
  rw [hpolyFun] at hP
  have hzero := hP.comp_ofReal
  have hx0 : x - x = 0 := sub_self x
  have hzero' := hx0.symm ▸ hzero
  have hshift := hzero'.comp_sub_const x x
  have hscaled := hshift.const_mul (Matrix.det Fx)
  have hdetUnit : IsUnit (Matrix.det Fx) :=
    (Matrix.isUnit_iff_isUnit_det Fx).mp (by simpa only [Fx] using hunit)
  have hinv : Fx * Fx⁻¹ = 1 := Matrix.mul_nonsing_inv Fx hdetUnit
  have hfun :
      (fun s : ℝ => Matrix.det Fx * Matrix.det
        (1 + ((((s - x : ℝ) : ℂ))) • R : ConcreteMatrixState N)) =
      (fun s : ℝ => Matrix.det
        (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)) := by
    funext s
    rw [← Matrix.det_mul]
    congr 1
    unfold R
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    unfold Fx
    module
  rw [hfun] at hscaled
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hscaled
  have hd := hre.deriv
  have hreFun :
      (Complex.reCLM ∘ (fun s : ℝ => Matrix.det
        (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N))) =
      (fun s : ℝ => (Matrix.det
        (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re) := by
    rfl
  rw [hreFun] at hd
  simpa only [Fx, R, Complex.reCLM_apply] using hd

private theorem h7_deriv_re_trace_nonsingInv_mul
    {N : ℕ} (Z : ConcreteMatrixState N) (x : ℝ)
    (hunit : IsUnit
      (1 + (((x : ℝ) : ℂ)) • Z : ConcreteMatrixState N)) :
    deriv (fun s : ℝ =>
        (Matrix.trace
          ((1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z)).re) x =
      (-Matrix.trace
        ((1 + (((x : ℝ) : ℂ)) • Z)⁻¹ * Z *
          (1 + (((x : ℝ) : ℂ)) • Z)⁻¹ * Z)).re := by
  have hJ := h7_hasDerivAt_one_add_smul_nonsingInv Z x hunit
  have hJZ := hJ.mul_const Z
  have htr := (h7CentralJetsTraceCLM N).hasFDerivAt.comp_hasDerivAt x hJZ
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x htr
  have hd := hre.deriv
  have hfun :
      (Complex.reCLM ∘ (h7CentralJetsTraceCLM N ∘
        (fun s : ℝ =>
          (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z))) =
      (fun s : ℝ =>
        (Matrix.trace
          ((1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z)).re) := by
    rfl
  rw [hfun] at hd
  change deriv (fun s : ℝ =>
      (Matrix.trace
        ((1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z)).re) x =
    (Matrix.trace
      ((-((1 + (((x : ℝ) : ℂ)) • Z)⁻¹ * Z *
        (1 + (((x : ℝ) : ℂ)) • Z)⁻¹)) * Z)).re at hd
  have hneg :
      (-((1 + (((x : ℝ) : ℂ)) • Z)⁻¹ * Z *
        (1 + (((x : ℝ) : ℂ)) • Z)⁻¹)) * Z =
      -((1 + (((x : ℝ) : ℂ)) • Z)⁻¹ * Z *
        (1 + (((x : ℝ) : ℂ)) • Z)⁻¹ * Z) := by
    noncomm_ring
  rw [hneg, Matrix.trace_neg, Complex.neg_re] at hd
  exact hd

private theorem h7_deriv_neg_re_trace_nonsingInv_square
    {N : ℕ} (Z : ConcreteMatrixState N) (x : ℝ)
    (hunit : IsUnit
      (1 + (((x : ℝ) : ℂ)) • Z : ConcreteMatrixState N)) :
    deriv (fun s : ℝ =>
        -(Matrix.trace
          ((1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z *
            (1 + (((s : ℝ) : ℂ)) • Z)⁻¹ * Z)).re) x =
      2 * (Matrix.trace
        ((1 + (((x : ℝ) : ℂ)) • Z)⁻¹ * Z *
          (1 + (((x : ℝ) : ℂ)) • Z)⁻¹ * Z *
          (1 + (((x : ℝ) : ℂ)) • Z)⁻¹ * Z)).re := by
  let J : ℝ → ConcreteMatrixState N := fun s =>
    (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹
  have hJ : HasDerivAt J (-(J x * Z * J x)) x := by
    simpa only [J] using h7_hasDerivAt_one_add_smul_nonsingInv Z x hunit
  have hJZ := hJ.mul_const Z
  have hJZJ := hJZ.mul hJ
  have hJZJZ := hJZJ.mul_const Z
  have htr := (h7CentralJetsTraceCLM N).hasFDerivAt.comp_hasDerivAt x hJZJZ
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x htr
  have hneg := hre.neg
  have hneg' : HasDerivAt
      (fun s : ℝ => -(Matrix.trace (J s * Z * J s * Z)).re)
      (-Complex.reCLM ((h7CentralJetsTraceCLM N)
        (((-(J x * Z * J x)) * Z * J x +
          J x * Z * (-(J x * Z * J x))) * Z))) x := by
    apply hneg.congr_of_eventuallyEq
    filter_upwards with s
    rfl
  have hd := hneg'.deriv
  change deriv (fun s : ℝ =>
      -(Matrix.trace (J s * Z * J s * Z)).re) x =
    -((Matrix.trace
      (((-(J x * Z * J x)) * Z * J x +
        J x * Z * (-(J x * Z * J x))) * Z)).re) at hd
  have hmatrix :
      (((-(J x * Z * J x)) * Z * J x +
        J x * Z * (-(J x * Z * J x))) * Z) =
      -(J x * Z * J x * Z * J x * Z) -
        (J x * Z * J x * Z * J x * Z) := by
    noncomm_ring
  rw [hmatrix, Matrix.trace_sub, Matrix.trace_neg, Complex.sub_re,
    Complex.neg_re] at hd
  change deriv (fun s : ℝ =>
      -(Matrix.trace
        ((1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z *
          (1 + (((s : ℝ) : ℂ)) • Z)⁻¹ * Z)).re) x = _ at hd
  simp only [J] at hd
  rw [hd]
  ring

private theorem h7_one_add_real_smul_isHermitian
    {N : ℕ} (Z : ConcreteMatrixState N) (hZ : Z.IsHermitian) (s : ℝ) :
    (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N).IsHermitian := by
  exact Matrix.isHermitian_one.add (hZ.smul (by simp [IsSelfAdjoint]))

private theorem h7_det_im_eq_zero_of_isHermitian
    {N : ℕ} (M : ConcreteMatrixState N) (hM : M.IsHermitian) :
    (Matrix.det M).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have h := congrArg Matrix.det hM.eq
  rw [Matrix.det_conjTranspose] at h
  exact h

private theorem h7_trace_im_eq_zero_of_isHermitian
    {N : ℕ} (M : ConcreteMatrixState N) (hM : M.IsHermitian) :
    (Matrix.trace M).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have h := congrArg Matrix.trace hM.eq
  rw [Matrix.trace_conjTranspose] at h
  exact h

private theorem h7_nonsingInv_mul_isHermitian
    {N : ℕ} (Z : ConcreteMatrixState N) (hZ : Z.IsHermitian) (s : ℝ)
    (hunit : IsUnit
      (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)) :
    ((1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z).IsHermitian := by
  let F : ConcreteMatrixState N := 1 + (((s : ℝ) : ℂ)) • Z
  have hF : F.IsHermitian := by
    exact h7_one_add_real_smul_isHermitian Z hZ s
  have hcommFZ : Commute F Z := by
    unfold F
    change (1 + (((s : ℝ) : ℂ)) • Z) * Z =
      Z * (1 + (((s : ℝ) : ℂ)) • Z)
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul]
  have hinvEq : F⁻¹ = (↑(hunit.unit⁻¹) : ConcreteMatrixState N) := by
    calc
      F⁻¹ = Ring.inverse F := nonsing_inv_eq_ringInverse _
      _ = Ring.inverse (hunit.unit : ConcreteMatrixState N) :=
        congrArg Ring.inverse hunit.unit_spec.symm
      _ = (↑(hunit.unit⁻¹) : ConcreteMatrixState N) := Ring.inverse_unit _
  have hcommInvZ : Commute F⁻¹ Z := by
    rw [hinvEq]
    apply Commute.units_inv_left
    simpa only [hunit.unit_spec] using hcommFZ
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, hZ.eq, hF.inv.eq]
  exact hcommInvZ.eq.symm

private theorem h7_det_re_one_add_smul_contDiff
    {N : ℕ} (Z : ConcreteMatrixState N) :
    ContDiff ℝ ⊤ (fun s : ℝ => (Matrix.det
      (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re) := by
  have hdet : ContDiff ℝ ⊤ (fun s : ℝ => Matrix.det
      (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)) := by
    simp only [Matrix.det_apply']
    apply ContDiff.sum
    intro σ _
    apply ContDiff.mul contDiff_const
    apply contDiff_prod
    intro i _
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply]
    apply ContDiff.add contDiff_const
    apply ContDiff.mul
    · exact h7_contDiff_complex_ofReal contDiff_id
    · exact contDiff_const
  have hre := Complex.reCLM.contDiff.comp hdet
  simpa only [Function.comp_def, Complex.reCLM_apply] using hre

private theorem h7_one_add_smul_eventually_isUnit
    {N : ℕ} (Z : ConcreteMatrixState N) :
    ∀ᶠ s in nhds 0,
      IsUnit (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N) := by
  have hcont : ContinuousAt
      (fun s : ℝ =>
        (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)) 0 := by
    fun_prop
  exact hcont (Units.isOpen.mem_nhds (by simp))

private theorem h7_det_re_one_add_smul_eventually_pos
    {N : ℕ} (Z : ConcreteMatrixState N) :
    ∀ᶠ s in nhds 0,
      0 < (Matrix.det
        (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re := by
  exact continuousAt_const.eventually_lt
    (h7_det_re_one_add_smul_contDiff Z).continuous.continuousAt (by simp)

private theorem h7_deriv_log_det_re_one_add_smul_eventuallyEq_trace
    {N : ℕ} (Z : ConcreteMatrixState N) (hZ : Z.IsHermitian) :
    (fun s : ℝ => deriv
      (fun r : ℝ => Real.log ((Matrix.det
        (1 + (((r : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re)) s) =ᶠ[nhds 0]
      (fun s : ℝ => (Matrix.trace
        ((1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z)).re) := by
  filter_upwards [h7_one_add_smul_eventually_isUnit Z,
    h7_det_re_one_add_smul_eventually_pos Z] with s hunit hpos
  have hdetHerm :
      (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N).IsHermitian :=
    h7_one_add_real_smul_isHermitian Z hZ s
  have htraceHerm :
      ((1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z).IsHermitian :=
    h7_nonsingInv_mul_isHermitian Z hZ s hunit
  have hdetIm := h7_det_im_eq_zero_of_isHermitian _ hdetHerm
  have htraceIm := h7_trace_im_eq_zero_of_isHermitian _ htraceHerm
  have hd : HasDerivAt
      (fun r : ℝ => (Matrix.det
        (1 + (((r : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re)
      (deriv (fun r : ℝ => (Matrix.det
        (1 + (((r : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re) s) s :=
    ((h7_det_re_one_add_smul_contDiff Z).differentiable (by simp)).differentiableAt.hasDerivAt
  rw [h7_hasDerivAt_det_one_add_smul Z s hunit] at hd
  have hlog := hd.log hpos.ne'
  rw [hlog.deriv]
  rw [Complex.mul_re, hdetIm, htraceIm]
  simp only [mul_zero, zero_mul, sub_zero]
  exact mul_div_cancel_left₀ _ hpos.ne'

/-- First trace jet of the real logarithmic determinant on a Hermitian line. -/
theorem h7_iteratedDeriv_one_log_det_re_one_add_smul
    {N : ℕ} (Z : ConcreteMatrixState N) (hZ : Z.IsHermitian) :
    iteratedDeriv 1
        (fun s : ℝ => Real.log ((Matrix.det
          (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re)) 0 =
      (Matrix.trace Z).re := by
  have heq := h7_deriv_log_det_re_one_add_smul_eventuallyEq_trace Z hZ
  rw [iteratedDeriv_one]
  have hzero := heq.self_of_nhds
  change deriv (fun s : ℝ => Real.log ((Matrix.det
    (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re)) 0 =
    (Matrix.trace
      ((1 + (((0 : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z)).re at hzero
  rw [hzero]
  simp

/-- Second trace jet of the real logarithmic determinant on a Hermitian line. -/
theorem h7_iteratedDeriv_two_log_det_re_one_add_smul
    {N : ℕ} (Z : ConcreteMatrixState N) (hZ : Z.IsHermitian) :
    iteratedDeriv 2
        (fun s : ℝ => Real.log ((Matrix.det
          (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re)) 0 =
      -(Matrix.trace (Z * Z)).re := by
  have heq := h7_deriv_log_det_re_one_add_smul_eventuallyEq_trace Z hZ
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, heq.deriv_eq,
    h7_deriv_re_trace_nonsingInv_mul Z 0 (by simp)]
  simp

/-- Third trace jet of the real logarithmic determinant on a Hermitian line. -/
theorem h7_iteratedDeriv_three_log_det_re_one_add_smul
    {N : ℕ} (Z : ConcreteMatrixState N) (hZ : Z.IsHermitian) :
    iteratedDeriv 3
        (fun s : ℝ => Real.log ((Matrix.det
          (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re)) 0 =
      2 * (Matrix.trace (Z * Z * Z)).re := by
  let f : ℝ → ℝ := fun s => Real.log ((Matrix.det
    (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)).re)
  let T : ℝ → ℝ := fun s => (Matrix.trace
    ((1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z)).re
  let U : ℝ → ℝ := fun s => -(Matrix.trace
    ((1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z *
      (1 + (((s : ℝ) : ℂ)) • Z : ConcreteMatrixState N)⁻¹ * Z)).re
  have hfirst : deriv f =ᶠ[nhds 0] T := by
    simpa only [f, T] using
      h7_deriv_log_det_re_one_add_smul_eventuallyEq_trace Z hZ
  have hTderiv : deriv T =ᶠ[nhds 0] U := by
    filter_upwards [h7_one_add_smul_eventually_isUnit Z] with s hunit
    exact h7_deriv_re_trace_nonsingInv_mul Z s hunit
  have hsecond : iteratedDeriv 2 f =ᶠ[nhds 0] U := by
    filter_upwards [hfirst.deriv, hTderiv] with s hder hT
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one, hder, hT]
  change iteratedDeriv 3 f 0 = _
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ,
    hsecond.deriv_eq]
  change deriv U 0 = _
  rw [h7_deriv_neg_re_trace_nonsingInv_square Z 0 (by simp)]
  simp

/-- The scalar displacement on the inverse central congruence line. -/
def h7CentralScalarPath (t : ℝ) : ℝ := 1 - Real.exp (-4 * t)

@[simp]
theorem h7CentralScalarPath_zero : h7CentralScalarPath 0 = 0 := by
  simp [h7CentralScalarPath]

/-- The input-side support resolvent is Hermitian. -/
theorem h7CentralInputKernel_isHermitian
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h7CentralInputKernel K A).IsHermitian := by
  let C := unscaleCOECorner K A
  let B : ConcreteMatrixState N := C.conjTranspose * C
  let H : ConcreteMatrixState N := 1 - B
  have hB : B.IsHermitian := by
    exact Matrix.isHermitian_conjTranspose_mul_self C
  have hH : H.IsHermitian := Matrix.isHermitian_one.sub hB
  have hunit : IsUnit H := by
    simpa only [H, B, C] using hsupport.isUnit
  have hcommHB : Commute H B := by
    change H * B = B * H
    unfold H
    noncomm_ring
  have hinvEq : H⁻¹ = (↑(hunit.unit⁻¹) : ConcreteMatrixState N) := by
    calc
      H⁻¹ = Ring.inverse H := nonsing_inv_eq_ringInverse _
      _ = Ring.inverse (hunit.unit : ConcreteMatrixState N) :=
        congrArg Ring.inverse hunit.unit_spec.symm
      _ = (↑(hunit.unit⁻¹) : ConcreteMatrixState N) := Ring.inverse_unit _
  have hcommInvB : Commute H⁻¹ B := by
    rw [hinvEq]
    apply Commute.units_inv_left
    simpa only [hunit.unit_spec] using hcommHB
  unfold h7CentralInputKernel
  dsimp only
  change (H⁻¹ * B).IsHermitian
  exact (hH.inv.commute_iff hB).mp hcommInvB

/-- Cyclic trace transfer from the input resolvent to the literal output `Z`. -/
theorem h7CentralInputKernel_trace_eq_concreteCOEZ
    {N K : ℕ} (A : ConcreteMatrixState N) :
    Matrix.trace (h7CentralInputKernel K A) =
      Matrix.trace (concreteCOEZ K A) := by
  let C := unscaleCOECorner K A
  let J : ConcreteMatrixState N := (1 - C.conjTranspose * C)⁻¹
  unfold h7CentralInputKernel concreteCOEZ
  dsimp only
  change Matrix.trace (J * (C.conjTranspose * C)) =
    Matrix.trace (C * J * C.conjTranspose)
  calc
    Matrix.trace (J * (C.conjTranspose * C)) =
        Matrix.trace ((J * C.conjTranspose) * C) := by
          congr 1
          noncomm_ring
    _ = Matrix.trace (C * (J * C.conjTranspose)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (C * J * C.conjTranspose) := by
      congr 1
      noncomm_ring

/-- Cyclic transfer of the squared input resolvent trace. -/
theorem h7CentralInputKernel_sq_trace_eq_concreteCOEZ_sq
    {N K : ℕ} (A : ConcreteMatrixState N) :
    Matrix.trace (h7CentralInputKernel K A * h7CentralInputKernel K A) =
      Matrix.trace (concreteCOEZ K A * concreteCOEZ K A) := by
  let C := unscaleCOECorner K A
  let J : ConcreteMatrixState N := (1 - C.conjTranspose * C)⁻¹
  unfold h7CentralInputKernel concreteCOEZ
  dsimp only
  change Matrix.trace ((J * (C.conjTranspose * C)) *
      (J * (C.conjTranspose * C))) =
    Matrix.trace ((C * J * C.conjTranspose) *
      (C * J * C.conjTranspose))
  calc
    Matrix.trace ((J * (C.conjTranspose * C)) *
        (J * (C.conjTranspose * C))) =
        Matrix.trace ((J * C.conjTranspose * C * J * C.conjTranspose) * C) := by
          congr 1
          noncomm_ring
    _ = Matrix.trace (C * (J * C.conjTranspose * C * J * C.conjTranspose)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((C * J * C.conjTranspose) *
        (C * J * C.conjTranspose)) := by
          congr 1
          noncomm_ring

/-- Cyclic transfer of the cubed input resolvent trace. -/
theorem h7CentralInputKernel_cube_trace_eq_concreteCOEZ_cube
    {N K : ℕ} (A : ConcreteMatrixState N) :
    Matrix.trace
        (h7CentralInputKernel K A * h7CentralInputKernel K A *
          h7CentralInputKernel K A) =
      Matrix.trace
        (concreteCOEZ K A * concreteCOEZ K A * concreteCOEZ K A) := by
  let C := unscaleCOECorner K A
  let J : ConcreteMatrixState N := (1 - C.conjTranspose * C)⁻¹
  unfold h7CentralInputKernel concreteCOEZ
  dsimp only
  change Matrix.trace
      ((J * (C.conjTranspose * C)) * (J * (C.conjTranspose * C)) *
        (J * (C.conjTranspose * C))) =
    Matrix.trace
      ((C * J * C.conjTranspose) * (C * J * C.conjTranspose) *
        (C * J * C.conjTranspose))
  calc
    Matrix.trace
        ((J * (C.conjTranspose * C)) * (J * (C.conjTranspose * C)) *
          (J * (C.conjTranspose * C))) =
        Matrix.trace
          ((J * C.conjTranspose * C * J * C.conjTranspose * C * J *
            C.conjTranspose) * C) := by
              congr 1
              noncomm_ring
    _ = Matrix.trace
        (C * (J * C.conjTranspose * C * J * C.conjTranspose * C * J *
          C.conjTranspose)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        ((C * J * C.conjTranspose) * (C * J * C.conjTranspose) *
          (C * J * C.conjTranspose)) := by
            congr 1
            noncomm_ring

/-- The normalized literal determinant is exactly the identity-line
determinant of the input resolvent kernel. -/
theorem h7CentralInverseDeterminant_div_base_eq_inputKernel
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) (t : ℝ) :
    h7CentralInverseDeterminant K A t /
        concreteCOEBaseDeterminant K A =
      (Matrix.det
        (1 + (((h7CentralScalarPath t : ℝ) : ℂ)) •
          h7CentralInputKernel K A : ConcreteMatrixState N)).re := by
  let C := unscaleCOECorner K A
  let B : ConcreteMatrixState N := C.conjTranspose * C
  let H : ConcreteMatrixState N := 1 - B
  let R : ConcreteMatrixState N := H⁻¹ * B
  have hunit : IsUnit H := by
    simpa only [H, B, C] using hsupport.isUnit
  letI : Invertible H := hunit.invertible
  have hfactor :
      H * (1 + (((h7CentralScalarPath t : ℝ) : ℂ)) • R) =
        1 - (((Real.exp (-4 * t) : ℝ) : ℂ)) • B := by
    unfold R h7CentralScalarPath
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_inv_of_invertible, Matrix.one_mul]
    module
  have hdetEq :
      Matrix.det H * Matrix.det
          (1 + (((h7CentralScalarPath t : ℝ) : ℂ)) • R) =
        Matrix.det
          (1 - (((Real.exp (-4 * t) : ℝ) : ℂ)) • B) := by
    rw [← Matrix.det_mul, hfactor]
  have hHherm : H.IsHermitian := by
    exact Matrix.isHermitian_one.sub
      (Matrix.isHermitian_conjTranspose_mul_self C)
  have hRherm : R.IsHermitian := by
    change (h7CentralInputKernel K A).IsHermitian
    exact h7CentralInputKernel_isHermitian A hsupport
  have hFherm :
      (1 + (((h7CentralScalarPath t : ℝ) : ℂ)) • R :
        ConcreteMatrixState N).IsHermitian :=
    h7_one_add_real_smul_isHermitian R hRherm (h7CentralScalarPath t)
  have hHim := h7_det_im_eq_zero_of_isHermitian H hHherm
  have hFim := h7_det_im_eq_zero_of_isHermitian _ hFherm
  have hreEq := congrArg Complex.re hdetEq
  rw [Complex.mul_re, hHim, hFim] at hreEq
  simp only [mul_zero, zero_mul, sub_zero] at hreEq
  have hbase : (Matrix.det H).re ≠ 0 := by
    exact ((RCLike.lt_iff_re_im.mp hsupport.det_pos).1).ne'
  unfold h7CentralInverseDeterminant concreteCOEBaseDeterminant
  dsimp only
  change (Matrix.det
      (1 - (((Real.exp (-4 * t) : ℝ) : ℂ)) • B)).re /
      (Matrix.det H).re = _
  rw [← hreEq]
  exact mul_div_cancel_left₀ _ hbase

theorem h7CentralScalarPath_jet_one :
    iteratedDeriv 1 h7CentralScalarPath 0 = 4 := by
  unfold h7CentralScalarPath
  calc
    iteratedDeriv 1 (fun t : ℝ => 1 - Real.exp (-4 * t)) 0 =
        iteratedDeriv 1 (fun t : ℝ => -Real.exp (-4 * t)) 0 :=
      iteratedDeriv_const_sub (n := 1) (x := (0 : ℝ)) (by norm_num) 1
    _ = -iteratedDeriv 1 (fun t : ℝ => Real.exp (-4 * t)) 0 := by
      exact iteratedDeriv_fun_neg 1 _ 0
    _ = 4 := by
      rw [congrFun (iteratedDeriv_exp_const_mul 1 (-4)) 0]
      norm_num

theorem h7CentralScalarPath_jet_two :
    iteratedDeriv 2 h7CentralScalarPath 0 = -16 := by
  unfold h7CentralScalarPath
  calc
    iteratedDeriv 2 (fun t : ℝ => 1 - Real.exp (-4 * t)) 0 =
        iteratedDeriv 2 (fun t : ℝ => -Real.exp (-4 * t)) 0 :=
      iteratedDeriv_const_sub (n := 2) (x := (0 : ℝ)) (by norm_num) 1
    _ = -iteratedDeriv 2 (fun t : ℝ => Real.exp (-4 * t)) 0 := by
      exact iteratedDeriv_fun_neg 2 _ 0
    _ = -16 := by
      rw [congrFun (iteratedDeriv_exp_const_mul 2 (-4)) 0]
      norm_num

theorem h7CentralScalarPath_jet_three :
    iteratedDeriv 3 h7CentralScalarPath 0 = 64 := by
  unfold h7CentralScalarPath
  calc
    iteratedDeriv 3 (fun t : ℝ => 1 - Real.exp (-4 * t)) 0 =
        iteratedDeriv 3 (fun t : ℝ => -Real.exp (-4 * t)) 0 :=
      iteratedDeriv_const_sub (n := 3) (x := (0 : ℝ)) (by norm_num) 1
    _ = -iteratedDeriv 3 (fun t : ℝ => Real.exp (-4 * t)) 0 := by
      exact iteratedDeriv_fun_neg 3 _ 0
    _ = 64 := by
      rw [congrFun (iteratedDeriv_exp_const_mul 3 (-4)) 0]
      norm_num

private theorem h7CentralScalarPath_contDiffAt_three :
    ContDiffAt ℝ 3 h7CentralScalarPath 0 := by
  unfold h7CentralScalarPath
  fun_prop

/-- The second output-resolvent trace in the `Y=cZ` normalization. -/
theorem concreteCOEZ_sq_trace_re_eq_traceTwo_div
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0) :
    (Matrix.trace (concreteCOEZ K A * concreteCOEZ K A)).re =
      concreteCOETraceTwo N K A / concreteCOEExponent N K ^ 2 := by
  have ht : concreteCOETraceTwo N K A =
      concreteCOEExponent N K ^ 2 *
        (Matrix.trace (concreteCOEZ K A * concreteCOEZ K A)).re := by
    simp only [concreteCOETraceTwo, concreteRealTrace, concreteCOEY,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    ring
  rw [ht]
  field_simp [hc]

/-- The first trace normalization needed by the H7 determinant jets.

This elementary identity is kept next to the jets so the hiding release does
not import the broader historical cubic-identification branch merely for a
one-line scalar rearrangement. -/
theorem concreteCOEZ_trace_re_eq_traceOne_div_h7
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0) :
    (Matrix.trace (concreteCOEZ K A)).re =
      concreteCOETraceOne N K A / concreteCOEExponent N K := by
  have ht1 : concreteCOETraceOne N K A =
      concreteCOEExponent N K *
        (Matrix.trace (concreteCOEZ K A)).re := by
    simp only [concreteCOETraceOne, concreteRealTrace, concreteCOEY,
      Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [ht1]
  field_simp [hc]

/-- The third output-resolvent trace in the `Y=cZ` normalization. -/
theorem concreteCOEZ_cube_trace_re_eq_traceThree_div
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0) :
    (Matrix.trace
      (concreteCOEZ K A * concreteCOEZ K A * concreteCOEZ K A)).re =
      concreteCOETraceThree N K A / concreteCOEExponent N K ^ 3 := by
  have ht : concreteCOETraceThree N K A =
      concreteCOEExponent N K ^ 3 *
        (Matrix.trace
          (concreteCOEZ K A * concreteCOEZ K A * concreteCOEZ K A)).re := by
    simp only [concreteCOETraceThree, concreteRealTrace, concreteCOEY,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    ring
  rw [ht]
  field_simp [hc]

/-- Exact function-level factorization of the central normalized log
determinant through the input resolvent kernel. -/
theorem h7CentralLogDeterminantRatio_eq_inputKernel_comp
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    h7CentralLogDeterminantRatio K A =
      (fun s : ℝ => Real.log ((Matrix.det
        (1 + (((s : ℝ) : ℂ)) • h7CentralInputKernel K A :
          ConcreteMatrixState N)).re)) ∘ h7CentralScalarPath := by
  funext t
  unfold h7CentralLogDeterminantRatio Function.comp
  rw [h7CentralInverseDeterminant_div_base_eq_inputKernel A hsupport t]

private theorem h7_inputKernel_logdet_contDiffAt_three
    {N K : ℕ} (A : ConcreteMatrixState N) :
    ContDiffAt ℝ 3
      (fun s : ℝ => Real.log ((Matrix.det
        (1 + (((s : ℝ) : ℂ)) • h7CentralInputKernel K A :
          ConcreteMatrixState N)).re)) 0 := by
  apply ((h7_det_re_one_add_smul_contDiff
    (h7CentralInputKernel K A)).contDiffAt.of_le (by norm_num)).log
  simp

/-- First unconditional trace jet of the literal central log determinant. -/
theorem h7CentralLogDeterminantRatio_jet_one
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hc : concreteCOEExponent N K ≠ 0) :
    iteratedDeriv 1 (h7CentralLogDeterminantRatio K A) 0 =
      4 * concreteCOETraceOne N K A / concreteCOEExponent N K := by
  let R := h7CentralInputKernel K A
  let g : ℝ → ℝ := fun s => Real.log ((Matrix.det
    (1 + (((s : ℝ) : ℂ)) • R : ConcreteMatrixState N)).re)
  have hR : R.IsHermitian := by
    exact h7CentralInputKernel_isHermitian A hsupport
  have hg : ContDiffAt ℝ 3 g 0 := by
    exact h7_inputKernel_logdet_contDiffAt_three A
  have hg1 : deriv g 0 = (Matrix.trace R).re := by
    simpa only [iteratedDeriv_one] using
      h7_iteratedDeriv_one_log_det_re_one_add_smul R hR
  have hs1 : deriv h7CentralScalarPath 0 = 4 := by
    simpa only [iteratedDeriv_one] using h7CentralScalarPath_jet_one
  have hcomp : HasDerivAt (g ∘ h7CentralScalarPath)
      ((Matrix.trace R).re * 4) 0 := by
    have hgHas : HasDerivAt g (Matrix.trace R).re 0 := by
      rw [← hg1]
      exact (hg.differentiableAt (by norm_num)).hasDerivAt
    have hsHas : HasDerivAt h7CentralScalarPath 4 0 := by
      rw [← hs1]
      exact (h7CentralScalarPath_contDiffAt_three.differentiableAt
        (by norm_num)).hasDerivAt
    have hgHas' : HasDerivAt g (Matrix.trace R).re
        (h7CentralScalarPath 0) := by simpa using hgHas
    exact hgHas'.comp 0 hsHas
  rw [h7CentralLogDeterminantRatio_eq_inputKernel_comp A hsupport,
    iteratedDeriv_one, hcomp.deriv]
  have htrace : (Matrix.trace R).re =
      (Matrix.trace (concreteCOEZ K A)).re := by
    simpa only [R] using congrArg Complex.re
      (h7CentralInputKernel_trace_eq_concreteCOEZ A)
  rw [htrace, concreteCOEZ_trace_re_eq_traceOne_div_h7 A hc]
  ring

/-- Second unconditional trace jet of the literal central log determinant. -/
theorem h7CentralLogDeterminantRatio_jet_two
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hc : concreteCOEExponent N K ≠ 0) :
    iteratedDeriv 2 (h7CentralLogDeterminantRatio K A) 0 =
      -16 * (concreteCOETraceOne N K A / concreteCOEExponent N K +
        concreteCOETraceTwo N K A / concreteCOEExponent N K ^ 2) := by
  let R := h7CentralInputKernel K A
  let g : ℝ → ℝ := fun s => Real.log ((Matrix.det
    (1 + (((s : ℝ) : ℂ)) • R : ConcreteMatrixState N)).re)
  have hR : R.IsHermitian := h7CentralInputKernel_isHermitian A hsupport
  have hg : ContDiffAt ℝ 2 g 0 :=
    (h7_inputKernel_logdet_contDiffAt_three A).of_le (by norm_num)
  have hs : ContDiffAt ℝ 2 h7CentralScalarPath 0 :=
    h7CentralScalarPath_contDiffAt_three.of_le (by norm_num)
  have hg' : ContDiffAt ℝ 2 g (h7CentralScalarPath 0) := by
    simpa using hg
  have hg1 : deriv g 0 = (Matrix.trace R).re := by
    simpa only [iteratedDeriv_one] using
      h7_iteratedDeriv_one_log_det_re_one_add_smul R hR
  have hs1 : deriv h7CentralScalarPath 0 = 4 := by
    simpa only [iteratedDeriv_one] using h7CentralScalarPath_jet_one
  rw [show h7CentralLogDeterminantRatio K A =
      g ∘ h7CentralScalarPath by
        simpa only [g, R] using
          h7CentralLogDeterminantRatio_eq_inputKernel_comp A hsupport,
    iteratedDeriv_comp_two hg' hs, h7CentralScalarPath_zero,
    h7_iteratedDeriv_two_log_det_re_one_add_smul R hR, hg1, hs1,
    h7CentralScalarPath_jet_two]
  have htrace1 : (Matrix.trace R).re =
      (Matrix.trace (concreteCOEZ K A)).re := by
    simpa only [R] using congrArg Complex.re
      (h7CentralInputKernel_trace_eq_concreteCOEZ A)
  have htrace2 : (Matrix.trace (R * R)).re =
      (Matrix.trace (concreteCOEZ K A * concreteCOEZ K A)).re := by
    simpa only [R] using congrArg Complex.re
      (h7CentralInputKernel_sq_trace_eq_concreteCOEZ_sq A)
  rw [htrace1, htrace2, concreteCOEZ_trace_re_eq_traceOne_div_h7 A hc,
    concreteCOEZ_sq_trace_re_eq_traceTwo_div A hc]
  ring

/-- Third unconditional trace jet of the literal central log determinant. -/
theorem h7CentralLogDeterminantRatio_jet_three
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A))
    (hc : concreteCOEExponent N K ≠ 0) :
    iteratedDeriv 3 (h7CentralLogDeterminantRatio K A) 0 =
      64 * (concreteCOETraceOne N K A / concreteCOEExponent N K +
        3 * concreteCOETraceTwo N K A / concreteCOEExponent N K ^ 2 +
        2 * concreteCOETraceThree N K A / concreteCOEExponent N K ^ 3) := by
  let R := h7CentralInputKernel K A
  let g : ℝ → ℝ := fun s => Real.log ((Matrix.det
    (1 + (((s : ℝ) : ℂ)) • R : ConcreteMatrixState N)).re)
  have hR : R.IsHermitian := h7CentralInputKernel_isHermitian A hsupport
  have hg : ContDiffAt ℝ 3 g 0 := h7_inputKernel_logdet_contDiffAt_three A
  have hs : ContDiffAt ℝ 3 h7CentralScalarPath 0 :=
    h7CentralScalarPath_contDiffAt_three
  have hg' : ContDiffAt ℝ 3 g (h7CentralScalarPath 0) := by
    simpa using hg
  have hg1 : deriv g 0 = (Matrix.trace R).re := by
    simpa only [iteratedDeriv_one] using
      h7_iteratedDeriv_one_log_det_re_one_add_smul R hR
  have hs1 : deriv h7CentralScalarPath 0 = 4 := by
    simpa only [iteratedDeriv_one] using h7CentralScalarPath_jet_one
  rw [show h7CentralLogDeterminantRatio K A =
      g ∘ h7CentralScalarPath by
        simpa only [g, R] using
          h7CentralLogDeterminantRatio_eq_inputKernel_comp A hsupport,
    iteratedDeriv_comp_three hg' hs, h7CentralScalarPath_zero,
    h7_iteratedDeriv_three_log_det_re_one_add_smul R hR,
    h7_iteratedDeriv_two_log_det_re_one_add_smul R hR,
    hg1, hs1, h7CentralScalarPath_jet_two, h7CentralScalarPath_jet_three]
  have htrace1 : (Matrix.trace R).re =
      (Matrix.trace (concreteCOEZ K A)).re := by
    simpa only [R] using congrArg Complex.re
      (h7CentralInputKernel_trace_eq_concreteCOEZ A)
  have htrace2 : (Matrix.trace (R * R)).re =
      (Matrix.trace (concreteCOEZ K A * concreteCOEZ K A)).re := by
    simpa only [R] using congrArg Complex.re
      (h7CentralInputKernel_sq_trace_eq_concreteCOEZ_sq A)
  have htrace3 : (Matrix.trace (R * R * R)).re =
      (Matrix.trace
        (concreteCOEZ K A * concreteCOEZ K A * concreteCOEZ K A)).re := by
    simpa only [R] using congrArg Complex.re
      (h7CentralInputKernel_cube_trace_eq_concreteCOEZ_cube A)
  rw [htrace1, htrace2, htrace3,
    concreteCOEZ_trace_re_eq_traceOne_div_h7 A hc,
    concreteCOEZ_sq_trace_re_eq_traceTwo_div A hc,
    concreteCOEZ_cube_trace_re_eq_traceThree_div A hc]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
