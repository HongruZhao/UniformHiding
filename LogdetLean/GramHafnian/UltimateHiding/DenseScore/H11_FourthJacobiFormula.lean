import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_BlockFourthTraceReduction
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic

/-!
# Fourth Jacobi formula for a finite matrix path

This file supplies the analytic identity which is implicit in the algebraic
definition `h11BlockFourthJacobiMatrix`.  For a four-times differentiable
Hermitian path `F`, it differentiates `log (det F).re` four times, using only
the finite Leibniz formula for the determinant and the derivative of inversion
in a normed algebra.

The final specialization records the coefficient convention for a path whose
jets at the base point are `2^k E^k`: `16,-64,-48,192,-96`.
-/

open Function Matrix Polynomial
open scoped Matrix Topology ComplexConjugate ComplexOrder BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

/-! ## Finite matrix calculus instances -/

local instance h11JacobiMatrixNormedAddCommGroup
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NormedAddCommGroup (Matrix ι ι ℂ) :=
  Matrix.linftyOpNormedAddCommGroup

local instance h11JacobiMatrixNormedRing
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NormedRing (Matrix ι ι ℂ) :=
  { Matrix.linftyOpNormedRing with
    toAddCommGroup := h11JacobiMatrixNormedAddCommGroup.toAddCommGroup }

local instance h11JacobiMatrixComplexNormedSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NormedSpace ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedSpace

local instance h11JacobiMatrixRealNormedSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NormedSpace ℝ (Matrix ι ι ℂ) := Matrix.linftyOpNormedSpace

local instance h11JacobiMatrixAddCommGroup
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    AddCommGroup (Matrix ι ι ℂ) :=
  h11JacobiMatrixNormedAddCommGroup.toAddCommGroup

local instance h11JacobiMatrixComplexModule
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Module ℂ (Matrix ι ι ℂ) := h11JacobiMatrixComplexNormedSpace.toModule

local instance h11JacobiMatrixRealModule
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Module ℝ (Matrix ι ι ℂ) := h11JacobiMatrixRealNormedSpace.toModule

local instance h11JacobiMatrixPseudoMetricSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    PseudoMetricSpace (Matrix ι ι ℂ) :=
  h11JacobiMatrixNormedAddCommGroup.toPseudoMetricSpace

local instance h11JacobiMatrixUniformSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    UniformSpace (Matrix ι ι ℂ) :=
  h11JacobiMatrixPseudoMetricSpace.toUniformSpace

local instance h11JacobiMatrixTopologicalSpace
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    TopologicalSpace (Matrix ι ι ℂ) :=
  h11JacobiMatrixUniformSpace.toTopologicalSpace

local instance h11JacobiMatrixComplexNormedAlgebra
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NormedAlgebra ℂ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra

local instance h11JacobiMatrixRealNormedAlgebra
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    NormedAlgebra ℝ (Matrix ι ι ℂ) := Matrix.linftyOpNormedAlgebra

private def h11JacobiMatrixEntryLinearMap
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    Matrix ι ι ℂ →ₗ[ℝ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def h11JacobiMatrixEntryCLM
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    Matrix ι ι ℂ →L[ℝ] ℂ :=
  (h11JacobiMatrixEntryLinearMap i j).toContinuousLinearMap

private def h11JacobiTraceCLM
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] ℂ :=
  (Matrix.traceLinearMap ι ℝ ℂ).toContinuousLinearMap

private def h11JacobiReTraceCLM
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    Matrix ι ι ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (h11JacobiTraceCLM ι)

@[simp] private theorem h11JacobiReTraceCLM_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    h11JacobiReTraceCLM ι M = (Matrix.trace M).re := rfl

/-! ## First Jacobi formula and inverse derivative -/

private theorem h11_perm_erase_prod_one_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sigma : Equiv.Perm ι) (i : ι) :
    ∏ j ∈ Finset.univ.erase i,
        (1 : Matrix ι ι ℂ) (sigma j) j =
      if sigma = 1 then 1 else 0 := by
  classical
  by_cases hsigma : sigma = 1
  · subst sigma
    simp [Matrix.one_apply]
  · rw [if_neg hsigma]
    have hmoved : ∃ j, sigma j ≠ j := by
      by_contra h
      push_neg at h
      apply hsigma
      ext j
      simpa using h j
    obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ sigma j ≠ j := by
      by_cases hi : sigma i = i
      · obtain ⟨j, hj⟩ := hmoved
        exact ⟨j, fun hji ↦ hj (hji.symm ▸ hi), hj⟩
      · refine ⟨sigma i, hi, ?_⟩
        intro heq
        exact hi (sigma.injective heq)
    refine Finset.prod_eq_zero
      (i := j) (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) ?_
    simp [Matrix.one_apply, hj]

private theorem h11_hasDerivAt_det_of_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ℝ → Matrix ι ι ℂ) (F' : Matrix ι ι ℂ) (x : ℝ)
    (hF : HasDerivAt F F' x) (hF0 : F x = 1) :
    HasDerivAt (fun t ↦ Matrix.det (F t)) (Matrix.trace F') x := by
  classical
  have hentry (i j : ι) :
      HasDerivAt (fun t ↦ F t i j) (F' i j) x := by
    convert (h11JacobiMatrixEntryCLM i j).hasFDerivAt.comp_hasDerivAt x hF
      using 1 <;>
      first
      | rfl
      | exact Subsingleton.elim _ _
  rw [show (fun t ↦ Matrix.det (F t)) =
      fun t ↦ ∑ sigma : Equiv.Perm ι,
        Equiv.Perm.sign sigma • ∏ i, F t (sigma i) i by
    funext t
    exact Matrix.det_apply (F t)]
  have hprod : ∀ sigma : Equiv.Perm ι,
      HasDerivAt (fun t ↦ ∏ i, F t (sigma i) i)
        (∑ i, (∏ j ∈ Finset.univ.erase i, F x (sigma j) j) *
          F' (sigma i) i) x := by
    intro sigma
    simpa only [smul_eq_mul] using
      (HasDerivAt.fun_finsetProd (u := Finset.univ)
        (f := fun i t ↦ F t (sigma i) i)
        (f' := fun i ↦ F' (sigma i) i)
        (fun i _ ↦ hentry (sigma i) i))
  have hsum : HasDerivAt
      (fun t ↦ ∑ sigma : Equiv.Perm ι,
        Equiv.Perm.sign sigma • ∏ i, F t (sigma i) i)
      (∑ sigma : Equiv.Perm ι,
        Equiv.Perm.sign sigma •
          ∑ i, (∏ j ∈ Finset.univ.erase i, F x (sigma j) j) *
            F' (sigma i) i) x := by
    apply HasDerivAt.fun_sum
    intro sigma _
    exact (hprod sigma).const_smul (Equiv.Perm.sign sigma)
  convert hsum using 1
  rw [hF0]
  simp_rw [h11_perm_erase_prod_one_apply]
  rw [Finset.sum_eq_single 1]
  · simp [Matrix.trace]
  · intro sigma _ hsigma
    simp [hsigma]
  · simp

/-- Jacobi's first formula for a real-parameter finite complex matrix path. -/
theorem h11_hasDerivAt_det_matrix_path_of_isUnit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ℝ → Matrix ι ι ℂ) (F' : Matrix ι ι ℂ) (x : ℝ)
    (hF : HasDerivAt F F' x) (hunit : IsUnit (F x)) :
    HasDerivAt (fun t ↦ Matrix.det (F t))
      (Matrix.det (F x) * Matrix.trace ((F x)⁻¹ * F')) x := by
  let G : ℝ → Matrix ι ι ℂ := fun t ↦ (F x)⁻¹ * F t
  have hdetUnit : IsUnit (Matrix.det (F x)) :=
    (Matrix.isUnit_iff_isUnit_det (F x)).mp hunit
  have hG : HasDerivAt G ((F x)⁻¹ * F') x := by
    simpa only [G] using hF.const_mul ((F x)⁻¹)
  have hGx : G x = 1 := by
    dsimp [G]
    exact Matrix.nonsing_inv_mul _ hdetUnit
  have hdetG : HasDerivAt (fun t ↦ Matrix.det (G t))
      (Matrix.trace ((F x)⁻¹ * F')) x :=
    h11_hasDerivAt_det_of_eq_one G ((F x)⁻¹ * F') x hG hGx
  have hfactor : (fun t ↦ Matrix.det (F t)) =
      fun t ↦ Matrix.det (F x) * Matrix.det (G t) := by
    funext t
    have hmul : F x * G t = F t := by
      dsimp [G]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetUnit,
        Matrix.one_mul]
    rw [← hmul, Matrix.det_mul]
  rw [hfactor]
  exact hdetG.const_mul _

private theorem h11_hasDerivAt_nonsingInv_matrix_path
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ℝ → Matrix ι ι ℂ) (F' : Matrix ι ι ℂ) (x : ℝ)
    (hF : HasDerivAt F F' x) (hunit : IsUnit (F x)) :
    HasDerivAt (fun t ↦ (F t)⁻¹)
      (-((F x)⁻¹ * F' * (F x)⁻¹)) x := by
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) hunit.unit
  have hcomp := hinv.comp_hasDerivAt x hF
  have hinvEq :
      (F x)⁻¹ = (↑(hunit.unit⁻¹) : Matrix ι ι ℂ) := by
    calc
      (F x)⁻¹ = Ring.inverse (F x) := nonsing_inv_eq_ringInverse _
      _ = Ring.inverse (hunit.unit : Matrix ι ι ℂ) :=
        congrArg Ring.inverse hunit.unit_spec.symm
      _ = (↑(hunit.unit⁻¹) : Matrix ι ι ℂ) := Ring.inverse_unit _
  convert hcomp using 1 <;> try rfl
  · funext t
    simp only [Function.comp_apply, nonsing_inv_eq_ringInverse]
  · simp only [ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.mulLeftRight_apply]
    rw [← hinvEq]

/-! ## The order-four trace polynomial -/

/-- General fourth Jacobi trace polynomial for path jets `A,B,C,D`. -/
def h11FourthJacobiMatrixGeneral
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W A B C D : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  W * D -
    (4 : ℂ) • (W * A * W * C) -
    (3 : ℂ) • (W * B * W * B) +
    (12 : ℂ) • (W * A * W * A * W * B) -
    (6 : ℂ) • ((W * A) ^ 4)

private theorem h11_trace_cycle_BAA
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W A B : Matrix ι ι ℂ) :
    Matrix.trace (W * B * W * A * W * A) =
      Matrix.trace (W * A * W * A * W * B) := by
  calc
    Matrix.trace (W * B * W * A * W * A) =
        Matrix.trace ((W * B) * (W * A * W * A)) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((W * A * W * A) * (W * B)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (W * A * W * A * W * B) := by
      simp only [Matrix.mul_assoc]

private theorem h11_fourth_raw_trace_eq_general
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W A B C D : Matrix ι ι ℂ) :
    (Matrix.trace ((-(W * A * W)) * C + W * D)).re -
        3 * (Matrix.trace
          ((((-(W * A * W)) * A + W * B) * W +
              W * A * (-(W * A * W))) * B +
            W * A * W * C)).re +
        2 * (Matrix.trace
          ((((-(W * A * W)) * A + W * B) * (W * A) +
              (W * A) * (-(W * A * W) * A + W * B)) * (W * A) +
            (W * A) * (W * A) *
              (-(W * A * W) * A + W * B))).re =
      (Matrix.trace (h11FourthJacobiMatrixGeneral W A B C D)).re := by
  let K : Matrix ι ι ℂ := W * A
  have htermOne :
      (-(W * A * W)) * C + W * D =
        -(W * A * W * C) + W * D := by
    noncomm_ring
  have htermTwo :
      ((((-(W * A * W)) * A + W * B) * W +
          W * A * (-(W * A * W))) * B + W * A * W * C) =
        -((2 : ℂ) • (W * A * W * A * W * B)) +
          W * B * W * B + W * A * W * C := by
    noncomm_ring
    module
  have htermThree :
      ((((-(W * A * W)) * A + W * B) * (W * A) +
          (W * A) * (-(W * A * W) * A + W * B)) * (W * A) +
        (W * A) * (W * A) * (-(W * A * W) * A + W * B)) =
        -((3 : ℂ) • (K ^ 4)) +
          (W * B * K * K + K * W * B * K + K * K * W * B) := by
    simp only [K, pow_succ, pow_zero, Matrix.one_mul]
    noncomm_ring
    module
  have hcycleOne : Matrix.trace (W * B * K * K) =
      Matrix.trace (K * K * W * B) := by
    calc
      Matrix.trace (W * B * K * K) =
          Matrix.trace ((W * B) * (K * K)) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((K * K) * (W * B)) :=
        Matrix.trace_mul_comm _ _
      _ = Matrix.trace (K * K * W * B) := by
        simp only [Matrix.mul_assoc]
  have hcycleTwo : Matrix.trace (K * W * B * K) =
      Matrix.trace (K * K * W * B) := by
    calc
      Matrix.trace (K * W * B * K) =
          Matrix.trace ((K * W * B) * K) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (K * (K * W * B)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (K * K * W * B) := by
        simp only [Matrix.mul_assoc]
  rw [htermOne, htermTwo, htermThree]
  simp only [Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul,
    Complex.add_re, Complex.neg_re]
  rw [hcycleOne, hcycleTwo]
  simp only [K, h11FourthJacobiMatrixGeneral, Matrix.trace_sub,
    Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    Complex.sub_re, Complex.add_re]
  norm_num [Complex.mul_re]
  simp only [Matrix.mul_assoc]
  ring

/-- Fourth Jacobi formula for a locally positive Hermitian matrix path.

The four matrix-valued derivative hypotheses are local, which is exactly what
is needed by `iteratedDeriv`.  No commutativity between the four jets is
assumed. -/
theorem h11_iteratedDeriv_four_log_det_re_of_matrix_four_jet
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F F₁ F₂ F₃ F₄ : ℝ → Matrix ι ι ℂ) (x : ℝ)
    (hjet : ∀ᶠ y in nhds x,
      HasDerivAt F (F₁ y) y ∧
      HasDerivAt F₁ (F₂ y) y ∧
      HasDerivAt F₂ (F₃ y) y ∧
      HasDerivAt F₃ (F₄ y) y)
    (hHerm : ∀ᶠ y in nhds x, (F y).IsHermitian)
    (hpos : ∀ᶠ y in nhds x, 0 < (Matrix.det (F y)).re) :
    iteratedDeriv 4
        (fun t : ℝ ↦ Real.log (Matrix.det (F t)).re) x =
      (Matrix.trace
        (h11FourthJacobiMatrixGeneral (F x)⁻¹
          (F₁ x) (F₂ x) (F₃ x) (F₄ x))).re := by
  let J : ℝ → Matrix ι ι ℂ := fun y ↦ (F y)⁻¹
  let g : ℝ → ℝ := fun y ↦ Real.log (Matrix.det (F y)).re
  let g₁ : ℝ → ℝ := h11JacobiReTraceCLM ι ∘ (J * F₁)
  let g₂ : ℝ → ℝ :=
    -(h11JacobiReTraceCLM ι ∘ (J * F₁ * J * F₁)) +
      (h11JacobiReTraceCLM ι ∘ (J * F₂))
  let g₃ : ℝ → ℝ :=
    (h11JacobiReTraceCLM ι ∘ (J * F₃)) -
      (fun y ↦ 3 * (Matrix.trace (J y * F₁ y * J y * F₂ y)).re) +
      (fun y ↦ 2 * (Matrix.trace ((J y * F₁ y) ^ 3)).re)
  have hunit : ∀ᶠ y in nhds x, IsUnit (F y) := by
    filter_upwards [hpos] with y hy
    apply (Matrix.isUnit_iff_isUnit_det (F y)).2
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    rw [hzero] at hy
    norm_num at hy
  have hfirst : deriv g =ᶠ[nhds x] g₁ := by
    filter_upwards [hjet, hHerm, hpos, hunit] with y hyjet hyHerm hypos hyunit
    have hdet := h11_hasDerivAt_det_matrix_path_of_isUnit
      F (F₁ y) y hyjet.1 hyunit
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hdet
    have hlog := hre.log hypos.ne'
    have hd := hlog.deriv
    change deriv (fun t : ℝ ↦ Real.log (Matrix.det (F t)).re) y =
      ((Matrix.det (F y) * Matrix.trace ((F y)⁻¹ * F₁ y)).re) /
        (Matrix.det (F y)).re at hd
    change deriv (fun t : ℝ ↦ Real.log (Matrix.det (F t)).re) y =
      (Matrix.trace ((F y)⁻¹ * F₁ y)).re
    rw [hd]
    have hdetIm : (Matrix.det (F y)).im = 0 := by
      apply Complex.conj_eq_iff_im.mp
      have h := congrArg Matrix.det hyHerm.eq
      rw [Matrix.det_conjTranspose] at h
      exact h
    rw [Complex.mul_re, hdetIm]
    simp only [zero_mul, sub_zero]
    exact mul_div_cancel_left₀ _ hypos.ne'
  have hg₁ : deriv g₁ =ᶠ[nhds x] g₂ := by
    filter_upwards [hjet, hunit] with y hyjet hyunit
    have hJ : HasDerivAt J (-(J y * F₁ y * J y)) y := by
      simpa only [J] using
        h11_hasDerivAt_nonsingInv_matrix_path F (F₁ y) y hyjet.1 hyunit
    have hprod := hJ.mul hyjet.2.1
    have htrace :=
      (h11JacobiReTraceCLM ι).hasFDerivAt.comp_hasDerivAt y hprod
    have hmatrix :
        (-(J y * F₁ y * J y)) * F₁ y + J y * F₂ y =
          -(J y * F₁ y * J y * F₁ y) + J y * F₂ y := by
      noncomm_ring
    rw [hmatrix] at htrace
    simp only [g₁, g₂, Function.comp_apply, h11JacobiReTraceCLM_apply,
      Pi.mul_apply, Pi.add_apply, Pi.neg_apply]
    rw [htrace.deriv]
    change (Matrix.trace
      (-(J y * F₁ y * J y * F₁ y) + J y * F₂ y)).re = _
    rw [Matrix.trace_add, Matrix.trace_neg, Complex.add_re, Complex.neg_re]
  have hsecond : iteratedDeriv 2 g =ᶠ[nhds x] g₂ := by
    filter_upwards [hfirst.deriv, hg₁] with y hder hg
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one, hder, hg]
  have hg₂ : deriv g₂ =ᶠ[nhds x] g₃ := by
    filter_upwards [hjet, hunit] with y hyjet hyunit
    rcases hyjet with ⟨hF, hF₁, hF₂, hF₃⟩
    have hJ : HasDerivAt J (-(J y * F₁ y * J y)) y := by
      simpa only [J] using
        h11_hasDerivAt_nonsingInv_matrix_path F (F₁ y) y hF hyunit
    have hJAJA := ((hJ.mul hF₁).mul hJ).mul hF₁
    have hJB := hJ.mul hF₂
    have htrJAJA :=
      (h11JacobiReTraceCLM ι).hasFDerivAt.comp_hasDerivAt y hJAJA
    have htrJB :=
      (h11JacobiReTraceCLM ι).hasFDerivAt.comp_hasDerivAt y hJB
    have hraw : HasDerivAt g₂
        (-((Matrix.trace
          ((((-(J y * F₁ y * J y)) * F₁ y + J y * F₂ y) * J y +
              J y * F₁ y * (-(J y * F₁ y * J y))) * F₁ y +
            J y * F₁ y * J y * F₂ y)).re) +
          (Matrix.trace
            ((-(J y * F₁ y * J y)) * F₂ y + J y * F₃ y)).re) y := by
      simpa only [g₂, Function.comp_apply, h11JacobiReTraceCLM_apply,
        Pi.mul_apply, Pi.add_apply, Pi.neg_apply] using
        htrJAJA.neg.add htrJB
    have hcycle : Matrix.trace (J y * F₂ y * J y * F₁ y) =
        Matrix.trace (J y * F₁ y * J y * F₂ y) := by
      calc
        Matrix.trace (J y * F₂ y * J y * F₁ y) =
            Matrix.trace ((J y * F₂ y) * (J y * F₁ y)) := by
              simp only [Matrix.mul_assoc]
        _ = Matrix.trace ((J y * F₁ y) * (J y * F₂ y)) :=
          Matrix.trace_mul_comm _ _
        _ = Matrix.trace (J y * F₁ y * J y * F₂ y) := by
          simp only [Matrix.mul_assoc]
    have hvalue :
        -((Matrix.trace
          ((((-(J y * F₁ y * J y)) * F₁ y + J y * F₂ y) * J y +
              J y * F₁ y * (-(J y * F₁ y * J y))) * F₁ y +
            J y * F₁ y * J y * F₂ y)).re) +
          (Matrix.trace
            ((-(J y * F₁ y * J y)) * F₂ y + J y * F₃ y)).re =
        g₃ y := by
      simp only [g₃, Function.comp_apply, h11JacobiReTraceCLM_apply,
        Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
      have hpow : (J y * F₁ y) ^ 3 =
          J y * F₁ y * J y * F₁ y * J y * F₁ y := by
        simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.mul_assoc]
      rw [hpow]
      have hrawMatrix :
          ((((-(J y * F₁ y * J y)) * F₁ y + J y * F₂ y) * J y +
              J y * F₁ y * (-(J y * F₁ y * J y))) * F₁ y +
            J y * F₁ y * J y * F₂ y) =
          -((2 : ℂ) •
              (J y * F₁ y * J y * F₁ y * J y * F₁ y)) +
            (J y * F₂ y * J y * F₁ y) +
            (J y * F₁ y * J y * F₂ y) := by
        noncomm_ring
        module
      have htailMatrix :
          (-(J y * F₁ y * J y)) * F₂ y + J y * F₃ y =
            -(J y * F₁ y * J y * F₂ y) + J y * F₃ y := by
        noncomm_ring
      rw [hrawMatrix, htailMatrix]
      simp only [Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul,
        Complex.add_re, Complex.neg_re]
      rw [hcycle]
      norm_num [Complex.mul_re]
      ring
    rw [hraw.deriv, hvalue]
  have hthird : iteratedDeriv 3 g =ᶠ[nhds x] g₃ := by
    filter_upwards [hsecond.deriv, hg₂] with y hder hg
    rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ, hder, hg]
  rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ,
    hthird.deriv_eq]
  have hxjet := mem_of_mem_nhds hjet
  have hxunit := mem_of_mem_nhds hunit
  rcases hxjet with ⟨hF, hF₁, hF₂, hF₃⟩
  have hJ : HasDerivAt J (-(J x * F₁ x * J x)) x := by
    simpa only [J] using
      h11_hasDerivAt_nonsingInv_matrix_path F (F₁ x) x hF hxunit
  have hterm₁ := hJ.mul hF₃
  have hterm₂ := ((hJ.mul hF₁).mul hJ).mul hF₂
  let K : ℝ → Matrix ι ι ℂ := J * F₁
  have hK : HasDerivAt K
      (-(J x * F₁ x * J x) * F₁ x + J x * F₂ x) x := by
    simpa only [K] using hJ.mul hF₁
  have hKcube := ((hK.mul hK).mul hK)
  have htr₁ :=
    (h11JacobiReTraceCLM ι).hasFDerivAt.comp_hasDerivAt x hterm₁
  have htr₂ :=
    (h11JacobiReTraceCLM ι).hasFDerivAt.comp_hasDerivAt x hterm₂
  have htrCube :=
    (h11JacobiReTraceCLM ι).hasFDerivAt.comp_hasDerivAt x hKcube
  have hderivRaw : HasDerivAt g₃
      ((Matrix.trace
          ((-(J x * F₁ x * J x)) * F₃ x + J x * F₄ x)).re -
        3 * (Matrix.trace
          ((((-(J x * F₁ x * J x)) * F₁ x + J x * F₂ x) * J x +
              J x * F₁ x * (-(J x * F₁ x * J x))) * F₂ x +
            J x * F₁ x * J x * F₃ x)).re +
        2 * (Matrix.trace
          ((((-(J x * F₁ x * J x)) * F₁ x + J x * F₂ x) * K x +
              K x * (-(J x * F₁ x * J x) * F₁ x + J x * F₂ x)) * K x +
            K x * K x *
              (-(J x * F₁ x * J x) * F₁ x + J x * F₂ x))).re) x := by
    simpa only [g₃, Function.comp_apply, h11JacobiReTraceCLM_apply,
      Pi.mul_apply, Pi.add_apply, Pi.sub_apply, K, pow_succ, pow_zero,
      Matrix.one_mul] using
      (htr₁.sub (htr₂.const_mul 3) |>.add (htrCube.const_mul 2))
  rw [hderivRaw.deriv]
  simpa only [J, K, Pi.mul_apply] using
    h11_fourth_raw_trace_eq_general
      (F x)⁻¹ (F₁ x) (F₂ x) (F₃ x) (F₄ x)

/-! ## Coefficient specialization -/

/-- The general fourth Jacobi polynomial specializes to the H11 block
polynomial when the matrix-path jets are `2^k E^k`. -/
theorem h11FourthJacobiMatrixGeneral_two_pow
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W E : Matrix ι ι ℂ) :
    h11FourthJacobiMatrixGeneral W
        ((2 : ℂ) • E) ((4 : ℂ) • E ^ 2)
        ((8 : ℂ) • E ^ 3) ((16 : ℂ) • E ^ 4) =
      h11BlockFourthJacobiMatrix W E := by
  unfold h11FourthJacobiMatrixGeneral h11BlockFourthJacobiMatrix
  noncomm_ring
  module

/-- Fourth Jacobi formula for the exp-affine path used by the doubled COE
block reduction.  Positivity and Hermiticity are stated only locally, so the
result applies directly on the open support. -/
theorem h11_iteratedDeriv_four_log_det_re_exp_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R E : Matrix ι ι ℂ)
    (hHerm : ∀ᶠ t in nhds (0 : ℝ),
      (R + NormedSpace.exp
        (t • ((2 : ℂ) • E) : Matrix ι ι ℂ)).IsHermitian)
    (hpos : ∀ᶠ t in nhds (0 : ℝ),
      0 < (Matrix.det
        (R + NormedSpace.exp
          (t • ((2 : ℂ) • E) : Matrix ι ι ℂ))).re) :
    iteratedDeriv 4
        (fun t : ℝ ↦ Real.log
          (Matrix.det
            (R + NormedSpace.exp
              (t • ((2 : ℂ) • E) : Matrix ι ι ℂ))).re) 0 =
      (Matrix.trace
        (h11BlockFourthJacobiMatrix (R + 1)⁻¹ E)).re := by
  let H : Matrix ι ι ℂ := (2 : ℂ) • E
  let ePath : ℝ → Matrix ι ι ℂ := fun t ↦ NormedSpace.exp (t • H)
  let F : ℝ → Matrix ι ι ℂ := fun t ↦ R + ePath t
  let F₁ : ℝ → Matrix ι ι ℂ := fun t ↦ ePath t * H
  let F₂ : ℝ → Matrix ι ι ℂ := fun t ↦ ePath t * H ^ 2
  let F₃ : ℝ → Matrix ι ι ℂ := fun t ↦ ePath t * H ^ 3
  let F₄ : ℝ → Matrix ι ι ℂ := fun t ↦ ePath t * H ^ 4
  have hePath (t : ℝ) : HasDerivAt ePath (ePath t * H) t := by
    simpa only [ePath] using hasDerivAt_exp_smul_const H t
  have hjets : ∀ᶠ t in nhds (0 : ℝ),
      HasDerivAt F (F₁ t) t ∧
      HasDerivAt F₁ (F₂ t) t ∧
      HasDerivAt F₂ (F₃ t) t ∧
      HasDerivAt F₃ (F₄ t) t := by
    filter_upwards [] with t
    have hF : HasDerivAt F (F₁ t) t := by
      convert (hasDerivAt_const (x := t) (c := R)).add (hePath t)
        using 1 <;>
      first
      | rfl
      | (funext s; rfl)
      | simp only [F, F₁, Pi.add_apply, zero_add]
    have hF₁ : HasDerivAt F₁ (F₂ t) t := by
      convert (hePath t).mul_const H using 1 <;>
      first
      | rfl
      | (funext s; rfl)
      | simp only [F₁, F₂, pow_two, Matrix.mul_assoc]
    have hF₂ : HasDerivAt F₂ (F₃ t) t := by
      convert (hePath t).mul_const (H ^ 2) using 1 <;>
      first
      | rfl
      | (funext s; rfl)
      | simp only [F₂, F₃, pow_succ, pow_zero, Matrix.one_mul,
          Matrix.mul_assoc]
    have hF₃ : HasDerivAt F₃ (F₄ t) t := by
      convert (hePath t).mul_const (H ^ 3) using 1 <;>
      first
      | rfl
      | (funext s; rfl)
      | simp only [F₃, F₄, pow_succ, pow_zero, Matrix.one_mul,
          Matrix.mul_assoc]
    exact ⟨hF, hF₁, hF₂, hF₃⟩
  have hHermF : ∀ᶠ t in nhds (0 : ℝ), (F t).IsHermitian := by
    simpa only [F, ePath, H] using hHerm
  have hposF : ∀ᶠ t in nhds (0 : ℝ),
      0 < (Matrix.det (F t)).re := by
    simpa only [F, ePath, H] using hpos
  have hmain := h11_iteratedDeriv_four_log_det_re_of_matrix_four_jet
    F F₁ F₂ F₃ F₄ 0 hjets hHermF hposF
  have hH₂ : H ^ 2 = (4 : ℂ) • E ^ 2 := by
    dsimp only [H]
    simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    norm_num
  have hH₃ : H ^ 3 = (8 : ℂ) • E ^ 3 := by
    dsimp only [H]
    simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    norm_num
  have hH₄ : H ^ 4 = (16 : ℂ) • E ^ 4 := by
    dsimp only [H]
    simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]
    norm_num
  simp only [F, F₁, F₂, F₃, F₄, ePath, zero_smul,
    NormedSpace.exp_zero, Matrix.one_mul] at hmain
  rw [hH₂, hH₃, hH₄] at hmain
  have hpoly := h11FourthJacobiMatrixGeneral_two_pow (R + 1)⁻¹ E
  rw [show H = (2 : ℂ) • E by rfl, hpoly] at hmain
  simpa only [F, ePath, H] using hmain

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
