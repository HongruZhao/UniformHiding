import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_COEBlockCayley
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFlowGeometry
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic

/-!
# The doubled COE block along the centered flow

This file isolates the exact determinant and block-factorization identities
which connect the literal COE support determinant to the fourth-Jacobi block
curve.  It contains no probability or scientific input.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open NormedSpace
open LogdetLean.GramHafnian.UltimateHiding.Dense

local instance h11FlowMatrixNormedAddCommGroup {N : ℕ} :
    NormedAddCommGroup (ConcreteMatrixState N) :=
  Matrix.linftyOpNormedAddCommGroup

local instance h11FlowMatrixNormedRing {N : ℕ} :
    NormedRing (ConcreteMatrixState N) :=
  { Matrix.linftyOpNormedRing with
    toAddCommGroup := h11FlowMatrixNormedAddCommGroup.toAddCommGroup }

local instance h11FlowMatrixRealNormedSpace {N : ℕ} :
    NormedSpace ℝ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

local instance h11FlowMatrixComplexNormedSpace {N : ℕ} :
    NormedSpace ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedSpace

local instance h11FlowMatrixRealNormedAlgebra {N : ℕ} :
    NormedAlgebra ℝ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra

local instance h11FlowMatrixComplexNormedAlgebra {N : ℕ} :
    NormedAlgebra ℂ (ConcreteMatrixState N) := Matrix.linftyOpNormedAlgebra

private def h11FlowMatrixEntryLinearMapReal
    (N : ℕ) (i j : Fin N) : ConcreteMatrixState N →ₗ[ℝ] ℂ where
  toFun M := M i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def h11FlowMatrixEntryCLM
    (N : ℕ) (i j : Fin N) : ConcreteMatrixState N →L[ℝ] ℂ :=
  (h11FlowMatrixEntryLinearMapReal N i j).toContinuousLinearMap

@[simp] private theorem h11FlowMatrixEntryCLM_apply
    {N : ℕ} (i j : Fin N) (M : ConcreteMatrixState N) :
    h11FlowMatrixEntryCLM N i j M = M i j := rfl

private def h11FlowConjTransposeLinearMapReal
    (N : ℕ) : ConcreteMatrixState N →ₗ[ℝ] ConcreteMatrixState N where
  toFun M := M.conjTranspose
  map_add' A B := Matrix.conjTranspose_add A B
  map_smul' c A := by
    simpa using (Matrix.conjTranspose_smul c A)

private def h11FlowConjTransposeCLM
    (N : ℕ) : ConcreteMatrixState N →L[ℝ] ConcreteMatrixState N :=
  (h11FlowConjTransposeLinearMapReal N).toContinuousLinearMap

@[simp] private theorem h11FlowConjTransposeCLM_apply
    {N : ℕ} (M : ConcreteMatrixState N) :
    h11FlowConjTransposeCLM N M = M.conjTranspose := rfl

private theorem contDiff_exp_ofReal_mul_matrix_h11
    {N : ℕ} (Q : ConcreteMatrixState N) (a : ℝ) :
    ContDiff ℝ ⊤ (fun t : ℝ =>
      exp ((((a * t : ℝ) : ℂ)) • Q)) := by
  have hscalar : ContDiff ℝ ⊤ (fun t : ℝ => ((a * t : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => a)).mul contDiff_id)
  have hinner : ContDiff ℝ ⊤ (fun t : ℝ =>
      (((a * t : ℝ) : ℂ)) • Q) :=
    hscalar.smul (contDiff_const : ContDiff ℝ ⊤
      (fun _ : ℝ => Q))
  rw [contDiff_iff_contDiffAt]
  intro t
  exact (NormedSpace.exp_analytic
      ((((a * t : ℝ) : ℂ)) • Q)).contDiffAt.comp t hinner.contDiffAt

private theorem contDiff_exp_ofReal_mul_matrix_entry_h11
    {N : ℕ} (Q : ConcreteMatrixState N) (a : ℝ) (i j : Fin N) :
    ContDiff ℝ ⊤ (fun t : ℝ =>
      exp ((((a * t : ℝ) : ℂ)) • Q) i j) := by
  exact (h11FlowMatrixEntryCLM N i j).contDiff.comp
    (contDiff_exp_ofReal_mul_matrix_h11 Q a)

private theorem contDiff_transposeCongruenceFlow_neg_h11
    {N : ℕ} (Q C : ConcreteMatrixState N) :
    ContDiff ℝ ⊤ (fun t : ℝ =>
      transposeCongruenceFlow Q (-t) C) := by
  have hleft := contDiff_exp_ofReal_mul_matrix_h11 Q (-1)
  have hright := contDiff_exp_ofReal_mul_matrix_h11 Q.transpose (-1)
  have hprod := (hleft.mul
    (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => C))).mul hright
  have heq : (fun t : ℝ => transposeCongruenceFlow Q (-t) C) =
      fun t : ℝ => exp ((((-1 : ℝ) * t : ℝ) : ℂ) • Q) * C *
        exp ((((-1 : ℝ) * t : ℝ) : ℂ) • Q.transpose) := by
    funext t
    rw [transposeCongruenceFlow_eq]
    have hs : ((-t : ℝ) : ℂ) = (((-1 : ℝ) * t : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hs]
  rw [heq]
  exact hprod

/-- The determinant of the doubled Hermitian block is the literal COE gap
determinant. -/
theorem det_h11COEBlockM_eq_det_inputGap
    {N : ℕ} (C : ConcreteMatrixState N) :
    Matrix.det (h11COEBlockM C) =
      Matrix.det (1 - C.conjTranspose * C) := by
  classical
  simpa [h11COEBlockM] using
    (Matrix.det_fromBlocks_one₁₁ C C.conjTranspose
      (1 : ConcreteMatrixState N))

/-- The block-diagonal outer factor in the centered-flow factorization. -/
def h11COEBlockOuter {N : ℕ}
    (Q : ConcreteMatrixState N) (t : ℝ) :
    Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ :=
  Matrix.fromBlocks
    (exp (((-t : ℝ) : ℂ) • Q)) 0 0
    (exp (((-t : ℝ) : ℂ) • Q.transpose))

/-- The positive block diagonal factor which removes the two outer factors
from the centered flow factorization. -/
def h11COEBlockUnwrapper {N : ℕ}
    (Q : ConcreteMatrixState N) (t : ℝ) :
    Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ :=
  Matrix.fromBlocks
    (exp (((t : ℝ) : ℂ) • Q)) 0 0
    (exp (((t : ℝ) : ℂ) • Q.transpose))

/-- The exponential-affine middle block.  At zero it is `M(C)`, while its
positive-order derivatives are the powers of the doubled direction with the
Jacobi coefficients `2^r`. -/
def h11COEBlockMiddle {N : ℕ}
    (Q C : ConcreteMatrixState N) (t : ℝ) :
    Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ :=
  Matrix.fromBlocks
    (exp (((2 * t : ℝ) : ℂ) • Q)) C C.conjTranspose
    (exp (((2 * t : ℝ) : ℂ) • Q.transpose))

@[simp] theorem h11COEBlockMiddle_zero
    {N : ℕ} (Q C : ConcreteMatrixState N) :
    h11COEBlockMiddle Q C 0 = h11COEBlockM C := by
  simp [h11COEBlockMiddle, h11COEBlockM]

theorem h11COEBlockM_isHermitian
    {N : ℕ} (C : ConcreteMatrixState N) :
    (h11COEBlockM C).IsHermitian := by
  unfold h11COEBlockM
  exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_one
    (by simp) Matrix.isHermitian_one

theorem h11COEBlockMiddle_isHermitian
    {N : ℕ} (Q C : ConcreteMatrixState N) (t : ℝ)
    (hQ : Q.IsHermitian) :
    (h11COEBlockMiddle Q C t).IsHermitian := by
  have htop :
      (exp (((2 * t : ℝ) : ℂ) • Q)).IsHermitian :=
    (hQ.smul (by simp [IsSelfAdjoint])).exp
  have hbottom :
      (exp (((2 * t : ℝ) : ℂ) • Q.transpose)).IsHermitian :=
    (hQ.transpose.smul (by simp [IsSelfAdjoint])).exp
  unfold h11COEBlockMiddle
  exact Matrix.IsHermitian.fromBlocks htop (by simp) hbottom

theorem det_im_eq_zero_of_isHermitian_h11
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (hM : M.IsHermitian) :
    (Matrix.det M).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have h := congrArg Matrix.det hM.eq
  rw [Matrix.det_conjTranspose] at h
  exact h

private theorem contDiff_det_of_entrywise_h11
    {n : Type*} [Fintype n] [DecidableEq n]
    (F : ℝ → Matrix n n ℂ)
    (hF : ∀ i j, ContDiff ℝ ⊤ (fun t => F t i j)) :
    ContDiff ℝ ⊤ (fun t => Matrix.det (F t)) := by
  classical
  rw [show (fun t => Matrix.det (F t)) =
      fun t => ∑ sigma : Equiv.Perm n,
        Equiv.Perm.sign sigma • ∏ i, F t (sigma i) i by
    funext t
    exact Matrix.det_apply (F t)]
  apply ContDiff.sum
  intro sigma _hsigma
  exact (contDiff_prod (t := Finset.univ)
    (fun i _hi => hF (sigma i) i)).const_smul
      (Equiv.Perm.sign sigma)

private theorem h11_exp_real_smul_mul_exp_real_smul
    {N : ℕ} (Q : ConcreteMatrixState N) (s t : ℝ) :
    exp (((s : ℝ) : ℂ) • Q) * exp (((t : ℝ) : ℂ) • Q) =
      exp ((((s + t : ℝ) : ℂ)) • Q) := by
  rw [← Matrix.exp_add_of_commute]
  · congr 1
    norm_num
    module
  · exact ((Commute.refl Q).smul_left (s : ℂ)).smul_right (t : ℂ)

private theorem h11_exp_neg_two_pos_cancel
    {N : ℕ} (Q : ConcreteMatrixState N) (t : ℝ) :
    exp (((-t : ℝ) : ℂ) • Q) *
        exp (((2 * t : ℝ) : ℂ) • Q) *
        exp (((-t : ℝ) : ℂ) • Q) = 1 := by
  rw [h11_exp_real_smul_mul_exp_real_smul Q (-t) (2 * t)]
  rw [h11_exp_real_smul_mul_exp_real_smul Q (-t + 2 * t) (-t)]
  have hz : (((-t + 2 * t + -t : ℝ) : ℂ)) = 0 := by
    push_cast
    ring
  rw [hz, zero_smul, exp_zero]

private theorem h11_exp_pos_neg_cancel
    {N : ℕ} (Q : ConcreteMatrixState N) (t : ℝ) :
    exp (((t : ℝ) : ℂ) • Q) * exp (((-t : ℝ) : ℂ) • Q) = 1 := by
  rw [h11_exp_real_smul_mul_exp_real_smul Q t (-t)]
  have hz : ((((t + -t : ℝ) : ℂ))) = 0 := by simp
  rw [hz, zero_smul, exp_zero]

private theorem h11_exp_neg_pos_cancel
    {N : ℕ} (Q : ConcreteMatrixState N) (t : ℝ) :
    exp (((-t : ℝ) : ℂ) • Q) * exp (((t : ℝ) : ℂ) • Q) = 1 := by
  rw [h11_exp_real_smul_mul_exp_real_smul Q (-t) t]
  have hz : ((((-t + t : ℝ) : ℂ))) = 0 := by simp
  rw [hz, zero_smul, exp_zero]

theorem h11COEBlockUnwrapper_mul_outer
    {N : ℕ} (Q : ConcreteMatrixState N) (t : ℝ) :
    h11COEBlockUnwrapper Q t * h11COEBlockOuter Q t = 1 := by
  classical
  simp only [h11COEBlockUnwrapper, h11COEBlockOuter,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, h11_exp_pos_neg_cancel]
  exact Matrix.fromBlocks_one

theorem h11COEBlockOuter_mul_unwrapper
    {N : ℕ} (Q : ConcreteMatrixState N) (t : ℝ) :
    h11COEBlockOuter Q t * h11COEBlockUnwrapper Q t = 1 := by
  classical
  simp only [h11COEBlockUnwrapper, h11COEBlockOuter,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, h11_exp_neg_pos_cancel]
  exact Matrix.fromBlocks_one

private theorem h11_conjTranspose_centered_flow_neg
    {N : ℕ} (Q C : ConcreteMatrixState N) (t : ℝ)
    (hQ : Q.IsHermitian) :
    (transposeCongruenceFlow Q (-t) C).conjTranspose =
      exp (((-t : ℝ) : ℂ) • Q.transpose) * C.conjTranspose *
        exp (((-t : ℝ) : ℂ) • Q) := by
  rw [transposeCongruenceFlow_eq, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul]
  simp only [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul,
    Complex.star_def, Complex.conj_ofReal, map_neg]
  rw [hQ.eq, hQ.transpose.eq]
  simp only [Matrix.mul_assoc]

/-- Exact centered-flow block factorization

`M(C_t) = D_t (exp(2tE) + (M(C)-I)) D_t`.

The middle expression is written blockwise, so this theorem does not need a
separate matrix-exponential theorem for block diagonal matrices. -/
theorem h11COEBlockM_centeredFlow_factorization
    {N : ℕ} (Q C : ConcreteMatrixState N) (t : ℝ)
    (hQ : Q.IsHermitian) :
    h11COEBlockM (transposeCongruenceFlow Q (-t) C) =
      h11COEBlockOuter Q t * h11COEBlockMiddle Q C t *
        h11COEBlockOuter Q t := by
  classical
  have hdiagQ := h11_exp_neg_two_pos_cancel Q t
  have hdiagQt := h11_exp_neg_two_pos_cancel Q.transpose t
  have hupper :
      exp (((-t : ℝ) : ℂ) • Q) * C *
          exp (((-t : ℝ) : ℂ) • Q.transpose) =
        transposeCongruenceFlow Q (-t) C := by
    symm
    simpa only [Complex.ofReal_neg] using
      (transposeCongruenceFlow_eq Q (-t) C)
  have hlower := h11_conjTranspose_centered_flow_neg Q C t hQ
  unfold h11COEBlockM h11COEBlockOuter h11COEBlockMiddle
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]
  rw [hdiagQ, hdiagQt, hupper, hlower]

/-- Exact unwrapped form of the centered flow block identity:
`D_t M(C_t) D_t = [[exp(2tQ), C], [Cᴴ, exp(2tQᵀ)]]`. -/
theorem h11COEBlockUnwrapper_mul_centeredFlow_mul_unwrapper
    {N : ℕ} (Q C : ConcreteMatrixState N) (t : ℝ)
    (hQ : Q.IsHermitian) :
    h11COEBlockUnwrapper Q t *
        h11COEBlockM (transposeCongruenceFlow Q (-t) C) *
          h11COEBlockUnwrapper Q t =
      h11COEBlockMiddle Q C t := by
  rw [h11COEBlockM_centeredFlow_factorization Q C t hQ]
  calc
    h11COEBlockUnwrapper Q t *
          (h11COEBlockOuter Q t * h11COEBlockMiddle Q C t *
            h11COEBlockOuter Q t) * h11COEBlockUnwrapper Q t =
        (h11COEBlockUnwrapper Q t * h11COEBlockOuter Q t) *
          h11COEBlockMiddle Q C t *
            (h11COEBlockOuter Q t * h11COEBlockUnwrapper Q t) := by
              noncomm_ring
    _ = h11COEBlockMiddle Q C t := by
      rw [h11COEBlockUnwrapper_mul_outer,
        h11COEBlockOuter_mul_unwrapper, Matrix.one_mul, Matrix.mul_one]

/-- Determinant form of the exact block factorization. -/
theorem det_h11COEBlockM_centeredFlow_factorization
    {N : ℕ} (Q C : ConcreteMatrixState N) (t : ℝ)
    (hQ : Q.IsHermitian) :
    Matrix.det (h11COEBlockM (transposeCongruenceFlow Q (-t) C)) =
      Matrix.det (h11COEBlockOuter Q t) *
        Matrix.det (h11COEBlockMiddle Q C t) *
          Matrix.det (h11COEBlockOuter Q t) := by
  rw [h11COEBlockM_centeredFlow_factorization Q C t hQ,
    Matrix.det_mul, Matrix.det_mul]

/-- The outer block can be eliminated without proving a separate
`det(exp)=exp(trace)` theorem: apply the same factorization at `C=0`, where
the literal doubled block is the identity. -/
theorem det_h11COEBlockM_centeredFlow_mul_middle_zero
    {N : ℕ} (Q C : ConcreteMatrixState N) (t : ℝ)
    (hQ : Q.IsHermitian) :
    Matrix.det (h11COEBlockM (transposeCongruenceFlow Q (-t) C)) *
        Matrix.det (h11COEBlockMiddle Q 0 t) =
      Matrix.det (h11COEBlockMiddle Q C t) := by
  classical
  have hC := det_h11COEBlockM_centeredFlow_factorization Q C t hQ
  have hzero := det_h11COEBlockM_centeredFlow_factorization
    Q (0 : ConcreteMatrixState N) t hQ
  have houter :
      Matrix.det (h11COEBlockOuter Q t) *
          Matrix.det (h11COEBlockMiddle Q 0 t) *
            Matrix.det (h11COEBlockOuter Q t) = 1 := by
    simp only [transposeCongruenceFlow, transposeCongruence_zero] at hzero
    have hMzero : h11COEBlockM (0 : ConcreteMatrixState N) = 1 := by
      simp [h11COEBlockM, ← Matrix.fromBlocks_one]
    rw [hMzero, Matrix.det_one] at hzero
    exact hzero.symm
  rw [hC]
  calc
    (Matrix.det (h11COEBlockOuter Q t) *
          Matrix.det (h11COEBlockMiddle Q C t) *
            Matrix.det (h11COEBlockOuter Q t)) *
        Matrix.det (h11COEBlockMiddle Q 0 t) =
      Matrix.det (h11COEBlockMiddle Q C t) *
        (Matrix.det (h11COEBlockOuter Q t) *
          Matrix.det (h11COEBlockMiddle Q 0 t) *
            Matrix.det (h11COEBlockOuter Q t)) := by ring
    _ = Matrix.det (h11COEBlockMiddle Q C t) := by
      rw [houter, mul_one]

/-- Real-part form of the determinant cancellation.  All three determinants
are real because their matrices are Hermitian. -/
theorem re_det_h11COEBlockM_centeredFlow_mul_middle_zero
    {N : ℕ} (Q C : ConcreteMatrixState N) (t : ℝ)
    (hQ : Q.IsHermitian) :
    (Matrix.det
        (h11COEBlockM (transposeCongruenceFlow Q (-t) C))).re *
        (Matrix.det (h11COEBlockMiddle Q 0 t)).re =
      (Matrix.det (h11COEBlockMiddle Q C t)).re := by
  have h := congrArg Complex.re
    (det_h11COEBlockM_centeredFlow_mul_middle_zero Q C t hQ)
  have himLit :
      (Matrix.det
        (h11COEBlockM (transposeCongruenceFlow Q (-t) C))).im = 0 :=
    det_im_eq_zero_of_isHermitian_h11 _
      (h11COEBlockM_isHermitian _)
  have himZero :
      (Matrix.det (h11COEBlockMiddle Q 0 t)).im = 0 :=
    det_im_eq_zero_of_isHermitian_h11 _
      (h11COEBlockMiddle_isHermitian Q 0 t hQ)
  simpa only [Complex.mul_re, himLit, himZero, mul_zero, sub_zero] using h

/-- On the open COE support, the real determinant of the exponential-affine
middle block stays positive in a neighborhood of the base point. -/
theorem eventually_det_h11COEBlockMiddle_re_pos_of_support
    {N : ℕ} (Q C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    ∀ᶠ t in nhds (0 : ℝ),
      0 < (Matrix.det (h11COEBlockMiddle Q C t)).re := by
  let d : ℝ → ℝ := fun t =>
    (Matrix.det (h11COEBlockMiddle Q C t)).re
  have hd0 : 0 < d 0 := by
    simp only [d, h11COEBlockMiddle_zero]
    rw [det_h11COEBlockM_eq_det_inputGap]
    exact (RCLike.lt_iff_re_im.mp hsupport.det_pos).1
  have hdCD : ContDiff ℝ ⊤ d := by
    dsimp only [d]
    apply Complex.reCLM.contDiff.comp
    apply contDiff_det_of_entrywise_h11
    intro i j
    rcases i with i | i
    · rcases j with j | j
      · simpa [h11COEBlockMiddle] using
          contDiff_exp_ofReal_mul_matrix_entry_h11 Q 2 i j
      · simpa [h11COEBlockMiddle] using
          (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => C i j))
    · rcases j with j | j
      · simpa [h11COEBlockMiddle] using
          (contDiff_const : ContDiff ℝ ⊤
            (fun _ : ℝ => C.conjTranspose i j))
      · simpa [h11COEBlockMiddle] using
          contDiff_exp_ofReal_mul_matrix_entry_h11 Q.transpose 2 i j
  exact continuousAt_const.eventually_lt
    hdCD.continuous.continuousAt hd0

/-- The literal doubled-block fourth log jet is the fourth log jet of the
exp-affine middle block minus its `C=0` value. -/
theorem iteratedDeriv_four_log_re_det_h11COEBlockM_centeredFlow_eq_middle_sub
    {N : ℕ} (Q C : ConcreteMatrixState N)
    (hQ : Q.IsHermitian) (hsupport : coeCornerSupport C) :
    iteratedDeriv 4 (fun t : ℝ => Real.log
        (Matrix.det
          (h11COEBlockM (transposeCongruenceFlow Q (-t) C))).re) 0 =
      iteratedDeriv 4 (fun t : ℝ => Real.log
        (Matrix.det (h11COEBlockMiddle Q C t)).re) 0 -
      iteratedDeriv 4 (fun t : ℝ => Real.log
        (Matrix.det (h11COEBlockMiddle Q 0 t)).re) 0 := by
  let dLit : ℝ → ℝ := fun t =>
    (Matrix.det
      (h11COEBlockM (transposeCongruenceFlow Q (-t) C))).re
  let dC : ℝ → ℝ := fun t =>
    (Matrix.det (h11COEBlockMiddle Q C t)).re
  let dZero : ℝ → ℝ := fun t =>
    (Matrix.det (h11COEBlockMiddle Q 0 t)).re
  have hdLit0 : 0 < dLit 0 := by
    simp only [dLit, neg_zero, transposeCongruenceFlow_zero]
    rw [det_h11COEBlockM_eq_det_inputGap]
    exact (RCLike.lt_iff_re_im.mp hsupport.det_pos).1
  have hdC0 : 0 < dC 0 := by
    simp only [dC, h11COEBlockMiddle_zero]
    rw [det_h11COEBlockM_eq_det_inputGap]
    exact (RCLike.lt_iff_re_im.mp hsupport.det_pos).1
  have hdZero0 : 0 < dZero 0 := by
    simp [dZero, h11COEBlockMiddle, ← Matrix.fromBlocks_one]
  have hdLitCD : ContDiff ℝ ⊤ dLit := by
    dsimp only [dLit]
    apply Complex.reCLM.contDiff.comp
    apply contDiff_det_of_entrywise_h11
    have hflow := contDiff_transposeCongruenceFlow_neg_h11 Q C
    have hflowStar := (h11FlowConjTransposeCLM N).contDiff.comp hflow
    intro i j
    rcases i with i | i
    · rcases j with j | j
      · simpa [h11COEBlockM] using
          (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ =>
            (1 : ConcreteMatrixState N) i j))
      · change ContDiff ℝ ⊤ (fun t : ℝ =>
          transposeCongruenceFlow Q (-t) C i j)
        rw [show (fun t : ℝ => transposeCongruenceFlow Q (-t) C i j) =
            (h11FlowMatrixEntryCLM N i j) ∘
              (fun t : ℝ => transposeCongruenceFlow Q (-t) C) by
          funext t
          rfl]
        exact (h11FlowMatrixEntryCLM N i j).contDiff.comp hflow
    · rcases j with j | j
      · change ContDiff ℝ ⊤ (fun t : ℝ =>
          (transposeCongruenceFlow Q (-t) C).conjTranspose i j)
        rw [show (fun t : ℝ =>
              (transposeCongruenceFlow Q (-t) C).conjTranspose i j) =
            (h11FlowMatrixEntryCLM N i j) ∘
              ((h11FlowConjTransposeCLM N) ∘
                (fun t : ℝ => transposeCongruenceFlow Q (-t) C)) by
          funext t
          rfl]
        exact (h11FlowMatrixEntryCLM N i j).contDiff.comp hflowStar
      · simpa [h11COEBlockM] using
          (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ =>
            (1 : ConcreteMatrixState N) i j))
  have hdCCD : ContDiff ℝ ⊤ dC := by
    dsimp only [dC]
    apply Complex.reCLM.contDiff.comp
    apply contDiff_det_of_entrywise_h11
    intro i j
    rcases i with i | i
    · rcases j with j | j
      · simpa [h11COEBlockMiddle] using
          contDiff_exp_ofReal_mul_matrix_entry_h11 Q 2 i j
      · simpa [h11COEBlockMiddle] using
          (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => C i j))
    · rcases j with j | j
      · simpa [h11COEBlockMiddle] using
          (contDiff_const : ContDiff ℝ ⊤
            (fun _ : ℝ => C.conjTranspose i j))
      · simpa [h11COEBlockMiddle] using
          contDiff_exp_ofReal_mul_matrix_entry_h11 Q.transpose 2 i j
  have hdZeroCD : ContDiff ℝ ⊤ dZero := by
    dsimp only [dZero]
    apply Complex.reCLM.contDiff.comp
    apply contDiff_det_of_entrywise_h11
    intro i j
    rcases i with i | i
    · rcases j with j | j
      · simpa [h11COEBlockMiddle] using
          contDiff_exp_ofReal_mul_matrix_entry_h11 Q 2 i j
      · simpa [h11COEBlockMiddle] using
          (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (0 : ℂ)))
    · rcases j with j | j
      · simpa [h11COEBlockMiddle] using
          (contDiff_const : ContDiff ℝ ⊤ (fun _ : ℝ => (0 : ℂ)))
      · simpa [h11COEBlockMiddle] using
          contDiff_exp_ofReal_mul_matrix_entry_h11 Q.transpose 2 i j
  have hdLitPos : ∀ᶠ t in nhds 0, 0 < dLit t :=
    continuousAt_const.eventually_lt hdLitCD.continuous.continuousAt hdLit0
  have hdCPos : ∀ᶠ t in nhds 0, 0 < dC t :=
    continuousAt_const.eventually_lt hdCCD.continuous.continuousAt hdC0
  have hdZeroPos : ∀ᶠ t in nhds 0, 0 < dZero t :=
    continuousAt_const.eventually_lt hdZeroCD.continuous.continuousAt hdZero0
  have hlog :
      (fun t => Real.log (dLit t)) =ᶠ[nhds 0]
        (fun t => Real.log (dC t) - Real.log (dZero t)) := by
    filter_upwards [hdLitPos, hdCPos, hdZeroPos] with t htLit _htC htZero
    have hprod : dLit t * dZero t = dC t := by
      exact re_det_h11COEBlockM_centeredFlow_mul_middle_zero Q C t hQ
    rw [← hprod, Real.log_mul (ne_of_gt htLit) (ne_of_gt htZero)]
    ring
  change iteratedDeriv 4 (fun t => Real.log (dLit t)) 0 = _
  rw [hlog.iteratedDeriv_eq 4]
  change iteratedDeriv 4
      ((fun t => Real.log (dC t)) - (fun t => Real.log (dZero t))) 0 =
    iteratedDeriv 4 (fun t => Real.log (dC t)) 0 -
      iteratedDeriv 4 (fun t => Real.log (dZero t)) 0
  rw [iteratedDeriv_sub
    ((hdCCD.contDiffAt.log (ne_of_gt hdC0)).of_le (by norm_num))
    ((hdZeroCD.contDiffAt.log (ne_of_gt hdZero0)).of_le (by norm_num))]

/-- Literal input-gap form of the previous fourth-jet reduction. -/
theorem iteratedDeriv_four_log_re_det_inputGap_centeredFlow_eq_middle_sub
    {N : ℕ} (Q C : ConcreteMatrixState N)
    (hQ : Q.IsHermitian) (hsupport : coeCornerSupport C) :
    iteratedDeriv 4 (fun t : ℝ => Real.log
        (Matrix.det
          (1 - (transposeCongruenceFlow Q (-t) C).conjTranspose *
            transposeCongruenceFlow Q (-t) C)).re) 0 =
      iteratedDeriv 4 (fun t : ℝ => Real.log
        (Matrix.det (h11COEBlockMiddle Q C t)).re) 0 -
      iteratedDeriv 4 (fun t : ℝ => Real.log
        (Matrix.det (h11COEBlockMiddle Q 0 t)).re) 0 := by
  have hblock :=
    iteratedDeriv_four_log_re_det_h11COEBlockM_centeredFlow_eq_middle_sub
      Q C hQ hsupport
  have heq :
      (fun t : ℝ => Real.log
        (Matrix.det
          (1 - (transposeCongruenceFlow Q (-t) C).conjTranspose *
            transposeCongruenceFlow Q (-t) C)).re) =
      (fun t : ℝ => Real.log
        (Matrix.det
          (h11COEBlockM (transposeCongruenceFlow Q (-t) C))).re) := by
    funext t
    rw [det_h11COEBlockM_eq_det_inputGap]
  rw [heq]
  exact hblock

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
