import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_COEBlockFlow
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_FourthJacobiFormula
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_FourthScoreSupportReduction
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_FourthBellNormalizationReducer
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

/-!
# Literal fourth-score sign from the doubled COE block

This file identifies the exponential-affine middle block with the path in the
fourth Jacobi formula.  Combined with the Cayley trace inequality, this gives
the pointwise nonpositivity package used by the H11 normalization argument.
There is no probabilistic or scientific input in this module.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open scoped ComplexOrder MatrixOrder
open NormedSpace
open LogdetLean.GramHafnian.UltimateHiding.Dense

private def h11SumSelfEquivProdBool (a : Type*) : a ⊕ a ≃ a × Bool where
  toFun
    | Sum.inl i => (i, false)
    | Sum.inr i => (i, true)
  invFun
    | (i, false) => Sum.inl i
    | (i, true) => Sum.inr i
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i, b⟩; cases b <;> rfl

private def h11BoolBlocks {a : Type*}
    (A B : Matrix a a ℂ) : Bool → Matrix a a ℂ
  | false => A
  | true => B

private theorem reindex_tsum_h11
    {X m n : Type*} (e : m ≃ n) (f : X → Matrix m m ℂ) :
    Matrix.reindex e e (∑' x, f x) =
      ∑' x, Matrix.reindex e e (f x) := by
  exact Function.LeftInverse.map_tsum
    (g := Matrix.reindexAddEquiv ℂ e e) f
    (continuous_id.matrix_reindex e e)
    (continuous_id.matrix_reindex e.symm e.symm)
    (fun M => by simp)

private theorem reindex_exp_h11
    {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m ℂ) :
    Matrix.reindex e e (exp A) = exp (Matrix.reindex e e A) := by
  rw [exp_eq_tsum_rat, exp_eq_tsum_rat, reindex_tsum_h11]
  apply tsum_congr
  intro k
  change (Matrix.reindexRingEquiv ℂ e)
      (((k.factorial : ℚ)⁻¹) • A ^ k) =
    ((k.factorial : ℚ)⁻¹) • (Matrix.reindexRingEquiv ℂ e A) ^ k
  have hp := (Matrix.reindexRingEquiv ℂ e).map_pow A k
  rw [← hp]
  rfl

private theorem reindex_fromBlocks_diagonal_h11
    {a : Type*} [DecidableEq a]
    (A B : Matrix a a ℂ) :
    Matrix.reindex (h11SumSelfEquivProdBool a)
        (h11SumSelfEquivProdBool a)
        (Matrix.fromBlocks A 0 0 B) =
      Matrix.blockDiagonal (h11BoolBlocks A B) := by
  ext i j
  rcases i with ⟨i, bi⟩
  rcases j with ⟨j, bj⟩
  cases bi <;> cases bj <;>
    simp [Matrix.reindex_apply, h11SumSelfEquivProdBool,
      Matrix.blockDiagonal_apply, h11BoolBlocks]

/-- The exponential of a two-by-two block-diagonal matrix is the block
diagonal matrix of exponentials. -/
theorem exp_fromBlocks_diagonal_h11
    {a : Type*} [Fintype a] [DecidableEq a]
    (A B : Matrix a a ℂ) :
    exp (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (exp A) 0 0 (exp B) := by
  apply (Matrix.reindex (h11SumSelfEquivProdBool a)
    (h11SumSelfEquivProdBool a)).injective
  rw [reindex_exp_h11, reindex_fromBlocks_diagonal_h11,
    Matrix.exp_blockDiagonal, reindex_fromBlocks_diagonal_h11]
  congr 1
  funext b
  open scoped Matrix.Norms.Operator in
    cases b with
    | false =>
        change exp (h11BoolBlocks A B) false = exp A
        exact Pi.coe_exp (h11BoolBlocks A B) false
    | true =>
        change exp (h11BoolBlocks A B) true = exp B
        exact Pi.coe_exp (h11BoolBlocks A B) true

/-- The literal middle block is exactly the exponential-affine path whose
fourth log-determinant jet is evaluated by the Jacobi formula. -/
theorem h11COEBlockMiddle_eq_exp_affine
    {N : ℕ} (Q C : ConcreteMatrixState N) (t : ℝ)
    (hQ : Q.IsHermitian) :
    h11COEBlockMiddle Q C t =
      (h11COEBlockM C - 1) +
        exp (t • ((2 : ℂ) • h11COEBlockDirection Q)) := by
  classical
  rw [show t • ((2 : ℂ) • h11COEBlockDirection Q) =
      Matrix.fromBlocks
        ((((2 * t : ℝ) : ℂ)) • Q) 0 0
        ((((2 * t : ℝ) : ℂ)) • Q.transpose) by
    unfold h11COEBlockDirection
    rw [map_star_eq_transpose_of_isHermitian_h11 hQ]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp <;> ring]
  rw [exp_fromBlocks_diagonal_h11]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [h11COEBlockMiddle, h11COEBlockM, Matrix.one_apply]

/-- The fourth log-determinant jet of the literal middle block is the H11
Jacobi trace polynomial at the doubled block inverse. -/
theorem iteratedDeriv_four_log_det_h11COEBlockMiddle_eq
    {N : ℕ} (Q C : ConcreteMatrixState N)
    (hQ : Q.IsHermitian) (hsupport : coeCornerSupport C) :
    iteratedDeriv 4 (fun t : ℝ => Real.log
        (Matrix.det (h11COEBlockMiddle Q C t)).re) 0 =
      (Matrix.trace (h11BlockFourthJacobiMatrix
        (h11COEBlockM C)⁻¹ (h11COEBlockDirection Q))).re := by
  let R : Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ :=
    h11COEBlockM C - 1
  let E : Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ :=
    h11COEBlockDirection Q
  have hpath (t : ℝ) :
      R + exp (t • ((2 : ℂ) • E)) = h11COEBlockMiddle Q C t := by
    exact (h11COEBlockMiddle_eq_exp_affine Q C t hQ).symm
  have hHerm : ∀ᶠ t in nhds (0 : ℝ),
      (R + exp (t • ((2 : ℂ) • E))).IsHermitian := by
    filter_upwards [] with t
    rw [hpath t]
    exact h11COEBlockMiddle_isHermitian Q C t hQ
  have hpos : ∀ᶠ t in nhds (0 : ℝ),
      0 < (Matrix.det
        (R + exp (t • ((2 : ℂ) • E)))).re := by
    filter_upwards
      [eventually_det_h11COEBlockMiddle_re_pos_of_support Q C hsupport]
      with t ht
    rw [hpath t]
    exact ht
  have hmain := h11_iteratedDeriv_four_log_det_re_exp_affine
    R E hHerm hpos
  have hfun :
      (fun t : ℝ => Real.log
        (Matrix.det (h11COEBlockMiddle Q C t)).re) =
      (fun t : ℝ => Real.log
        (Matrix.det (R + exp (t • ((2 : ℂ) • E)))).re) := by
    funext t
    rw [hpath t]
  rw [hfun]
  dsimp only [R, E] at hmain
  convert hmain using 1
  · rfl
  · rw [sub_add_cancel]

/-- At the identity base block all five fourth-Jacobi words coincide, and
their coefficients cancel. -/
theorem h11BlockFourthJacobiMatrix_one_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (E : Matrix n n ℂ) :
    h11BlockFourthJacobiMatrix 1 E = 0 := by
  unfold h11BlockFourthJacobiMatrix
  noncomm_ring
  module

/-- The `C=0` middle block contributes no positive-order log-determinant
jet; in particular its fourth jet vanishes. -/
theorem iteratedDeriv_four_log_det_h11COEBlockMiddle_zero_eq_zero
    {N : ℕ} (Q : ConcreteMatrixState N) (hQ : Q.IsHermitian) :
    iteratedDeriv 4 (fun t : ℝ => Real.log
        (Matrix.det (h11COEBlockMiddle Q 0 t)).re) 0 = 0 := by
  have hs0 : coeCornerSupport (0 : ConcreteMatrixState N) := by
    unfold coeCornerSupport
    simpa only [Matrix.conjTranspose_zero, Matrix.zero_mul, sub_zero] using
      (Matrix.PosDef.one :
      (1 : ConcreteMatrixState N).PosDef)
  rw [iteratedDeriv_four_log_det_h11COEBlockMiddle_eq Q 0 hQ hs0]
  have hM0 : h11COEBlockM (0 : ConcreteMatrixState N) = 1 := by
    simp [h11COEBlockM]
  rw [hM0]
  simp only [inv_one, h11BlockFourthJacobiMatrix_one_eq_zero,
    Matrix.trace_zero, Complex.zero_re]

/-- Exact literal fourth gap-log jet as the Cayley-controlled block Jacobi
trace.  This is the analytic equality that fixes the sign convention. -/
theorem iteratedDeriv_four_log_re_det_inputGap_centeredFlow_eq_blockJacobi
    {N : ℕ} (Q C : ConcreteMatrixState N)
    (hQ : Q.IsHermitian) (hsupport : coeCornerSupport C) :
    iteratedDeriv 4 (fun t : ℝ => Real.log
        (Matrix.det
          (1 - (transposeCongruenceFlow Q (-t) C).conjTranspose *
            transposeCongruenceFlow Q (-t) C)).re) 0 =
      (Matrix.trace (h11BlockFourthJacobiMatrix
        (h11COEBlockM C)⁻¹ (h11COEBlockDirection Q))).re := by
  rw [iteratedDeriv_four_log_re_det_inputGap_centeredFlow_eq_middle_sub
    Q C hQ hsupport]
  rw [iteratedDeriv_four_log_det_h11COEBlockMiddle_eq Q C hQ hsupport,
    iteratedDeriv_four_log_det_h11COEBlockMiddle_zero_eq_zero Q hQ,
    sub_zero]

/-- The public determinant-log jet for the literal centered orbital flow is
exactly the doubled-block Jacobi trace. -/
theorem concreteCenteredLogDeterminantJet_four_eq_blockJacobi
    {N K : ℕ} (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredLogDeterminantJet 4 N K v A =
      (Matrix.trace (h11BlockFourthJacobiMatrix
        (h11COEBlockM (unscaleCOECorner K A))⁻¹
        (h11COEBlockDirection
          (concreteCenteredOrbitalDirection N v)))).re := by
  simpa [concreteCenteredLogDeterminantJet,
    concreteCOECenteredInverseDeterminant] using
    (iteratedDeriv_four_log_re_det_inputGap_centeredFlow_eq_blockJacobi
      (concreteCenteredOrbitalDirection N v)
      (unscaleCOECorner K A)
      (concreteCenteredOrbitalDirection_isHermitian v) hsupport)

/-- Pointwise sign of the literal fourth determinant-log jet on the open
COE support. -/
theorem concreteCenteredLogDeterminantJet_four_nonpos
    {N K : ℕ} (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredLogDeterminantJet 4 N K v A ≤ 0 := by
  rw [concreteCenteredLogDeterminantJet_four_eq_blockJacobi A v hsupport]
  exact trace_h11COEBlockFourthJacobiMatrix_re_nonpos
    (unscaleCOECorner K A) (concreteCenteredOrbitalDirection N v)
    hsupport (concreteCenteredOrbitalDirection_isHermitian v)

/-- Foundations-only producer of the support-sign package required by the
H11 Bell-normalization reducer. -/
theorem h11FourthLogScoreNonpositiveOnSupport_proved
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    H11FourthLogScoreNonpositiveOnSupport N K where
  nonpos_on_support := by
    intro A v _hsymm hsupport
    rw [concreteCenteredEll_four_eq_logDeterminantJet_h11_internal
      hN A v hsupport]
    have hc : 0 < concreteCOEExponent N K :=
      concreteCOEExponent_pos_of_higherScoreGap hgap
    have hp : 0 ≤ coeCornerDensityExponent N K := by
      change 0 ≤ concreteCOEExponent N K / 2
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hp
      (concreteCenteredLogDeterminantJet_four_nonpos A v hsupport)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
