import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_CayleyFourthJacobiSign
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredLikelihood
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# The literal doubled COE block and its Cayley grading

For a complex matrix `C`, the doubled Hermitian blocks are

`M(C) = [[I,C],[Cᴴ,I]]`,  `B(C) = M(-C)`,

with grading `J = diag(I,-I)`.  On the COE support
`I-CᴴC > 0`, both `M(C)` and `B(C)` are positive definite.  This file
records the finite block identities needed to feed the H11 Cayley sign.
-/

open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

abbrev H11COEBlockIndex (N : ℕ) := Fin N ⊕ Fin N

/-- Positive doubled block associated to a COE contraction. -/
def h11COEBlockM {N : ℕ} (C : ConcreteMatrixState N) :
    Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ :=
  Matrix.fromBlocks 1 C C.conjTranspose 1

/-- The opposite doubled block, obtained by changing the sign of `C`. -/
def h11COEBlockB {N : ℕ} (C : ConcreteMatrixState N) :
    Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ :=
  h11COEBlockM (-C)

/-- The block diagonal pair of the two COE gap matrices. -/
def h11COEBlockGapDiagonal {N : ℕ} (C : ConcreteMatrixState N) :
    Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ :=
  Matrix.fromBlocks
    (1 - C * C.conjTranspose) 0 0
    (1 - C.conjTranspose * C)

/-- Literal multiplication of the two opposite doubled blocks. -/
theorem h11COEBlockM_mul_B_eq_gapDiagonal
    {N : ℕ} (C : ConcreteMatrixState N) :
    h11COEBlockM C * h11COEBlockB C = h11COEBlockGapDiagonal C := by
  classical
  simp [h11COEBlockM, h11COEBlockB, h11COEBlockGapDiagonal,
    Matrix.fromBlocks_multiply]
  constructor <;> module

/-- The reverse product gives the same literal gap diagonal. -/
theorem h11COEBlockB_mul_M_eq_gapDiagonal
    {N : ℕ} (C : ConcreteMatrixState N) :
    h11COEBlockB C * h11COEBlockM C = h11COEBlockGapDiagonal C := by
  classical
  simp [h11COEBlockM, h11COEBlockB, h11COEBlockGapDiagonal,
    Matrix.fromBlocks_multiply]
  constructor <;> module

/-- The grading involution on the doubled space. -/
def h11COEBlockGrading (N : ℕ) :
    Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ :=
  Matrix.fromBlocks 1 0 0 (-1)

/-- The doubled centered-flow generator.  The lower block is the entrywise
conjugate generator because the right factor in the symmetric congruence is
the transpose exponential. -/
def h11COEBlockDirection {N : ℕ} (Q : ConcreteMatrixState N) :
    Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ :=
  Matrix.fromBlocks Q 0 0 (Q.map star)

/-- The positive Cayley transform attached to the pair `M(C),M(-C)`. -/
def h11COEBlockCayley {N : ℕ} (C : ConcreteMatrixState N) :
    Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ :=
  (h11COEBlockM C)⁻¹ * h11COEBlockB C

theorem h11COEBlockM_posDef_of_support
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (h11COEBlockM C).PosDef := by
  classical
  let I : ConcreteMatrixState N := 1
  have hI : I.PosDef := by
    exact Matrix.PosDef.one
  letI : Invertible I := invertibleOne
  have hpsd : (h11COEBlockM C).PosSemidef := by
    have h := (Matrix.PosDef.fromBlocks₁₁ C I hI).2
      (show (I - C.conjTranspose * I⁻¹ * C).PosSemidef by
        simpa only [I, inv_one, Matrix.mul_one] using
          hsupport.posSemidef)
    simpa only [h11COEBlockM, I] using h
  have hunit : IsUnit (h11COEBlockM C) := by
    change IsUnit (Matrix.fromBlocks I C C.conjTranspose I)
    rw [Matrix.isUnit_fromBlocks_iff_of_invertible₁₁]
    simpa only [I, invOf_one, Matrix.mul_one] using hsupport.isUnit
  exact hpsd.posDef_iff_isUnit.mpr hunit

theorem h11COEBlockB_posDef_of_support
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (h11COEBlockB C).PosDef := by
  have hsneg : coeCornerSupport (-C) := by
    unfold coeCornerSupport at hsupport ⊢
    simpa only [Matrix.conjTranspose_neg, Matrix.neg_mul,
      Matrix.mul_neg, neg_neg] using hsupport
  simpa only [h11COEBlockB] using
    h11COEBlockM_posDef_of_support (-C) hsneg

/-- The exact paper identity `M(C)B(C)=B(C)M(C)=diag(gaps)>0`. -/
theorem h11COEBlock_product_identity_posDef
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    h11COEBlockM C * h11COEBlockB C =
        h11COEBlockB C * h11COEBlockM C ∧
      h11COEBlockB C * h11COEBlockM C = h11COEBlockGapDiagonal C ∧
      (h11COEBlockGapDiagonal C).PosDef := by
  have hMB := h11COEBlockM_mul_B_eq_gapDiagonal C
  have hBM := h11COEBlockB_mul_M_eq_gapDiagonal C
  have hM := h11COEBlockM_posDef_of_support C hsupport
  have hB := h11COEBlockB_posDef_of_support C hsupport
  have hcomm : Commute (h11COEBlockM C) (h11COEBlockB C) :=
    hMB.trans hBM.symm
  have hnonneg : 0 ≤ h11COEBlockM C * h11COEBlockB C :=
    hcomm.mul_nonneg hM.posSemidef.nonneg hB.posSemidef.nonneg
  have hpsd : (h11COEBlockM C * h11COEBlockB C).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hnonneg
  have hunit : IsUnit (h11COEBlockM C * h11COEBlockB C) :=
    hM.isUnit.mul hB.isUnit
  have hprodPos : (h11COEBlockM C * h11COEBlockB C).PosDef :=
    hpsd.posDef_iff_isUnit.mpr hunit
  exact ⟨hcomm.eq, hBM, hMB ▸ hprodPos⟩

theorem h11COEBlockGrading_isHermitian (N : ℕ) :
    (h11COEBlockGrading N).IsHermitian := by
  unfold h11COEBlockGrading
  exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_one
    (by simp) Matrix.isHermitian_one.neg

theorem h11COEBlockGrading_sq (N : ℕ) :
    h11COEBlockGrading N * h11COEBlockGrading N = 1 := by
  classical
  simp [h11COEBlockGrading, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one]

theorem h11COEBlockGrading_conjugate_M
    {N : ℕ} (C : ConcreteMatrixState N) :
    h11COEBlockGrading N * h11COEBlockM C * h11COEBlockGrading N =
      h11COEBlockB C := by
  classical
  simp [h11COEBlockGrading, h11COEBlockM, h11COEBlockB,
    Matrix.fromBlocks_multiply]

theorem h11COEBlockDirection_commutes_grading
    {N : ℕ} (Q : ConcreteMatrixState N) :
    h11COEBlockDirection Q * h11COEBlockGrading N =
      h11COEBlockGrading N * h11COEBlockDirection Q := by
  classical
  simp [h11COEBlockDirection, h11COEBlockGrading,
    Matrix.fromBlocks_multiply]

theorem map_star_eq_transpose_of_isHermitian_h11
    {N : ℕ} {Q : ConcreteMatrixState N} (hQ : Q.IsHermitian) :
    Q.map star = Q.transpose := by
  ext i j
  exact hQ.apply j i

theorem h11COEBlockDirection_isHermitian
    {N : ℕ} (Q : ConcreteMatrixState N) (hQ : Q.IsHermitian) :
    (h11COEBlockDirection Q).IsHermitian := by
  have hmap : (Q.map star).IsHermitian := by
    rw [map_star_eq_transpose_of_isHermitian_h11 hQ]
    exact hQ.transpose
  unfold h11COEBlockDirection
  exact Matrix.IsHermitian.fromBlocks hQ (by simp) hmap

/-- The opposite block is the affine partner `2I-M`. -/
theorem h11COEBlockB_eq_two_one_sub_M
    {N : ℕ} (C : ConcreteMatrixState N) :
    h11COEBlockB C =
      (2 : ℂ) •
        (1 : Matrix (H11COEBlockIndex N) (H11COEBlockIndex N) ℂ) -
        h11COEBlockM C := by
  classical
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    by_cases h : i = j <;>
    simp [h11COEBlockB, h11COEBlockM, Matrix.one_apply, h] <;>
    norm_num

/-- A positive affine Cayley pair has a positive-definite product Cayley
transform. -/
theorem positiveCayleyPair_posDef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M B : Matrix ι ι ℂ) (hM : M.PosDef) (hB : B.PosDef)
    (hBaff : B = (2 : ℂ) • (1 : Matrix ι ι ℂ) - M) :
    (M⁻¹ * B).PosDef := by
  let W : Matrix ι ι ℂ := M⁻¹
  letI : Invertible M := hM.isUnit.invertible
  have hW : W.PosDef := by
    exact hM.inv
  have hWB : W * B = (2 : ℂ) • W - 1 := by
    simp only [W, hBaff, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.mul_one, Matrix.inv_mul_of_invertible]
  have hBW : B * W = (2 : ℂ) • W - 1 := by
    simp only [W, hBaff, Matrix.sub_mul, Matrix.smul_mul,
      Matrix.one_mul, Matrix.mul_inv_of_invertible]
  have hcomm : Commute W B := hWB.trans hBW.symm
  have hnonneg : 0 ≤ W * B :=
    hcomm.mul_nonneg hW.posSemidef.nonneg hB.posSemidef.nonneg
  have hpsd : (W * B).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hnonneg
  have hunit : IsUnit (W * B) := hW.isUnit.mul hB.isUnit
  change (W * B).PosDef
  exact hpsd.posDef_iff_isUnit.mpr hunit

/-- Conjugating a Cayley pair by an involution exchanges its two members and
therefore sends the Cayley transform to its inverse. -/
theorem grading_conjugate_positiveCayleyPair_eq_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M B J : Matrix ι ι ℂ) (hM : M.PosDef) (hB : B.PosDef)
    (hJ2 : J * J = 1) (hJMJ : J * M * J = B) :
    J * (M⁻¹ * B) * J = (M⁻¹ * B)⁻¹ := by
  letI : Invertible M := hM.isUnit.invertible
  letI : Invertible B := hB.isUnit.invertible
  have hJunit : IsUnit J := IsUnit.of_mul_eq_one J hJ2
  letI : Invertible J := hJunit.invertible
  have hJinv : J⁻¹ = J := by
    simpa using
      (Matrix.inv_mul_eq_iff_eq_mul_of_invertible J
        (1 : Matrix ι ι ℂ) J).2 hJ2.symm
  have hJBJ : J * B * J = M := by
    rw [← hJMJ]
    calc
      J * (J * M * J) * J = (J * J) * M * (J * J) := by
        noncomm_ring
      _ = M := by rw [hJ2, Matrix.one_mul, Matrix.mul_one]
  have hJMinvJ : J * M⁻¹ * J = B⁻¹ := by
    rw [← hJMJ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hJinv]
    simp only [Matrix.mul_assoc]
  calc
    J * (M⁻¹ * B) * J =
        (J * M⁻¹ * J) * (J * B * J) := by
      calc
        J * (M⁻¹ * B) * J = J * M⁻¹ * B * J := by
          simp only [Matrix.mul_assoc]
        _ = J * M⁻¹ * (J * J) * B * J := by
          rw [hJ2, Matrix.mul_one]
        _ = (J * M⁻¹ * J) * (J * B * J) := by
          simp only [Matrix.mul_assoc]
    _ = B⁻¹ * M := by rw [hJMinvJ, hJBJ]
    _ = (M⁻¹ * B)⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible]

/-- The inverse of the first member is exactly `(I+S)/2`. -/
theorem positiveCayleyPair_inv_eq_half_one_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M B : Matrix ι ι ℂ) (hM : M.PosDef)
    (hBaff : B = (2 : ℂ) • (1 : Matrix ι ι ℂ) - M) :
    M⁻¹ = ((2 : ℂ)⁻¹) • (1 + M⁻¹ * B) := by
  letI : Invertible M := hM.isUnit.invertible
  have hMB : M⁻¹ * B = (2 : ℂ) • M⁻¹ - 1 := by
    simp only [hBaff, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.mul_one, Matrix.inv_mul_of_invertible]
  rw [hMB]
  module

theorem h11COEBlockCayley_posDef_of_support
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (h11COEBlockCayley C).PosDef := by
  unfold h11COEBlockCayley
  exact positiveCayleyPair_posDef
    (h11COEBlockM C) (h11COEBlockB C)
    (h11COEBlockM_posDef_of_support C hsupport)
    (h11COEBlockB_posDef_of_support C hsupport)
    (h11COEBlockB_eq_two_one_sub_M C)

theorem h11COEBlockGrading_conjugate_Cayley_eq_inv
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    h11COEBlockGrading N * h11COEBlockCayley C *
        h11COEBlockGrading N =
      (h11COEBlockCayley C)⁻¹ := by
  unfold h11COEBlockCayley
  exact grading_conjugate_positiveCayleyPair_eq_inv
    (h11COEBlockM C) (h11COEBlockB C) (h11COEBlockGrading N)
    (h11COEBlockM_posDef_of_support C hsupport)
    (h11COEBlockB_posDef_of_support C hsupport)
    (h11COEBlockGrading_sq N)
    (h11COEBlockGrading_conjugate_M C)

theorem h11COEBlockM_inv_eq_half_one_add_Cayley
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (h11COEBlockM C)⁻¹ =
      ((2 : ℂ)⁻¹) • (1 + h11COEBlockCayley C) := by
  unfold h11COEBlockCayley
  exact positiveCayleyPair_inv_eq_half_one_add
    (h11COEBlockM C) (h11COEBlockB C)
    (h11COEBlockM_posDef_of_support C hsupport)
    (h11COEBlockB_eq_two_one_sub_M C)

/-- The complete fourth Jacobi trace polynomial of the literal doubled COE
block is nonpositive along every Hermitian doubled direction. -/
theorem trace_h11COEBlockFourthJacobiMatrix_re_nonpos
    {N : ℕ} (C Q : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) (hQ : Q.IsHermitian) :
    (Matrix.trace
      (h11BlockFourthJacobiMatrix
        (h11COEBlockM C)⁻¹ (h11COEBlockDirection Q))).re ≤ 0 := by
  rw [h11COEBlockM_inv_eq_half_one_add_Cayley C hsupport]
  exact
    trace_h11BlockFourthJacobiMatrix_re_nonpos_of_cayley_grading
      (h11COEBlockDirection Q) (h11COEBlockCayley C)
      (h11COEBlockGrading N)
      (h11COEBlockDirection_isHermitian Q hQ)
      (h11COEBlockCayley_posDef_of_support C hsupport)
      (h11COEBlockGrading_isHermitian N)
      (h11COEBlockGrading_sq N)
      (h11COEBlockGrading_conjugate_Cayley_eq_inv C hsupport)
      (h11COEBlockDirection_commutes_grading Q)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
