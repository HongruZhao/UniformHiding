import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7RankOneSupportAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7RankOneLineConditional
import Mathlib.Tactic

/-!
# Literal rank-one determinant ratio for H7

This module proves the matrix determinant identity left explicit in the
conditional rank-one-line reduction.  The calculation is pointwise in the
line parameter and uses only the open-ball support and symmetry of the COE
corner.
-/

open Function NormedSpace
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxHeartbeats 800000

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

def h7RankOneInverseFactor {N : ℕ}
    (v : ComplexUnitSphere N) (t : ℝ) : ConcreteMatrixState N :=
  1 + (((Real.exp (-t) - 1 : ℝ) : ℂ)) • complexRankOneProjection v

theorem h7ComplexRankOneProjection_isHermitian
    {N : ℕ} (v : ComplexUnitSphere N) :
    (complexRankOneProjection v).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [Matrix.conjTranspose_apply, complexRankOneProjection]
  ring

theorem h7RankOneInverseFactor_isHermitian
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ) :
    (h7RankOneInverseFactor v t).IsHermitian := by
  apply Matrix.isHermitian_one.add
  apply (h7ComplexRankOneProjection_isHermitian v).smul
  change star (((Real.exp (-t) - 1 : ℝ) : ℂ)) =
    (((Real.exp (-t) - 1 : ℝ) : ℂ))
  rw [RCLike.star_def, Complex.conj_ofReal]

theorem h7RankOneInverseFactor_sq
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ) :
    h7RankOneInverseFactor v t * h7RankOneInverseFactor v t =
      1 - (((1 - Real.exp (-t) ^ 2 : ℝ) : ℂ)) •
        complexRankOneProjection v := by
  have hP := complexRankOneProjection_mul_self v
  unfold h7RankOneInverseFactor
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hP, smul_smul]
  module
  <;> ring

theorem h7RankOneInverseFactor_det
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ) :
    (h7RankOneInverseFactor v t).det = (Real.exp (-t) : ℂ) := by
  let c : ℂ := ((Real.exp (-t) - 1 : ℝ) : ℂ)
  let u : Fin N → ℂ := c • v.1
  let w : Fin N → ℂ := h7StarVector v
  have hmatrix : h7RankOneInverseFactor v t =
      1 + Matrix.vecMulVec u w := by
    ext i j
    simp [h7RankOneInverseFactor, u, w, c, h7StarVector,
      complexRankOneProjection, Matrix.vecMulVec_apply]
  rw [hmatrix, Matrix.vecMulVec_eq (Unit),
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  change 1 + h7StarVector v ⬝ᵥ
      (((Real.exp (-t) - 1 : ℝ) : ℂ) • v.1) = _
  rw [dotProduct_smul, h7StarVector_dot_self]
  push_cast
  ring

theorem transposeCongruenceFlow_rankOne_inverse_eq
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (C : ConcreteMatrixState N) :
    transposeCongruenceFlow (t • complexRankOneProjection v) (-1 : ℝ) C =
      transposeCongruence (h7RankOneInverseFactor v t) C := by
  have hP := complexRankOneProjection_mul_self v
  have harg :
      ((((-1 : ℝ) : ℂ)) • (t • complexRankOneProjection v)) =
        (((-t : ℝ) : ℂ)) • complexRankOneProjection v := by
    ext i j
    simp [Matrix.smul_apply]
  have hexp : NormedSpace.exp (((-t : ℝ) : ℂ)) =
      ((Real.exp (-t) : ℝ) : ℂ) := by
    rw [← NormedSpace.ofReal_exp_ℝ_ℝ, ← Real.exp_eq_exp_ℝ]
  unfold transposeCongruenceFlow
  rw [harg, matrix_exp_smul_idempotent _ hP, hexp]
  unfold h7RankOneInverseFactor
  norm_cast

theorem h7RankOne_exp_scalar_identity (t : ℝ) :
    Real.exp (2 * t) * Real.exp (-t) ^ 2 = 1 := by
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  ring_nf
  simp

theorem h7RankOne_support_factorization
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N) :
    let C := unscaleCOECorner K A
    let E := h7RankOneInverseFactor v t
    let D := transposeCongruenceFlow
      (t • complexRankOneProjection v) (-1 : ℝ) C
    let α : ℝ := Real.exp (2 * t) - 1
    let β : ℝ := 1 - Real.exp (-t) ^ 2
    1 - D.conjTranspose * D =
      E.transpose *
        (h7SupportH K A + ((α : ℝ) : ℂ) •
            (complexRankOneProjection v).transpose +
          ((β : ℝ) : ℂ) •
            (C.conjTranspose * complexRankOneProjection v * C)) *
        E.transpose := by
  dsimp only
  let C := unscaleCOECorner K A
  let E := h7RankOneInverseFactor v t
  let P := complexRankOneProjection v
  let M := E.transpose
  let Q := P.transpose
  let α : ℝ := Real.exp (2 * t) - 1
  let β : ℝ := 1 - Real.exp (-t) ^ 2
  have hP : P * P = P := by
    simpa only [P] using complexRankOneProjection_mul_self v
  have hQ : Q * Q = Q := by
    have ht := congrArg Matrix.transpose hP
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Q] using ht
  have hEherm : E.IsHermitian := by
    simpa only [E] using h7RankOneInverseFactor_isHermitian v t
  have hMherm : M.IsHermitian := hEherm.transpose
  have hEsq : E * E = 1 - (((β : ℝ) : ℂ)) • P := by
    simpa only [E, P, β] using h7RankOneInverseFactor_sq v t
  have hMsq : M * M = 1 - (((β : ℝ) : ℂ)) • Q := by
    have ht := congrArg Matrix.transpose hEsq
    simpa only [Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.transpose_smul, M, Q] using ht
  have hMQ : M * Q = Q * M := by
    unfold M E Q P h7RankOneInverseFactor
    simp only [Matrix.transpose_add, Matrix.transpose_one,
      Matrix.transpose_smul]
    noncomm_ring
  have hscalar :
      ((α : ℂ) - (β : ℂ) - (α : ℂ) * (β : ℂ)) = 0 := by
    norm_cast
    dsimp only [α, β]
    have hqa := h7RankOne_exp_scalar_identity t
    nlinarith
  have hscalar' :
      ((α : ℂ) - (α : ℂ) * (β : ℂ) - (β : ℂ)) = 0 := by
    calc
      (α : ℂ) - (α : ℂ) * (β : ℂ) - (β : ℂ) =
          (α : ℂ) - (β : ℂ) - (α : ℂ) * (β : ℂ) := by ring
      _ = 0 := hscalar
  have hcoeffMat :
      (α : ℂ) • Q - ((α : ℂ) * (β : ℂ)) • Q - (β : ℂ) • Q = 0 := by
    rw [← sub_smul, ← sub_smul, hscalar', zero_smul]
  have hcancel :
      M * (1 + ((α : ℝ) : ℂ) • Q) * M = 1 := by
    calc
      M * (1 + ((α : ℝ) : ℂ) • Q) * M =
          (1 + ((α : ℝ) : ℂ) • Q) * (M * M) := by
            rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
              Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, hMQ]
            noncomm_ring
      _ = (1 + ((α : ℝ) : ℂ) • Q) *
          (1 - ((β : ℝ) : ℂ) • Q) := by rw [hMsq]
      _ = 1 + ((α : ℂ) • Q - ((α : ℂ) * (β : ℂ)) • Q -
          (β : ℂ) • Q) := by
        simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul,
          Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hQ, smul_smul]
        module
      _ = 1 := by rw [hcoeffMat, add_zero]
  rw [transposeCongruenceFlow_rankOne_inverse_eq]
  unfold transposeCongruence
  change 1 - (E * C * M).conjTranspose * (E * C * M) = _
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hMherm.eq, hEherm.eq]
  calc
    _ =
        1 - M * C.conjTranspose * (E * E) * C * M := by noncomm_ring
    _ = 1 - M * C.conjTranspose *
          (1 - ((β : ℝ) : ℂ) • P) * C * M := by rw [hEsq]
    _ = M * (1 + ((α : ℝ) : ℂ) • Q) * M -
          M * C.conjTranspose *
            (1 - ((β : ℝ) : ℂ) • P) * C * M := by rw [hcancel]
    _ = M *
        (h7SupportH K A + ((α : ℝ) : ℂ) • Q +
          ((β : ℝ) : ℂ) •
            (C.conjTranspose * P * C)) * M := by
      unfold h7SupportH C
      noncomm_ring

theorem h7Matrix_mul_mul_apply_rect
    {l m n o α : Type*} [Fintype m] [Fintype n]
    [NonUnitalSemiring α]
    (A : Matrix l m α) (B : Matrix m n α) (C : Matrix n o α)
    (i : l) (j : o) :
    (A * B * C) i j = A i ⬝ᵥ (B *ᵥ (C.transpose j)) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rfl

def h7RankOneUpdateU {N : ℕ} (K : ℕ)
    (v : ComplexUnitSphere N) (t : ℝ) (A : ConcreteMatrixState N) :
    Matrix (Fin N) (Fin 2) ℂ :=
  let C := unscaleCOECorner K A
  let α : ℝ := Real.exp (2 * t) - 1
  let β : ℝ := 1 - Real.exp (-t) ^ 2
  fun i j ↦ ![
    ((α : ℝ) : ℂ) * h7StarVector v i,
    ((β : ℝ) : ℂ) * (C.conjTranspose *ᵥ v.1) i] j

def h7RankOneUpdateV {N : ℕ} (K : ℕ)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N) :
    Matrix (Fin 2) (Fin N) ℂ :=
  let C := unscaleCOECorner K A
  fun j i ↦ ![v.1 i, (h7StarVector v ᵥ* C) i] j

theorem h7RankOne_update_mul
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N) :
    let C := unscaleCOECorner K A
    let α : ℝ := Real.exp (2 * t) - 1
    let β : ℝ := 1 - Real.exp (-t) ^ 2
    h7RankOneUpdateU K v t A * h7RankOneUpdateV K v A =
      ((α : ℝ) : ℂ) • (complexRankOneProjection v).transpose +
        ((β : ℝ) : ℂ) •
          (C.conjTranspose * complexRankOneProjection v * C) := by
  dsimp only
  let C := unscaleCOECorner K A
  let α : ℝ := Real.exp (2 * t) - 1
  let β : ℝ := 1 - Real.exp (-t) ^ 2
  let sv := h7StarVector v
  let u₂ := C.conjTranspose *ᵥ v.1
  let w₂ := sv ᵥ* C
  have houter :
      h7RankOneUpdateU K v t A * h7RankOneUpdateV K v A =
        Matrix.vecMulVec (((α : ℂ)) • sv) v.1 +
          Matrix.vecMulVec (((β : ℂ)) • u₂) w₂ := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    simp [h7RankOneUpdateU, h7RankOneUpdateV, C, α, β, sv, u₂, w₂,
      Matrix.vecMulVec_apply]
    ring
  have hPouter : complexRankOneProjection v =
      Matrix.vecMulVec v.1 sv := by
    ext i j
    rfl
  have hPTouter : (complexRankOneProjection v).transpose =
      Matrix.vecMulVec sv v.1 := by
    rw [hPouter, Matrix.transpose_vecMulVec]
  have hCPouter :
      C.conjTranspose * complexRankOneProjection v * C =
        Matrix.vecMulVec u₂ w₂ := by
    rw [hPouter, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  rw [houter, hPTouter, hCPouter]
  rw [Matrix.smul_vecMulVec, Matrix.smul_vecMulVec]

theorem h7RankOne_smallMatrix_00
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h7RankOneUpdateV K v A * (h7SupportH K A)⁻¹ *
        h7RankOneUpdateU K v t A) 0 0 =
      (((Real.exp (2 * t) - 1) *
        (1 + concreteCOEX v K A) : ℝ) : ℂ) := by
  calc
    (h7RankOneUpdateV K v A * (h7SupportH K A)⁻¹ *
        h7RankOneUpdateU K v t A) 0 0 =
      h7RankOneUpdateV K v A 0 ⬝ᵥ
        ((h7SupportH K A)⁻¹ *ᵥ
          (h7RankOneUpdateU K v t A).transpose 0) :=
      h7Matrix_mul_mul_apply_rect
        (h7RankOneUpdateV K v A) ((h7SupportH K A)⁻¹)
        (h7RankOneUpdateU K v t A) 0 0
    _ = (((Real.exp (2 * t) - 1) *
        (1 + concreteCOEX v K A) : ℝ) : ℂ) := by
      change v.1 ⬝ᵥ ((h7SupportH K A)⁻¹ *ᵥ
        (((Real.exp (2 * t) - 1 : ℝ) : ℂ) • h7StarVector v)) = _
      rw [Matrix.mulVec_smul, dotProduct_smul,
        h7SupportH_inv_plain_star_pair v A hsymm hsupport]
      push_cast
      ring

theorem h7RankOne_smallMatrix_11
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h7RankOneUpdateV K v A * (h7SupportH K A)⁻¹ *
        h7RankOneUpdateU K v t A) 1 1 =
      (((1 - Real.exp (-t) ^ 2) * concreteCOEX v K A : ℝ) : ℂ) := by
  calc
    (h7RankOneUpdateV K v A * (h7SupportH K A)⁻¹ *
        h7RankOneUpdateU K v t A) 1 1 =
      h7RankOneUpdateV K v A 1 ⬝ᵥ
        ((h7SupportH K A)⁻¹ *ᵥ
          (h7RankOneUpdateU K v t A).transpose 1) :=
      h7Matrix_mul_mul_apply_rect
        (h7RankOneUpdateV K v A) ((h7SupportH K A)⁻¹)
        (h7RankOneUpdateU K v t A) 1 1
    _ = (((1 - Real.exp (-t) ^ 2) * concreteCOEX v K A : ℝ) : ℂ) := by
      change (h7StarVector v ᵥ* unscaleCOECorner K A) ⬝ᵥ
        ((h7SupportH K A)⁻¹ *ᵥ
          (((1 - Real.exp (-t) ^ 2 : ℝ) : ℂ) •
            ((unscaleCOECorner K A).conjTranspose *ᵥ v.1))) = _
      rw [Matrix.mulVec_smul, dotProduct_smul,
        h7SupportH_inv_C_pair v A hsupport]
      push_cast
      ring

theorem h7RankOne_smallMatrix_01
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h7RankOneUpdateV K v A * (h7SupportH K A)⁻¹ *
        h7RankOneUpdateU K v t A) 0 1 =
      ((1 - Real.exp (-t) ^ 2 : ℝ) : ℂ) *
        star (concreteCOEB v K A) := by
  calc
    (h7RankOneUpdateV K v A * (h7SupportH K A)⁻¹ *
        h7RankOneUpdateU K v t A) 0 1 =
      h7RankOneUpdateV K v A 0 ⬝ᵥ
        ((h7SupportH K A)⁻¹ *ᵥ
          (h7RankOneUpdateU K v t A).transpose 1) :=
      h7Matrix_mul_mul_apply_rect
        (h7RankOneUpdateV K v A) ((h7SupportH K A)⁻¹)
        (h7RankOneUpdateU K v t A) 0 1
    _ = ((1 - Real.exp (-t) ^ 2 : ℝ) : ℂ) *
        star (concreteCOEB v K A) := by
      change v.1 ⬝ᵥ ((h7SupportH K A)⁻¹ *ᵥ
        (((1 - Real.exp (-t) ^ 2 : ℝ) : ℂ) •
          ((unscaleCOECorner K A).conjTranspose *ᵥ v.1))) = _
      rw [Matrix.mulVec_smul, dotProduct_smul,
        h7SupportH_inv_starB_pair v A hsupport]
      rfl

theorem h7RankOne_smallMatrix_10
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h7RankOneUpdateV K v A * (h7SupportH K A)⁻¹ *
        h7RankOneUpdateU K v t A) 1 0 =
      ((Real.exp (2 * t) - 1 : ℝ) : ℂ) * concreteCOEB v K A := by
  calc
    (h7RankOneUpdateV K v A * (h7SupportH K A)⁻¹ *
        h7RankOneUpdateU K v t A) 1 0 =
      h7RankOneUpdateV K v A 1 ⬝ᵥ
        ((h7SupportH K A)⁻¹ *ᵥ
          (h7RankOneUpdateU K v t A).transpose 0) :=
      h7Matrix_mul_mul_apply_rect
        (h7RankOneUpdateV K v A) ((h7SupportH K A)⁻¹)
        (h7RankOneUpdateU K v t A) 1 0
    _ = ((Real.exp (2 * t) - 1 : ℝ) : ℂ) * concreteCOEB v K A := by
      change (h7StarVector v ᵥ* unscaleCOECorner K A) ⬝ᵥ
        ((h7SupportH K A)⁻¹ *ᵥ
          (((Real.exp (2 * t) - 1 : ℝ) : ℂ) • h7StarVector v)) = _
      rw [Matrix.mulVec_smul, dotProduct_smul,
        h7SupportH_inv_B_pair v A hsupport]
      rfl

theorem h7RankOne_smallMatrix_off_product
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (h7RankOneUpdateV K v A * (h7SupportH K A)⁻¹ *
        h7RankOneUpdateU K v t A) 0 1 *
      (h7RankOneUpdateV K v A * (h7SupportH K A)⁻¹ *
        h7RankOneUpdateU K v t A) 1 0 =
      ((((Real.exp (2 * t) - 1) * (1 - Real.exp (-t) ^ 2) *
        concreteCOEW v K A : ℝ)) : ℂ) := by
  rw [h7RankOne_smallMatrix_01 v t A hsupport,
    h7RankOne_smallMatrix_10 v t A hsupport]
  push_cast
  rw [show ((concreteCOEW v K A : ℝ) : ℂ) =
      star (concreteCOEB v K A) * concreteCOEB v K A by
    unfold concreteCOEW
    exact Complex.normSq_eq_conj_mul_self]
  ring

theorem h7RankOne_beta_eq_alpha_div_q (t : ℝ) :
    1 - Real.exp (-t) ^ 2 =
      (Real.exp (2 * t) - 1) / Real.exp (2 * t) := by
  have hq : Real.exp (2 * t) ≠ 0 := (Real.exp_pos _).ne'
  apply (eq_div_iff hq).2
  have hqa := h7RankOne_exp_scalar_identity t
  nlinarith

theorem h7RankOne_middle_scalar_identity
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N) :
    let q := Real.exp (2 * t)
    let α := q - 1
    let β := 1 - Real.exp (-t) ^ 2
    let x := concreteCOEX v K A
    let w := concreteCOEW v K A
    (1 + α * (1 + x)) * (1 + β * x) - α * β * w =
      q⁻¹ * concreteRankOneLikelihoodBracket K v t A := by
  dsimp only
  rw [h7RankOne_beta_eq_alpha_div_q t]
  have hq : Real.exp (2 * t) ≠ 0 := (Real.exp_pos _).ne'
  unfold concreteRankOneLikelihoodBracket
  dsimp only
  field_simp [hq]
  ring

theorem h7RankOne_middle_det
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    let C := unscaleCOECorner K A
    let α : ℝ := Real.exp (2 * t) - 1
    let β : ℝ := 1 - Real.exp (-t) ^ 2
    (h7SupportH K A + ((α : ℝ) : ℂ) •
          (complexRankOneProjection v).transpose +
        ((β : ℝ) : ℂ) •
          (C.conjTranspose * complexRankOneProjection v * C)).det =
      (h7SupportH K A).det *
        (((Real.exp (2 * t))⁻¹ *
          concreteRankOneLikelihoodBracket K v t A : ℝ) : ℂ) := by
  dsimp only
  let U := h7RankOneUpdateU K v t A
  let V := h7RankOneUpdateV K v A
  have hHdet : IsUnit (h7SupportH K A).det :=
    (Matrix.isUnit_iff_isUnit_det (h7SupportH K A)).mp
      (h7SupportH_isUnit A hsupport)
  have hdet := det_add_mul_fin_two_entries
    (h7SupportH K A) U V hHdet
    ((((Real.exp (2 * t) - 1) *
      (1 + concreteCOEX v K A) : ℝ)) : ℂ)
    ((((1 - Real.exp (-t) ^ 2) *
      concreteCOEX v K A : ℝ)) : ℂ)
    ((((Real.exp (2 * t) - 1) * (1 - Real.exp (-t) ^ 2) *
      concreteCOEW v K A : ℝ)) : ℂ)
    (by simpa only [U, V] using
      h7RankOne_smallMatrix_00 v t A hsymm hsupport)
    (by simpa only [U, V] using
      h7RankOne_smallMatrix_11 v t A hsupport)
    (by simpa only [U, V] using
      h7RankOne_smallMatrix_off_product v t A hsupport)
  have hupdate := h7RankOne_update_mul (K := K) v t A
  have hscalar := h7RankOne_middle_scalar_identity (K := K) v t A
  calc
    (h7SupportH K A +
          (((Real.exp (2 * t) - 1 : ℝ) : ℂ)) •
            (complexRankOneProjection v).transpose +
        (((1 - Real.exp (-t) ^ 2 : ℝ) : ℂ)) •
          ((unscaleCOECorner K A).conjTranspose *
            complexRankOneProjection v * unscaleCOECorner K A)).det =
      (h7SupportH K A + U * V).det := by
        rw [hupdate]
        rw [add_assoc]
    _ = (h7SupportH K A).det *
        (((1 + (Real.exp (2 * t) - 1) *
              (1 + concreteCOEX v K A)) *
            (1 + (1 - Real.exp (-t) ^ 2) * concreteCOEX v K A) -
          (Real.exp (2 * t) - 1) * (1 - Real.exp (-t) ^ 2) *
            concreteCOEW v K A : ℝ) : ℂ) := by
      rw [hdet]
      push_cast
      rfl
    _ = (h7SupportH K A).det *
        (((Real.exp (2 * t))⁻¹ *
          concreteRankOneLikelihoodBracket K v t A : ℝ) : ℂ) := by
      rw [hscalar]

theorem h7RankOne_outer_scalar_identity (t : ℝ) :
    Real.exp (-t) ^ 2 * (Real.exp (2 * t))⁻¹ = Real.exp (-4 * t) := by
  rw [pow_two, ← Real.exp_neg]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem h7RankOne_inverse_support_det
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    let C := unscaleCOECorner K A
    let D := transposeCongruenceFlow
      (t • complexRankOneProjection v) (-1 : ℝ) C
    (1 - D.conjTranspose * D).det =
      (h7SupportH K A).det *
        (((Real.exp (-4 * t) *
          concreteRankOneLikelihoodBracket K v t A : ℝ)) : ℂ) := by
  dsimp only
  have hfactor := h7RankOne_support_factorization (K := K) v t A
  have hmiddle := h7RankOne_middle_det (K := K) v t A hsymm hsupport
  dsimp only at hfactor hmiddle
  rw [hfactor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    h7RankOneInverseFactor_det, hmiddle]
  have hreal :
      Real.exp (-t) ^ 2 * (Real.exp (2 * t))⁻¹ *
          concreteRankOneLikelihoodBracket K v t A =
        Real.exp (-4 * t) *
          concreteRankOneLikelihoodBracket K v t A := by
    rw [h7RankOne_outer_scalar_identity]
  have hscalar :
      (((Real.exp (-t) ^ 2 * (Real.exp (2 * t))⁻¹ *
        concreteRankOneLikelihoodBracket K v t A : ℝ)) : ℂ) =
      (((Real.exp (-4 * t) *
        concreteRankOneLikelihoodBracket K v t A : ℝ)) : ℂ) :=
    congrArg (fun r : ℝ ↦ (r : ℂ)) hreal
  rw [← hscalar]
  push_cast
  ring

theorem h16GeneralCOEInverseDeterminant_rankOne_eq_mul
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    h16GeneralCOEInverseDeterminant K
        (t • complexRankOneProjection v) A =
      concreteCOEBaseDeterminant K A *
        (Real.exp (-4 * t) *
          concreteRankOneLikelihoodBracket K v t A) := by
  have hdet := h7RankOne_inverse_support_det v t A hsymm hsupport
  have hre := congrArg Complex.re hdet
  have hscaleRe :
      ((((Real.exp (-4 * t) *
        concreteRankOneLikelihoodBracket K v t A : ℝ)) : ℂ)).re =
        Real.exp (-4 * t) * concreteRankOneLikelihoodBracket K v t A :=
    Complex.ofReal_re _
  have hscaleIm :
      ((((Real.exp (-4 * t) *
        concreteRankOneLikelihoodBracket K v t A : ℝ)) : ℂ)).im = 0 :=
    Complex.ofReal_im _
  unfold h16GeneralCOEInverseDeterminant concreteCOEBaseDeterminant
  dsimp only
  simpa only [h7SupportH, Complex.mul_re, hscaleRe, hscaleIm,
    mul_zero, sub_zero] using hre

theorem h16GeneralCOEInverseDeterminant_rankOne_ratio
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    h16GeneralCOEInverseDeterminant K
          (t • complexRankOneProjection v) A /
        concreteCOEBaseDeterminant K A =
      Real.exp (-4 * t) * concreteRankOneLikelihoodBracket K v t A := by
  rw [h16GeneralCOEInverseDeterminant_rankOne_eq_mul
    v t A hsymm hsupport]
  have hbase : concreteCOEBaseDeterminant K A ≠ 0 :=
    ((RCLike.lt_iff_re_im.mp hsupport.det_pos).1).ne'
  field_simp [hbase]

theorem h16GeneralCOEInverseDeterminant_rankOne_eventuallyEq
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (fun t : ℝ =>
      h16GeneralCOEInverseDeterminant K
          (t • complexRankOneProjection v) A /
        concreteCOEBaseDeterminant K A) =ᶠ[nhds 0]
      (fun t : ℝ =>
        Real.exp (-4 * t) * concreteRankOneLikelihoodBracket K v t A) :=
  Filter.Eventually.of_forall fun t ↦
    h16GeneralCOEInverseDeterminant_rankOne_ratio
      v t A hsymm hsupport

theorem h16CoordinateLikelihoodCore_rankOne_iteratedDeriv_three_derived
    {N K : ℕ} (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    iteratedDeriv 3
        (fun t : ℝ => h16CoordinateLikelihoodCore K A
          (t • concreteMatrixRealCoordinates (complexRankOneProjection v))) 0 =
      concreteRankOneDensityScoreThree N K v A := by
  exact h16CoordinateLikelihoodCore_rankOne_iteratedDeriv_three_CONDITIONAL
    v A hsupport
      (h16GeneralCOEInverseDeterminant_rankOne_eventuallyEq
        v A hsymm hsupport)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
