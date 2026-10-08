import A4.TriangularColumnLaplace
import Mathlib.LinearAlgebra.Matrix.SchurComplement

open scoped BigOperators Matrix

noncomputable section

namespace A4Research

/-- The first-coordinate and remaining-coordinate decomposition. -/
def headTailEquiv (d : ℕ) : Unit ⊕ Fin d ≃ Fin (d + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv x := by cases x with
    | inl u => cases u; rfl
    | inr i => simp
  right_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem headTailEquiv_head (d : ℕ) (u : Unit) :
    headTailEquiv d (Sum.inl u) = 0 := rfl

@[simp] theorem headTailEquiv_tail (d : ℕ) (i : Fin d) :
    headTailEquiv d (Sum.inr i) = i.succ := rfl

/-- A symmetric matrix with one scalar border. -/
def matrixBorder {d : ℕ} (c : ℝ) (b : Fin d → ℝ)
    (D : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.of (Fin.cons (Fin.cons c b) (fun i => Fin.cons (b i) (D i)))

@[simp] theorem matrixBorder_head_head {d : ℕ} (c : ℝ) (b : Fin d → ℝ)
    (D : Matrix (Fin d) (Fin d) ℝ) : matrixBorder c b D 0 0 = c := by
  simp [matrixBorder]

@[simp] theorem matrixBorder_head_tail {d : ℕ} (c : ℝ) (b : Fin d → ℝ)
    (D : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    matrixBorder c b D 0 j.succ = b j := by simp [matrixBorder]

@[simp] theorem matrixBorder_tail_head {d : ℕ} (c : ℝ) (b : Fin d → ℝ)
    (D : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    matrixBorder c b D i.succ 0 = b i := by simp [matrixBorder]

@[simp] theorem matrixBorder_tail_tail {d : ℕ} (c : ℝ) (b : Fin d → ℝ)
    (D : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) :
    matrixBorder c b D i.succ j.succ = D i j := by simp [matrixBorder]

/-- Reindexing the finite border gives the usual two-by-two block matrix. -/
theorem matrixBorder_blocks {d : ℕ} (c : ℝ) (b : Fin d → ℝ)
    (D : Matrix (Fin d) (Fin d) ℝ) :
    (matrixBorder c b D).submatrix (headTailEquiv d) (headTailEquiv d) =
      Matrix.fromBlocks (Matrix.of (fun _ _ : Unit => c))
        (Matrix.of (fun _ : Unit => b)) (Matrix.of (fun i (_ : Unit) => b i)) D := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks]

/-- Exact determinant Schur factorization at an invertible tail. -/
theorem matrixBorder_det {d : ℕ} (c : ℝ) (b : Fin d → ℝ)
    {D : Matrix (Fin d) (Fin d) ℝ} (hD : IsUnit D) :
    Matrix.det (matrixBorder c b D) =
      Matrix.det D * (c - b ⬝ᵥ (D⁻¹ *ᵥ b)) := by
  let := hD.invertible
  rw [← Matrix.det_submatrix_equiv_self (headTailEquiv d), matrixBorder_blocks,
    Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
  congr 1
  simp only [Matrix.det_unique, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply,
    dotProduct, Matrix.mulVec]
  simp only [Finset.sum_mul, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A positive-definite finite border has a positive Schur scalar. -/
theorem matrixBorder_schur_pos {d : ℕ} (c : ℝ) (b : Fin d → ℝ)
    {D : Matrix (Fin d) (Fin d) ℝ} (hD : D.PosDef)
    (hfull : (matrixBorder c b D).PosDef) :
    0 < c - b ⬝ᵥ (D⁻¹ *ᵥ b) := by
  have hdet := hfull.det_pos
  rw [matrixBorder_det c b hD.isUnit] at hdet
  exact (mul_pos_iff.mp hdet).resolve_right (by simp [not_lt.mpr hD.det_pos.le]) |>.2

/-- The matrix remaining after removing the first coordinate. -/
def matrixTail {d : ℕ} (theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  theta.submatrix Fin.succ Fin.succ

/-- A symmetric tilt has a positive-definite tail gap whenever its full gap
is positive definite. -/
theorem matrixTail_gap_posDef {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (hgap : (1 - theta).PosDef) : (1 - matrixTail theta).PosDef := by
  have h : ((1 - theta).submatrix Fin.succ Fin.succ).PosDef :=
    hgap.submatrix (Fin.succ_injective d)
  have heq : (1 - theta).submatrix Fin.succ Fin.succ = 1 - matrixTail theta := by
    ext i j
    simp [matrixTail, Matrix.submatrix, Matrix.one_apply, Fin.succ_inj]
  exact heq ▸ h

theorem matrixTail_isHermitian {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (htheta : theta.IsHermitian) : (matrixTail theta).IsHermitian :=
  htheta.submatrix _

/-- The full gap in scalar-border form, with the minus sign on both edges. -/
theorem matrixGap_border {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (htheta : theta.IsHermitian) :
    1 - theta = matrixBorder (1 - theta 0 0)
      (fun i => -theta 0 i.succ) (1 - matrixTail theta) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j <;> simp [Fin.succ_ne_zero, eq_comm]
  · refine Fin.cases ?_ (fun j => ?_) j
    · have h := congrFun (congrFun htheta.eq 0) i.succ
      simpa using h
    · simp [matrixTail, Matrix.submatrix, Matrix.one_apply, Fin.succ_inj]

/-- SPD is exactly enough to obtain the column's strict scalar Laplace rate. -/
theorem matrixGap_schur_lt_one {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (htheta : theta.IsHermitian) (hgap : (1 - theta).PosDef) :
    theta 0 0 + (fun i => theta 0 i.succ) ⬝ᵥ
      ((1 - matrixTail theta)⁻¹ *ᵥ (fun i => theta 0 i.succ)) < 1 := by
  let b : Fin d → ℝ := fun i => theta 0 i.succ
  let c : ℝ := theta 0 0
  change c + b ⬝ᵥ ((1 - matrixTail theta)⁻¹ *ᵥ b) < 1
  have hpos : 0 < (1 - c) - (-b) ⬝ᵥ ((1 - matrixTail theta)⁻¹ *ᵥ (-b)) :=
    matrixBorder_schur_pos (1 - c) (-b) (matrixTail_gap_posDef hgap)
      (matrixGap_border htheta ▸ hgap)
  simp only [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg] at hpos
  linarith

/-- The determinant factor needed to telescope successive column transforms. -/
theorem matrixGap_det {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ}
    (htheta : theta.IsHermitian) (hgap : (1 - theta).PosDef) :
    Matrix.det (1 - theta) = Matrix.det (1 - matrixTail theta) *
      (1 - (theta 0 0 + (fun i => theta 0 i.succ) ⬝ᵥ
        ((1 - matrixTail theta)⁻¹ *ᵥ (fun i => theta 0 i.succ)))) := by
  let b : Fin d → ℝ := fun i => theta 0 i.succ
  let c : ℝ := theta 0 0
  have hborder : 1 - theta = matrixBorder (1 - c) (-b) (1 - matrixTail theta) :=
    matrixGap_border htheta
  rw [hborder, matrixBorder_det _ _ (matrixTail_gap_posDef hgap).isUnit]
  change _ = Matrix.det (1 - matrixTail theta) *
    (1 - (c + b ⬝ᵥ ((1 - matrixTail theta)⁻¹ *ᵥ b)))
  simp only [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  congr 1
  ring

end A4Research
