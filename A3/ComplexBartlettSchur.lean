import A3.ComplexBartlettColumnLaplace
import A4.TriangularSchurComplement

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def complexMatrixBorder {d : ℕ} (c : ℂ) (b : Fin d → ℂ)
    (D : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.of (Fin.cons (Fin.cons c b) (fun i ↦ Fin.cons (star (b i)) (D i)))

theorem complexMatrixBorder_blocks {d : ℕ} (c : ℂ) (b : Fin d → ℂ)
    (D : Matrix (Fin d) (Fin d) ℂ) :
    (complexMatrixBorder c b D).submatrix (A4Research.headTailEquiv d) (A4Research.headTailEquiv d) =
      Matrix.fromBlocks (Matrix.of (fun _ _ : Unit ↦ c))
        (Matrix.of (fun _ : Unit ↦ b)) (Matrix.of (fun i (_ : Unit) ↦ star (b i))) D := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks, complexMatrixBorder]

theorem complexMatrixBorder_det {d : ℕ} (c : ℂ) (b : Fin d → ℂ)
    {D : Matrix (Fin d) (Fin d) ℂ} (hD : IsUnit D) :
    (complexMatrixBorder c b D).det = D.det *
      (c - star b ⬝ᵥ ((D.transpose)⁻¹ *ᵥ b)) := by
  letI := hD.invertible
  rw [← Matrix.det_submatrix_equiv_self (A4Research.headTailEquiv d),
    complexMatrixBorder_blocks, Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv,
    ← Matrix.transpose_nonsing_inv]
  congr 1
  simp only [Matrix.det_unique, Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply,
    dotProduct, Matrix.mulVec, Matrix.transpose_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem complexMatrixBorder_det_re {d : ℕ} (c : ℂ) (b : Fin d → ℂ)
    {D : Matrix (Fin d) (Fin d) ℂ} (hD : D.PosDef) :
    (complexMatrixBorder c b D).det.re = D.det.re *
      (c.re - (star b ⬝ᵥ ((D.transpose)⁻¹ *ᵥ b)).re) := by
  rw [complexMatrixBorder_det c b hD.isUnit, Complex.mul_re, Complex.sub_re]
  have hd : D.det.im = 0 := (Complex.pos_iff.mp hD.det_pos).2.symm
  rw [hd, zero_mul, sub_zero]

theorem complexMatrixBorder_schur_pos {d : ℕ} (c : ℂ) (b : Fin d → ℂ)
    {D : Matrix (Fin d) (Fin d) ℂ} (hD : D.PosDef)
    (hfull : (complexMatrixBorder c b D).PosDef) :
    0 < c.re - (star b ⬝ᵥ ((D.transpose)⁻¹ *ᵥ b)).re := by
  have hdet := complex_posDef_det_re_pos hfull
  rw [complexMatrixBorder_det_re c b hD] at hdet
  exact (mul_pos_iff_of_pos_left (complex_posDef_det_re_pos hD)).mp hdet

def complexMatrixTail {d : ℕ} (theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Matrix (Fin d) (Fin d) ℂ := theta.submatrix Fin.succ Fin.succ

theorem complexMatrixTail_gap_posDef {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (hgap : (1 - theta).PosDef) : (1 - complexMatrixTail theta).PosDef := by
  have h := hgap.submatrix (Fin.succ_injective d)
  have heq : (1 - theta).submatrix Fin.succ Fin.succ = 1 - complexMatrixTail theta := by
    ext i j
    simp [complexMatrixTail, Matrix.submatrix, Matrix.one_apply, Fin.succ_inj]
  exact heq ▸ h

theorem complexMatrixTail_isHermitian {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (htheta : theta.IsHermitian) :
    (complexMatrixTail theta).IsHermitian := htheta.submatrix _

theorem complexMatrixGap_border {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ} (htheta : theta.IsHermitian) :
    1 - theta = complexMatrixBorder (1 - theta 0 0)
      (fun i ↦ -theta 0 i.succ) (1 - complexMatrixTail theta) := by
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · refine Fin.cases ?_ (fun j ↦ ?_) j <;>
      simp [complexMatrixBorder, Fin.succ_ne_zero, eq_comm]
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · simpa [complexMatrixBorder] using congrArg Neg.neg (htheta.apply i.succ 0).symm
    · simp [complexMatrixBorder, complexMatrixTail, Matrix.submatrix,
        Matrix.one_apply, Fin.succ_inj]

theorem complexQuadratic_neg {d : ℕ} (D : Matrix (Fin d) (Fin d) ℂ) (b : Fin d → ℂ) :
    (star (fun i ↦ -b i) ⬝ᵥ (D *ᵥ (fun i ↦ -b i))).re = (star b ⬝ᵥ (D *ᵥ b)).re := by
  change (star (-b) ⬝ᵥ (D *ᵥ (-b))).re = _
  rw [star_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

theorem complexMatrixGap_schur_lt_one {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (htheta : theta.IsHermitian) (hgap : (1 - theta).PosDef) :
    (theta 0 0).re + (star (fun i ↦ theta 0 i.succ) ⬝ᵥ
      ((1 - (complexMatrixTail theta).transpose)⁻¹ *ᵥ (fun i ↦ theta 0 i.succ))).re < 1 := by
  have hp := complexMatrixBorder_schur_pos (1 - theta 0 0)
    (fun i ↦ -theta 0 i.succ) (complexMatrixTail_gap_posDef hgap)
    (complexMatrixGap_border htheta ▸ hgap)
  simp only [Matrix.transpose_sub, Matrix.transpose_one, complexQuadratic_neg,
    Complex.sub_re, Complex.one_re] at hp
  linarith

theorem complexMatrixGap_det_re {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ}
    (htheta : theta.IsHermitian) (hgap : (1 - theta).PosDef) :
    (1 - theta).det.re = (1 - complexMatrixTail theta).det.re *
      (1 - ((theta 0 0).re + (star (fun i ↦ theta 0 i.succ) ⬝ᵥ
        ((1 - (complexMatrixTail theta).transpose)⁻¹ *ᵥ (fun i ↦ theta 0 i.succ))).re)) := by
  conv_lhs => rw [complexMatrixGap_border htheta,
    complexMatrixBorder_det_re _ _ (complexMatrixTail_gap_posDef hgap)]
  simp only [Matrix.transpose_sub, Matrix.transpose_one, complexQuadratic_neg,
    Complex.sub_re, Complex.one_re]
  ring

end A3Research
