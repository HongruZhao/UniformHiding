import A3.Definitions
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Algebra.Star.BigOperators

open scoped BigOperators Matrix ComplexOrder

noncomputable section

namespace A3Research

open Matrix InnerProductSpace

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Gram--Schmidt keeps coefficient one on the original ordered basis vector. -/
theorem gramSchmidt_repr_self {K E I : Type*} [RCLike K]
    [NormedAddCommGroup E] [InnerProductSpace K E] [LinearOrder I]
    [LocallyFiniteOrderBot I] [WellFoundedLT I]
    (b : Module.Basis I K E) (i : I) : b.repr (gramSchmidt K b i) i = 1 := by
  have h := congrArg (fun x : E ↦ b.repr x i) (gramSchmidt_def'' K b i)
  simp only [map_add, map_sum, map_smul, Finsupp.add_apply,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at h
  have hz : ∑ j ∈ Finset.Iio i,
      (inner K (gramSchmidt K b j) (b i) / (‖gramSchmidt K b j‖ : K) ^ 2) *
        b.repr (gramSchmidt K b j) i = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [gramSchmidt_triangular (Finset.mem_Iio.mp hj) b, mul_zero]
  simpa only [hz, add_zero, Module.Basis.repr_self_apply, ite_true] using h.symm

variable {K : Type*} [RCLike K]
variable {I : Type*} [Fintype I] [LinearOrder I] [WellFoundedLT I] [LocallyFiniteOrderBot I]
variable {S : Matrix I I K}

theorem ldl_lowerInv_diag (hS : S.PosDef) (i : I) : LDL.lowerInv hS i i = 1 := by
  let := S.transpose.toNormedAddCommGroup hS.transpose
  let := S.transpose.toInnerProductSpace hS.transpose.posSemidef
  simpa only [Pi.basisFun_repr, LDL.lowerInv] using
    gramSchmidt_repr_self (Pi.basisFun K I) i

theorem ldl_lowerInv_triangular (hS : S.PosDef) :
    (LDL.lowerInv hS).IsLowerTriangular := by
  intro i j hij
  exact LDL.lowerInv_triangular hS hij

theorem ldl_lower_triangular (hS : S.PosDef) : (LDL.lower hS).IsLowerTriangular :=
  blockTriangular_inv_of_blockTriangular (ldl_lowerInv_triangular hS)

omit [WellFoundedLT I] [LocallyFiniteOrderBot I] in
theorem lowerTriangular_mul_diag {A B : Matrix I I K}
    (hA : A.IsLowerTriangular) (hB : B.IsLowerTriangular) (i : I) :
    (A * B) i i = A i i * B i i := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hj
    · rw [hB hj, mul_zero]
    · rw [hA hj, zero_mul]
  · simp

theorem ldl_lower_diag (hS : S.PosDef) (i : I) : LDL.lower hS i i = 1 := by
  have h := congrArg (fun A : Matrix I I K ↦ A i i)
    (Matrix.mul_inv_of_invertible (LDL.lowerInv hS))
  rw [← LDL.lower, lowerTriangular_mul_diag
    (ldl_lowerInv_triangular hS) (ldl_lower_triangular hS),
    ldl_lowerInv_diag, one_mul, Matrix.one_apply_eq] at h
  exact h

theorem ldl_diagEntries_pos (hS : S.PosDef) (i : I) : 0 < LDL.diagEntries hS i := by
  have hD : (LDL.diag hS).PosDef := by
    rw [LDL.diag_eq_lowerInv_conj]
    exact (isUnit_of_invertible (LDL.lowerInv hS)).posDef_star_right_conjugate_iff.mpr hS
  exact posDef_diagonal_iff.mp hD i

theorem ldl_diagEntries_re_pos (hS : S.PosDef) (i : I) :
    0 < RCLike.re (LDL.diagEntries hS i) :=
  (RCLike.pos_iff.mp (ldl_diagEntries_pos hS i)).1

theorem ldl_diagEntries_eq_ofReal_re (hS : S.PosDef) (i : I) :
    LDL.diagEntries hS i = (RCLike.re (LDL.diagEntries hS i) : K) := by
  apply RCLike.ext
  · simp
  · simp only [RCLike.ofReal_im]
    exact (RCLike.pos_iff.mp (ldl_diagEntries_pos hS i)).2

/-- The generic real/complex positive-diagonal Cholesky factor. -/
def wishartCholeskyDiagonal (hS : S.PosDef) : Matrix I I K :=
  diagonal (fun i ↦ (Real.sqrt (RCLike.re (LDL.diagEntries hS i)) : K))

def wishartCholesky (hS : S.PosDef) : Matrix I I K :=
  LDL.lower hS * wishartCholeskyDiagonal hS

theorem wishartCholeskyDiagonal_mul_conjTranspose (hS : S.PosDef) :
    wishartCholeskyDiagonal hS * (wishartCholeskyDiagonal hS).conjTranspose = LDL.diag hS := by
  simp only [wishartCholeskyDiagonal, Matrix.diagonal_conjTranspose, Pi.star_apply, RCLike.star_def,
    RCLike.conj_ofReal, diagonal_mul_diagonal, LDL.diag]
  congr 1
  funext i
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (ldl_diagEntries_re_pos hS i).le,
    ← ldl_diagEntries_eq_ofReal_re]

theorem wishartCholesky_triangular (hS : S.PosDef) :
    (wishartCholesky hS).IsLowerTriangular :=
  (ldl_lower_triangular hS).mul (blockTriangular_diagonal _)

theorem wishartCholesky_diag (hS : S.PosDef) (i : I) :
    wishartCholesky hS i i = (Real.sqrt (RCLike.re (LDL.diagEntries hS i)) : K) := by
  simp only [wishartCholesky, wishartCholeskyDiagonal, Matrix.mul_diagonal,
    ldl_lower_diag, one_mul]

theorem wishartCholesky_diag_re_pos (hS : S.PosDef) (i : I) :
    0 < RCLike.re (wishartCholesky hS i i) := by
  rw [wishartCholesky_diag, RCLike.ofReal_re]
  exact Real.sqrt_pos.mpr (ldl_diagEntries_re_pos hS i)

theorem wishartCholesky_diag_im_zero (hS : S.PosDef) (i : I) :
    RCLike.im (wishartCholesky hS i i) = 0 := by
  rw [wishartCholesky_diag, RCLike.ofReal_im]

theorem wishartCholesky_mul_conjTranspose (hS : S.PosDef) :
    wishartCholesky hS * (wishartCholesky hS).conjTranspose = S := by
  simp only [wishartCholesky, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (wishartCholeskyDiagonal hS),
    wishartCholeskyDiagonal_mul_conjTranspose]
  simpa only [Matrix.mul_assoc] using LDL.lower_conj_diag hS

theorem wishartCholesky_isUnit (hS : S.PosDef) : IsUnit (wishartCholesky hS) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_of_isLowerTriangular _ (wishartCholesky_triangular hS)]
  rw [Finset.prod_ne_zero_iff]
  intro i _ hzero
  have hz := congrArg RCLike.re hzero
  exact (wishartCholesky_diag_re_pos hS i).ne' (by simpa using hz)

/-- The Cholesky pivot identity holds over both original fields. -/
theorem det_eq_ldl_pivot_product (hS : S.PosDef) :
    S.det = ∏ i, LDL.diagEntries hS i := by
  conv_lhs => rw [← wishartCholesky_mul_conjTranspose hS]
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_of_isLowerTriangular _ (wishartCholesky_triangular hS)]
  rw [star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [wishartCholesky_diag]
  simp only [RCLike.star_def, RCLike.conj_ofReal]
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt (ldl_diagEntries_re_pos hS i).le,
    ← ldl_diagEntries_eq_ofReal_re]

end A3Research
