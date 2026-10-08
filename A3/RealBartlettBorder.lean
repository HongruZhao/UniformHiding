import A3.WishartCholeskyBlock
import A4.TriangularRecursiveBorder

open Matrix
open scoped BigOperators

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem wishartGramCoordinates_cons_realRankOne {d : ℕ} (p : ℝ) (z : Fin d → ℝ)
    (y : HermitianCoordinates d ℝ) (hp : 0 ≤ p) :
    hermitianMatrixOfCoordinates (wishartGramCoordinates (wishartCoordinatesCons p z y)) =
      Matrix.vecMulVec (Fin.cons (Real.sqrt p) z) (Fin.cons (Real.sqrt p) z) +
        A4Research.matrixEmbedTail (hermitianMatrixOfCoordinates (wishartGramCoordinates y)) := by
  rw [hermitianMatrixOf_wishartGramCoordinates, hermitianMatrixOf_wishartGramCoordinates]
  ext i j
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · simpa [Matrix.vecMulVec, A4Research.matrixEmbedTail, Real.mul_self_sqrt hp] using
        wishartGramMatrix_cons_zero_zero p z y hp
    · simpa [Matrix.vecMulVec, A4Research.matrixEmbedTail] using
        wishartGramMatrix_cons_zero_succ p z y j
  · refine Fin.cases ?_ (fun j ↦ ?_) j
    · rw [Matrix.mul_apply, Fin.sum_univ_succ]
      simp [Matrix.conjTranspose_apply, wishartCholeskyMatrix_cons_succ_zero,
        wishartCholeskyMatrix_cons_zero_zero, wishartCholeskyMatrix_cons_zero_succ,
        Matrix.vecMulVec, A4Research.matrixEmbedTail, mul_comm]
    · simpa [Matrix.vecMulVec, A4Research.matrixEmbedTail, add_comm] using
        wishartGramMatrix_cons_succ_succ p z y i j

theorem realBartlettBorderTilt_factor {d : ℕ}
    {theta : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ} (htheta : theta.IsHermitian)
    (p : ℝ) (z : Fin d → ℝ) (y : HermitianCoordinates d ℝ) (hp : 0 ≤ p) :
    Real.exp (theta * hermitianMatrixOfCoordinates
      (wishartGramCoordinates (wishartCoordinatesCons p z y))).trace =
      A4Research.bartlettColumnTilt (theta 0 0) (A4Research.matrixTail theta)
        (fun i ↦ theta 0 i.succ) p z *
        Real.exp (A4Research.matrixTail theta * hermitianMatrixOfCoordinates
          (wishartGramCoordinates y)).trace := by
  rw [wishartGramCoordinates_cons_realRankOne p z y hp,
    Matrix.mul_add, Matrix.trace_add, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    A4Research.matrixEmbedTail_trace, dotProduct_comm]
  rw [A4Research.matrixTilt_border htheta, A4Research.matrixBorder_quadratic,
    Real.sq_sqrt hp, Real.exp_add]
  rfl

end A3Research
