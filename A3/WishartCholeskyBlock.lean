import A3.WishartCholeskySplit

open Matrix
open scoped BigOperators

noncomputable section

namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K : Type*} [RCLike K]

def wishartRankOneCoordinates (z : Fin n → K) : HermitianCoordinates n K :=
  hermitianCoordinateProjection (vecMulVec (star z) z)

theorem wishartGramMatrix_cons_zero_zero (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (hp : 0 ≤ p) :
    (wishartCholeskyMatrix (wishartCoordinatesCons p z y) *
      (wishartCholeskyMatrix (wishartCoordinatesCons p z y)).conjTranspose) 0 0 = (p : K) := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [Matrix.conjTranspose_apply, wishartCholeskyMatrix_cons_zero_zero,
    wishartCholeskyMatrix_cons_zero_succ, star_zero, mul_zero, Finset.sum_const_zero,
    add_zero, RCLike.star_def, RCLike.conj_ofReal]
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt hp]

theorem wishartGramMatrix_cons_zero_succ (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (j : Fin n) :
    (wishartCholeskyMatrix (wishartCoordinatesCons p z y) *
      (wishartCholeskyMatrix (wishartCoordinatesCons p z y)).conjTranspose) 0 j.succ =
        (Real.sqrt p : K) * z j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [Matrix.conjTranspose_apply, wishartCholeskyMatrix_cons_zero_zero,
    wishartCholeskyMatrix_cons_succ_zero, wishartCholeskyMatrix_cons_zero_succ,
    star_star, zero_mul, Finset.sum_const_zero, add_zero]

theorem wishartGramMatrix_cons_succ_succ (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (i j : Fin n) :
    (wishartCholeskyMatrix (wishartCoordinatesCons p z y) *
      (wishartCholeskyMatrix (wishartCoordinatesCons p z y)).conjTranspose) i.succ j.succ =
        star (z i) * z j + (wishartCholeskyMatrix y * (wishartCholeskyMatrix y).conjTranspose) i j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [Matrix.conjTranspose_apply, wishartCholeskyMatrix_cons_succ_zero,
    wishartCholeskyMatrix_cons_succ_succ, star_star, Matrix.mul_apply]

/-- The exact first-column Cholesky recursion, for both fields. -/
theorem wishartGramCoordinates_cons (p : ℝ) (z : Fin n → K)
    (y : HermitianCoordinates n K) (hp : 0 ≤ p) :
    wishartCoordinatesSplit (wishartGramCoordinates (wishartCoordinatesCons p z y)) =
      (p, ((Real.sqrt p) • z, wishartGramCoordinates y + wishartRankOneCoordinates z)) := by
  apply Prod.ext
  · dsimp [wishartCoordinatesSplit, wishartGramCoordinates, hermitianCoordinateProjection]
    rw [wishartGramMatrix_cons_zero_zero p z y hp, RCLike.ofReal_re]
  · apply Prod.ext
    · funext j
      dsimp [wishartCoordinatesSplit, wishartGramCoordinates, hermitianCoordinateProjection]
      rw [wishartGramMatrix_cons_zero_succ, RCLike.real_smul_eq_coe_mul]
    · apply Prod.ext
      · funext i
        dsimp [wishartCoordinatesSplit, wishartGramCoordinates,
          wishartRankOneCoordinates, hermitianCoordinateProjection, Matrix.vecMulVec]
        rw [wishartGramMatrix_cons_succ_succ, map_add, add_comm]
        rfl
      · funext ij
        dsimp [wishartCoordinatesSplit, wishartGramCoordinates,
          wishartRankOneCoordinates, hermitianCoordinateProjection, Matrix.vecMulVec]
        rw [wishartGramMatrix_cons_succ_succ, add_comm]
        rfl

end A3Research
