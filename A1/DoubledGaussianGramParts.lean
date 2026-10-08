import A1.DoubledGaussianLaw

open Matrix A3Research
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators

noncomputable section
namespace A1Research

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem doubledRealGramCoordinates_matrix {n m : ℕ}
    (G : Matrix (Fin n) (Fin m) ℂ) :
    doubledRealCoordinatesMatrix (doubledRealGramCoordinates G) =
      (doubledRealGaussianSumMatrix G).transpose * doubledRealGaussianSumMatrix G := by
  unfold doubledRealCoordinatesMatrix doubledRealGramCoordinates
  rw [hermitianMatrixOfCoordinates_projection _
    (Matrix.isHermitian_iff_isSymm.mpr (doubledRealGramMatrix_isSymm G))]
  ext i j
  simp [doubledRealGramMatrix, doubledRealGaussianMatrix, Matrix.submatrix,
    Matrix.mul_apply, Matrix.transpose_apply]

theorem doubledRealGramCoordinates_hermitianPart {n m : ℕ}
    (G : Matrix (Fin n) (Fin m) ℂ) :
    doubledHermitianPart (doubledRealCoordinatesMatrix (doubledRealGramCoordinates G)) =
      G.conjTranspose * G := by
  rw [doubledRealGramCoordinates_matrix]
  ext i j
  apply Complex.ext
  · simp [doubledHermitianPart, doubledRealGaussianSumMatrix, doubledRealRow,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, Complex.mul_re, Finset.sum_add_distrib]
  · simp [doubledHermitianPart, doubledRealGaussianSumMatrix, doubledRealRow,
      Matrix.mul_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
      Complex.im_sum, Complex.mul_im, sub_eq_add_neg, Finset.sum_add_distrib,
      Finset.sum_neg_distrib]

theorem doubledRealGramCoordinates_symmetricPart {n m : ℕ}
    (G : Matrix (Fin n) (Fin m) ℂ) :
    doubledSymmetricPart (doubledRealCoordinatesMatrix (doubledRealGramCoordinates G)) =
      G.transpose * G := by
  rw [doubledRealGramCoordinates_matrix]
  ext i j
  apply Complex.ext
  · simp [doubledSymmetricPart, doubledRealGaussianSumMatrix, doubledRealRow,
      Matrix.mul_apply, Matrix.transpose_apply, Complex.re_sum,
      Complex.mul_re, Finset.sum_sub_distrib]
  · simp [doubledSymmetricPart, doubledRealGaussianSumMatrix, doubledRealRow,
      Matrix.mul_apply, Matrix.transpose_apply, Complex.im_sum,
      Complex.mul_im, Finset.sum_add_distrib]

/-- The doubled-real independent-coordinate equivalence recovers the literal
Hermitian Gram and transpose Gram of the original circular Gaussian matrix. -/
theorem doubledRealCoordinatePair_Gram {n m : ℕ}
    (G : Matrix (Fin n) (Fin m) ℂ) :
    doubledRealCoordinatePairLinearEquiv m (doubledRealGramCoordinates G) =
      (hermitianCoordinateProjection (G.conjTranspose * G),
        A2Research.symmetricCoordinateProjection m (G.transpose * G)) := by
  change (hermitianCoordinateProjection (doubledHermitianPart
      (doubledRealCoordinatesMatrix (doubledRealGramCoordinates G))),
    A2Research.symmetricCoordinateProjection m (doubledSymmetricPart
      (doubledRealCoordinatesMatrix (doubledRealGramCoordinates G)))) = _
  rw [doubledRealGramCoordinates_hermitianPart, doubledRealGramCoordinates_symmetricPart]

end A1Research
