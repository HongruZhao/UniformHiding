import A1.GaussianGramPairLaw
import A1.DoubledWishartKernel
import A1.CornerMeasurable

open Matrix MeasureTheory
open A3Research
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace A1Research

/-- The coordinate beta statistic is the literal original normalized transpose Gram, everywhere. -/
theorem normalizedComplexPairCoordinates_gaussianGramPair {n m : ℕ}
    (G : Matrix (Fin n) (Fin m) ℂ) :
    normalizedComplexPairCoordinates (gaussianGramPairCoordinates G) =
      normalizedTransposeGramCoordinates G := by
  unfold normalizedComplexPairCoordinates gaussianGramPairCoordinates
  dsimp only [Prod.fst, Prod.snd]
  have hs : complexSymmetricMatrixOfCoordinates
      (A2Research.symmetricCoordinateProjection m (G.transpose * G)) = G.transpose * G := by
    apply A2Research.symmetricCoordinateEmbedding_projection
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [hermitianMatrixOfCoordinates_projection _ (Matrix.isHermitian_conjTranspose_mul_self G), hs]
  rfl

end A1Research
