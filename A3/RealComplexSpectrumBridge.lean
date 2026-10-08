import A3.RealComplexMatrixBridge

open Matrix Polynomial
open scoped BigOperators

noncomputable section
namespace A3Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem realMatrixComplexEmbedding_eigenvalues_permutation {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    ∃ sigma : Equiv.Perm (Fin n),
      (realMatrixComplexEmbedding_isHermitian hA).eigenvalues = hA.eigenvalues ∘ sigma := by
  apply eigenvalues_permutation_of_charpoly_eq
    (realMatrixComplexEmbedding_isHermitian hA) hA.eigenvalues
  rw [realMatrixComplexEmbedding, Matrix.charpoly_map, hA.charpoly_eq]
  simp [realRootPolynomial, Polynomial.map_prod]

theorem canonicalHermitianSpectrum_realEmbedding_permutation {n : ℕ}
    (x : HermitianCoordinates n ℝ) :
    ∃ sigma : Equiv.Perm (Fin n),
      canonicalHermitianSpectrum (realHermitianCoordinatesEmbedding x) =
        canonicalHermitianSpectrum x ∘ sigma := by
  have h := realMatrixComplexEmbedding_eigenvalues_permutation
    (hermitianMatrixOfCoordinates_isHermitian x)
  rcases h with ⟨sigma, hsigma⟩
  refine ⟨sigma, ?_⟩
  exact (hermitian_eigenvalues_congr
    (hermitianMatrixOfCoordinates_isHermitian (realHermitianCoordinatesEmbedding x))
    (realMatrixComplexEmbedding_isHermitian (hermitianMatrixOfCoordinates_isHermitian x))
    (hermitianMatrixOfCoordinates_realEmbedding x)).trans hsigma

theorem symmetric_test_canonicalHermitianSpectrum_realEmbedding
    {n : ℕ} {gamma : Type} (F : (Fin n → ℝ) → gamma)
    (hF : LogdetLean.GramHafnian.UltimateHiding.DenseScore.IsA2SymmetricTest F)
    (x : HermitianCoordinates n ℝ) :
    F (canonicalHermitianSpectrum (realHermitianCoordinatesEmbedding x)) =
      F (canonicalHermitianSpectrum x) := by
  rcases canonicalHermitianSpectrum_realEmbedding_permutation x with ⟨sigma, hsigma⟩
  rw [hsigma]
  exact hF sigma (canonicalHermitianSpectrum x)

end A3Research
