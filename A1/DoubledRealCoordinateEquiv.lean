import A1.DoubledRealCoordinates

open Matrix
open A3Research
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped ComplexOrder Matrix.Norms.Elementwise

noncomputable section
namespace A1Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def doubledRealCoordinatesMatrix {m : ℕ} (x : HermitianCoordinates (2 * m) ℝ) :
    Matrix (DoubledIndex m) (DoubledIndex m) ℝ :=
  (hermitianMatrixOfCoordinates x).submatrix (doubledIndexEquiv m) (doubledIndexEquiv m)

def doubledRealCoordinatesMatrixLinearMap (m : ℕ) :
    HermitianCoordinates (2 * m) ℝ →ₗ[ℝ] Matrix (DoubledIndex m) (DoubledIndex m) ℝ :=
  (Matrix.reindexLinearEquiv ℝ ℝ (doubledIndexEquiv m).symm (doubledIndexEquiv m).symm).toLinearMap.comp
    (hermitianMatrixOfCoordinatesLinearMap (2 * m) ℝ)

theorem doubledRealCoordinatesMatrix_isSymm {m : ℕ} (x : HermitianCoordinates (2 * m) ℝ) :
    (doubledRealCoordinatesMatrix x).IsSymm :=
  (Matrix.isHermitian_iff_isSymm.mp (hermitianMatrixOfCoordinates_isHermitian x)).submatrix _

def doubledRealCoordinatePairLinearMap (m : ℕ) :
    HermitianCoordinates (2 * m) ℝ →ₗ[ℝ]
      HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m :=
  (LinearMap.prodMap (hermitianCoordinateProjectionLinearMap m ℂ)
      ((A2Research.symmetricCoordinateProjection m).restrictScalars ℝ)).comp
    ((doubledRealComplexPairMatrixLinearEquiv m).toLinearMap.comp
      (doubledRealCoordinatesMatrixLinearMap m))

def complexPairRealCoordinates {m : ℕ}
    (x : HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m) :
    HermitianCoordinates (2 * m) ℝ :=
  hermitianCoordinateProjection ((complexPairRealMatrix (hermitianMatrixOfCoordinates x.1)
    (complexSymmetricMatrixOfCoordinates x.2)).submatrix
      (doubledIndexEquiv m).symm (doubledIndexEquiv m).symm)

theorem doubledRealCoordinatePair_reconstruct {m : ℕ} (x : HermitianCoordinates (2 * m) ℝ) :
    (hermitianMatrixOfCoordinates (doubledRealCoordinatePairLinearMap m x).1,
      complexSymmetricMatrixOfCoordinates (doubledRealCoordinatePairLinearMap m x).2) =
        (doubledHermitianPart (doubledRealCoordinatesMatrix x),
          doubledSymmetricPart (doubledRealCoordinatesMatrix x)) := by
  apply Prod.ext
  · exact hermitianMatrixOfCoordinates_projection _
      (doubledHermitianPart_isHermitian _ (doubledRealCoordinatesMatrix_isSymm x))
  · exact A2Research.symmetricCoordinateEmbedding_projection _
      (doubledSymmetricPart_isSymm _ (doubledRealCoordinatesMatrix_isSymm x))

theorem doubledRealCoordinatesMatrix_complexPair {m : ℕ}
    (x : HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m) :
    doubledRealCoordinatesMatrix (complexPairRealCoordinates x) =
      complexPairRealMatrix (hermitianMatrixOfCoordinates x.1)
        (complexSymmetricMatrixOfCoordinates x.2) := by
  have hW := complexPairRealMatrix_isSymm (hermitianMatrixOfCoordinates x.1)
    (complexSymmetricMatrixOfCoordinates x.2) (hermitianMatrixOfCoordinates_isHermitian x.1)
    (complexSymmetricMatrixOfCoordinates_isSymm x.2)
  unfold doubledRealCoordinatesMatrix complexPairRealCoordinates
  rw [hermitianMatrixOfCoordinates_projection _
    (Matrix.isHermitian_iff_isSymm.mpr (hW.submatrix (doubledIndexEquiv m).symm))]
  ext i j
  simp [Matrix.submatrix]

theorem doubledRealCoordinatesMatrix_injective (m : ℕ) :
    Function.Injective (doubledRealCoordinatesMatrix (m := m)) := by
  intro x y h
  have hM : hermitianMatrixOfCoordinates x = hermitianMatrixOfCoordinates y := by
    ext i j
    have hi := congrArg (fun W ↦ W ((doubledIndexEquiv m).symm i)
      ((doubledIndexEquiv m).symm j)) h
    simpa [doubledRealCoordinatesMatrix, Matrix.submatrix] using hi
  have hp := congrArg (hermitianCoordinateProjection (n := 2 * m) (K := ℝ)) hM
  simpa only [hermitianCoordinateProjection_ofCoordinates] using hp

/-- The literal independent coordinates of real symmetric `2m × 2m` matrices
are linearly equivalent to Hermitian and complex symmetric `m × m` coordinates. -/
def doubledRealCoordinatePairLinearEquiv (m : ℕ) :
    HermitianCoordinates (2 * m) ℝ ≃ₗ[ℝ]
      HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m where
  toLinearMap := doubledRealCoordinatePairLinearMap m
  invFun := complexPairRealCoordinates
  left_inv x := by
    apply doubledRealCoordinatesMatrix_injective m
    rw [doubledRealCoordinatesMatrix_complexPair]
    exact (congrArg (fun p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ ↦
      complexPairRealMatrix p.1 p.2) (doubledRealCoordinatePair_reconstruct x)).trans
        (complexPairRealMatrix_doubledParts (doubledRealCoordinatesMatrix x))
  right_inv x := by
    have heq : (doubledHermitianPart (doubledRealCoordinatesMatrix (complexPairRealCoordinates x)),
        doubledSymmetricPart (doubledRealCoordinatesMatrix (complexPairRealCoordinates x))) =
      (hermitianMatrixOfCoordinates x.1, complexSymmetricMatrixOfCoordinates x.2) := by
      rw [doubledRealCoordinatesMatrix_complexPair, doubledParts_complexPairRealMatrix]
    change (hermitianCoordinateProjection (doubledHermitianPart
      (doubledRealCoordinatesMatrix (complexPairRealCoordinates x))),
        A2Research.symmetricCoordinateProjection m (doubledSymmetricPart
          (doubledRealCoordinatesMatrix (complexPairRealCoordinates x)))) = x
    apply Prod.ext
    · have ht := congrArg (fun p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ ↦
          hermitianCoordinateProjection p.1) heq
      simpa only [hermitianCoordinateProjection_ofCoordinates] using ht
    · have hz := congrArg (fun p : Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ ↦
          A2Research.symmetricCoordinateProjection m p.2) heq
      exact hz.trans (A2Research.symmetricCoordinateProjection_embedding m x.2)

end A1Research
