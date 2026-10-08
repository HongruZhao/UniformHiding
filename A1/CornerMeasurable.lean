import A1.HaarBridgeCorner
import A2.UnitaryCongruenceAlgebra
import A3.WishartAmbientKernel

open Matrix MeasureTheory
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators MatrixOrder ComplexOrder ENNReal

noncomputable section
namespace A1Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem continuous_symmetricCoordinateReconstruction (m : ℕ) :
    Continuous (complexSymmetricMatrixOfCoordinates (N := m)) :=
  (A2Research.symmetricCoordinateEmbedding m).continuous_of_finiteDimensional

theorem measurable_symmetricCoordinateProjection (m : ℕ) :
    Measurable (A2Research.symmetricCoordinateProjection m) :=
  (A2Research.symmetricCoordinateProjection m).continuous_of_finiteDimensional.measurable

theorem symmetricBallComplement_isHermitian {m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℂ) : (1 - C.conjTranspose * C).IsHermitian :=
  Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self C)

/-- Measurability of the literal positive-definite support in the original A1 density. -/
theorem measurableSet_determinantWeight_support (m : ℕ) :
    MeasurableSet {x : ComplexSymmetricCoordinates m |
      FriedmanMelloA1.support (complexSymmetricMatrixOfCoordinates x)} := by
  let f : ComplexSymmetricCoordinates m → A3Research.HermitianCoordinates m ℂ :=
    fun x ↦ A3Research.hermitianCoordinateProjection
      (1 - (complexSymmetricMatrixOfCoordinates x).conjTranspose *
        complexSymmetricMatrixOfCoordinates x)
  have hf : Measurable f := by
    apply (A3Research.measurable_hermitianCoordinateProjection m ℂ).comp
    have hc := continuous_symmetricCoordinateReconstruction m
    exact (continuous_const.sub (hc.matrix_conjTranspose.matrix_mul hc)).measurable
  have heq : {x : ComplexSymmetricCoordinates m |
      FriedmanMelloA1.support (complexSymmetricMatrixOfCoordinates x)} =
      f ⁻¹' A3Research.wishartPositiveDefiniteDomain m ℂ := by
    ext x
    change (1 - (complexSymmetricMatrixOfCoordinates x).conjTranspose *
      complexSymmetricMatrixOfCoordinates x).PosDef ↔
      (A3Research.hermitianMatrixOfCoordinates (f x)).PosDef
    dsimp only [f]
    rw [A3Research.hermitianMatrixOfCoordinates_projection _
      (symmetricBallComplement_isHermitian _)]
  rw [heq]
  exact (A3Research.measurableSet_wishartPositiveDefiniteDomain
    (n := m) (K := ℂ)).preimage hf

theorem measurable_determinantWeight (n m : ℕ) :
    Measurable (FriedmanMelloA1.determinantWeight n m) := by
  unfold FriedmanMelloA1.determinantWeight
  apply Measurable.ite (measurableSet_determinantWeight_support m) _ measurable_const
  change Measurable (fun x : ComplexSymmetricCoordinates m ↦ ENNReal.ofReal
    ((1 - (complexSymmetricMatrixOfCoordinates x).conjTranspose *
      complexSymmetricMatrixOfCoordinates x).det.re ^ FriedmanMelloA1.densityExponent n m))
  have hc := continuous_symmetricCoordinateReconstruction m
  have hcomp : Continuous (fun x : ComplexSymmetricCoordinates m ↦
      (1 : Matrix (Fin m) (Fin m) ℂ) -
        (complexSymmetricMatrixOfCoordinates x).conjTranspose *
          complexSymmetricMatrixOfCoordinates x) :=
    continuous_const.sub (hc.matrix_conjTranspose.matrix_mul hc)
  have hd : Measurable (fun x : ComplexSymmetricCoordinates m ↦
      (1 - (complexSymmetricMatrixOfCoordinates x).conjTranspose *
        complexSymmetricMatrixOfCoordinates x).det.re) :=
    Complex.continuous_re.measurable.comp hcomp.matrix_det.measurable
  exact (hd.pow_const (FriedmanMelloA1.densityExponent n m)).ennreal_ofReal

theorem rawDeterminantDensityMeasure_eq_coordinate_map (n m : ℕ) :
    FriedmanMelloA1.rawDeterminantDensityMeasure n m =
      ((complexSymmetricCoordinateVolume m).withDensity
        (FriedmanMelloA1.determinantWeight n m)).map
        complexSymmetricMatrixOfCoordinates := rfl

/-- Symmetry holds for every Gaussian input, including singular Gram samples. -/
theorem normalizedTransposeGram_isSymm {n m : ℕ}
    (G : Matrix (Fin n) (Fin m) ℂ) : (normalizedTransposeGram G).IsSymm := by
  unfold normalizedTransposeGram normalizedComplexPairOverlap Matrix.IsSymm
  simp only [Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    Matrix.transpose_transpose, Matrix.mul_assoc]

def normalizedTransposeGramCoordinates {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℂ) :
    ComplexSymmetricCoordinates m :=
  A2Research.symmetricCoordinateProjection m (normalizedTransposeGram G)

theorem measurable_normalizedTransposeGramCoordinates (n m : ℕ) :
    Measurable (normalizedTransposeGramCoordinates : Matrix (Fin n) (Fin m) ℂ →
      ComplexSymmetricCoordinates m) :=
  (measurable_symmetricCoordinateProjection m).comp (measurable_normalizedTransposeGram n m)

theorem normalizedTransposeGramCoordinates_reconstruct {n m : ℕ}
    (G : Matrix (Fin n) (Fin m) ℂ) :
    complexSymmetricMatrixOfCoordinates (normalizedTransposeGramCoordinates G) =
      normalizedTransposeGram G :=
  A2Research.symmetricCoordinateEmbedding_projection _ (normalizedTransposeGram_isSymm G)

/-- Projecting the normalized overlap to independent coordinates and reconstructing
preserves its literal full matrix law for any source measure. -/
theorem map_reconstruct_normalizedTransposeGramCoordinates {n m : ℕ}
    (mu : Measure (Matrix (Fin n) (Fin m) ℂ)) :
    (mu.map normalizedTransposeGramCoordinates).map complexSymmetricMatrixOfCoordinates =
      mu.map normalizedTransposeGram := by
  rw [Measure.map_map (measurable_complexSymmetricMatrixOfCoordinates m)
    (measurable_normalizedTransposeGramCoordinates n m)]
  congr 1
  funext G
  exact normalizedTransposeGramCoordinates_reconstruct G

theorem normalizedTransposeGramCoordinates_haar_reconstruction {n m : ℕ} (hmn : m ≤ n) :
    ((standardComplexGaussianRectangularMeasure n m).map
      normalizedTransposeGramCoordinates).map complexSymmetricMatrixOfCoordinates =
      (unitaryHaarProbabilityMeasure n).map (fun U ↦
        FriedmanMelloA1.s hmn (FriedmanMelloA1.S U)) := by
  rw [map_reconstruct_normalizedTransposeGramCoordinates,
    normalizedTransposeGramLaw_eq_haar_coeCorner hmn]

end A1Research
