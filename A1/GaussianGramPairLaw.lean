import A1.DoubledGaussianGramParts

open Matrix A3Research MeasureTheory
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators

noncomputable section
namespace A1Research

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def gaussianGramPairCoordinates {n m : ℕ} (G : Matrix (Fin n) (Fin m) ℂ) :
    HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m :=
  (hermitianCoordinateProjection (G.conjTranspose * G),
    A2Research.symmetricCoordinateProjection m (G.transpose * G))

theorem gaussianGramPairCoordinates_eq_doubledMap {n m : ℕ}
    (G : Matrix (Fin n) (Fin m) ℂ) :
    gaussianGramPairCoordinates G =
      doubledRealCoordinatePairLinearEquiv m (doubledRealGramCoordinates G) :=
  (doubledRealCoordinatePair_Gram G).symm

theorem measurable_gaussianGramPairCoordinates (n m : ℕ) :
    Measurable (gaussianGramPairCoordinates : Matrix (Fin n) (Fin m) ℂ → _) := by
  have hmap : gaussianGramPairCoordinates =
      (doubledRealCoordinatePairLinearEquiv m) ∘
        (doubledRealGramCoordinates : Matrix (Fin n) (Fin m) ℂ → _) := by
    funext G
    exact gaussianGramPairCoordinates_eq_doubledMap G
  rw [hmap]
  exact (doubledRealCoordinatePairLinearEquiv m).continuous_of_finiteDimensional.measurable.comp
    (measurable_doubledRealGramCoordinates n m)

theorem map_gaussianGramPairCoordinates_eq_doubledWishart {n m : ℕ}
    (h2mn : 2 * m ≤ n) :
    (standardComplexGaussianRectangularMeasure n m).map gaussianGramPairCoordinates =
      (ENNReal.ofReal (wishartBartlettNormalization (2 * m) ℝ ((n : ℝ) / 2)
        (Real.sqrt Real.pi)⁻¹) • wishartAmbientMeasure (2 * m) ℝ ((n : ℝ) / 2)).map
        (doubledRealCoordinatePairLinearEquiv m) := by
  have hmap : gaussianGramPairCoordinates =
      (doubledRealCoordinatePairLinearEquiv m) ∘
        (doubledRealGramCoordinates : Matrix (Fin n) (Fin m) ℂ → _) := by
    funext G
    exact gaussianGramPairCoordinates_eq_doubledMap G
  have he : Measurable (doubledRealCoordinatePairLinearEquiv m) :=
    (doubledRealCoordinatePairLinearEquiv m).continuous_of_finiteDimensional.measurable
  rw [hmap, ← Measure.map_map he
    (measurable_doubledRealGramCoordinates n m),
    map_doubledRealGramCoordinates_eq_ambientDensity h2mn]

end A1Research
