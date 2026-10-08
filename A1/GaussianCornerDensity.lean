import A1.GaussianOverlapStatistic
import A1.DoubledDensityCoordinateChange
import A1.DoubledWishartFiberIntegration

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
open A3Research
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace A1Research

def gaussianCornerDensityConstant (n m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (wishartBartlettNormalization (2 * m) ℝ ((n : ℝ) / 2)
      (Real.sqrt Real.pi)⁻¹) *
    (doubledCoordinateVolumeConstant m : ℝ≥0∞) * doubledWishartMarginalConstant n m

/-- Full density of the literal normalized transpose Gram in every independent complex entry. -/
theorem normalizedTransposeGramCoordinates_density {n m : ℕ} (h2mn : 2 * m ≤ n) :
    (standardComplexGaussianRectangularMeasure n m).map normalizedTransposeGramCoordinates =
      gaussianCornerDensityConstant n m •
        (complexSymmetricCoordinateVolume m).withDensity (FriedmanMelloA1.determinantWeight n m) := by
  have hmap : (normalizedTransposeGramCoordinates : Matrix (Fin n) (Fin m) ℂ → _) =
      normalizedComplexPairCoordinates ∘ gaussianGramPairCoordinates := by
    funext G
    exact (normalizedComplexPairCoordinates_gaussianGramPair G).symm
  rw [hmap, ← Measure.map_map (measurable_normalizedComplexPairCoordinates m)
    (measurable_gaussianGramPairCoordinates n m),
    map_gaussianGramPairCoordinates_eq_doubledWishart h2mn,
    Measure.map_smul, map_doubledWishart_to_pair_density, Measure.map_smul,
    Measure.map_smul, map_normalizedComplexPair_doubledDensity, smul_smul, smul_smul]
  rfl

end A1Research
