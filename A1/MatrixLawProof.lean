import A1.GaussianCornerDensity
import A1.DensityNormalization

open MeasureTheory
open LogdetLean.GramHafnian.LocalAnticoncentration

noncomputable section
namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1

/-- Friedman--Mello's complete symmetric corner-matrix law on the original Haar carrier,
including the threshold `n=2m`, with the literal density and its own mass normalization. -/
theorem A1_friedmanMello_matrixLaw : Target := by
  intro n m hm h2mn
  change (unitaryHaarProbabilityMeasure n).map
    (fun U ↦ s (dimensionLe h2mn) (S U)) = determinantDensityProbabilityMeasure n m
  rw [← A1Research.normalizedTransposeGramLaw_eq_haar_coeCorner (dimensionLe h2mn)]
  exact A1Research.normalizedTransposeGramLaw_of_coordinate_density
    (A1Research.gaussianCornerDensityConstant n m)
    (A1Research.normalizedTransposeGramCoordinates_density h2mn)

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1
