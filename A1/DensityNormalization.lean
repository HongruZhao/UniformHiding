import A1.CornerMeasurable

open MeasureTheory MeasureTheory.Measure Set Matrix
open scoped ENNReal
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace A1Research

/-- A genuine probability proportional to a raw density determines its own normalizer. -/
theorem probability_eq_selfNormalized_of_smul {X : Type*} [MeasurableSpace X]
    (mu raw : Measure X) [IsProbabilityMeasure mu] (c : ℝ≥0∞)
    (h : mu = c • raw) : mu = (raw univ)⁻¹ • raw := by
  have hmass : c * raw univ = 1 := by
    simpa only [h, Measure.smul_apply, smul_eq_mul] using (measure_univ (μ := mu))
  have hZ0 : raw univ ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hmass
    exact zero_ne_one hmass
  have hZtop : raw univ ≠ ∞ := by
    intro hz
    by_cases hc : c = 0
    · rw [hc, zero_mul] at hmass
      exact zero_ne_one hmass
    · rw [hz, ENNReal.mul_top hc] at hmass
      exact ENNReal.top_ne_one hmass
  have hc : c = (raw univ)⁻¹ := by
    calc
      c = c * raw univ * (raw univ)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hZ0 hZtop, mul_one]
      _ = _ := by rw [hmass, one_mul]
  rw [h, hc]

/-- Exact full-matrix self-normalization after the independent-coordinate density calculation. -/
theorem normalizedTransposeGramLaw_of_coordinate_density {n m : ℕ} (c : ℝ≥0∞)
    (h : (standardComplexGaussianRectangularMeasure n m).map
        normalizedTransposeGramCoordinates =
      c • (complexSymmetricCoordinateVolume m).withDensity
        (FriedmanMelloA1.determinantWeight n m)) :
    (standardComplexGaussianRectangularMeasure n m).map normalizedTransposeGram =
      FriedmanMelloA1.determinantDensityProbabilityMeasure n m := by
  let mu := (standardComplexGaussianRectangularMeasure n m).map normalizedTransposeGram
  letI : IsProbabilityMeasure mu :=
    Measure.isProbabilityMeasure_map (measurable_normalizedTransposeGram n m).aemeasurable
  have hraw : mu = c • FriedmanMelloA1.rawDeterminantDensityMeasure n m := by
    dsimp only [mu]
    rw [← map_reconstruct_normalizedTransposeGramCoordinates, h,
      Measure.map_smul]
    rfl
  exact probability_eq_selfNormalized_of_smul mu _ c hraw

end A1Research
