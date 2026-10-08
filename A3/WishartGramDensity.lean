import A3.WishartAmbientMass
import A3.ComplexBartlettLaplace
import A3.RealGaussianBartlettLaw

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable section
namespace A3Research

/-- The literal real rectangular standard Gaussian Gram, divided by two,
has the explicit ambient real Wishart density. -/
theorem realGaussianGramCoordinateLaw_eq_ambientDensity {rows n : ℕ} (hn : n ≤ rows) :
    realGaussianGramCoordinateLaw rows n =
      ENNReal.ofReal (wishartBartlettNormalization n ℝ ((rows : ℝ) / 2)
        (Real.sqrt Real.pi)⁻¹) • wishartAmbientMeasure n ℝ ((rows : ℝ) / 2) := by
  rw [realGaussianGramCoordinateLaw_eq_bartlett hn]
  exact wishartRealBartlettGram_eq_ambientDensity _ (wishartBartlettShape_real_rows_pos hn)

/-- The literal circular complex rectangular Gaussian Gram has the explicit
ambient complex Wishart density. -/
theorem complexGaussianGramCoordinateLaw_eq_ambientDensity {rows n : ℕ} (hn : n ≤ rows) :
    complexGaussianGramCoordinateLaw rows n =
      ENNReal.ofReal (wishartBartlettNormalization n ℂ (rows : ℝ) Real.pi⁻¹) •
        wishartAmbientMeasure n ℂ (rows : ℝ) := by
  rw [complexGaussianGramCoordinateLaw_eq_bartlett hn]
  exact wishartComplexBartlettGram_eq_ambientDensity _ (wishartBartlettShape_complex_rows_pos hn)

theorem wishartAmbientMeasure_real_mass_pos (alpha : ℝ)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℝ i) :
    0 < wishartAmbientMeasure n ℝ alpha univ := by
  rw [wishartAmbientMeasure_real_mass alpha ha]
  exact ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top

theorem wishartAmbientMeasure_complex_mass_pos (alpha : ℝ)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℂ i) :
    0 < wishartAmbientMeasure n ℂ alpha univ := by
  rw [wishartAmbientMeasure_complex_mass alpha ha]
  exact ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top

end A3Research
