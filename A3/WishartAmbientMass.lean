import A3.WishartAmbientDensity

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace A3Research

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K : Type*} [RCLike K] [MeasureSpace K] [BorelSpace K]

theorem wishartAmbientMeasure_mass_of_bartlett
    [PolishSpace K] [IsAddHaarMeasure (volume : Measure K)] [SigmaFinite (volume : Measure K)]
    (alpha c : ℝ) (hc : 0 < c)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha K i)
    (gaussianField : Measure K) [IsProbabilityMeasure gaussianField]
    (hgauss : gaussianField = (volume : Measure K).withDensity
      (fun z ↦ ENNReal.ofReal (c * Real.exp (-RCLike.normSq z)))) :
    wishartAmbientMeasure n K alpha univ =
      (ENNReal.ofReal (wishartBartlettNormalization n K alpha c))⁻¹ := by
  letI := wishartBartlettMeasure_probability gaussianField ha
  have hp := congrArg (fun mu : Measure (HermitianCoordinates n K) ↦ mu univ)
    (wishartBartlettGram_eq_ambientDensity alpha c hc ha gaussianField hgauss)
  rw [Measure.map_apply continuous_wishartGramCoordinates.measurable MeasurableSet.univ,
    preimage_univ, measure_univ, Measure.smul_apply, smul_eq_mul] at hp
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa only [mul_comm] using hp.symm)

theorem wishartAmbientMeasure_real_mass (alpha : ℝ)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℝ i) :
    wishartAmbientMeasure n ℝ alpha univ =
      (ENNReal.ofReal (wishartBartlettNormalization n ℝ alpha (Real.sqrt Real.pi)⁻¹))⁻¹ := by
  apply wishartAmbientMeasure_mass_of_bartlett alpha (Real.sqrt Real.pi)⁻¹
    (inv_pos.mpr (Real.sqrt_pos.mpr Real.pi_pos)) ha (gaussianReal 0 (1 / 2))
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)]
  congr 1
  funext x
  simp only [gaussianPDF_def, gaussianHalf_pdf_real, RCLike.normSq_eq_def', Real.norm_eq_abs,
    sq_abs]

theorem wishartAmbientMeasure_complex_mass (alpha : ℝ)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℂ i) :
    wishartAmbientMeasure n ℂ alpha univ =
      (ENNReal.ofReal (wishartBartlettNormalization n ℂ alpha Real.pi⁻¹))⁻¹ := by
  letI := circularGaussian_isProbabilityMeasure
  apply wishartAmbientMeasure_mass_of_bartlett alpha Real.pi⁻¹ (inv_pos.mpr Real.pi_pos) ha
    LogdetLean.GramHafnian.circularGaussian
  rw [circularGaussian_eq_withDensity]
  congr 1
  funext z
  rw [complexHalfGaussianDensity_eq_kernel]
  rfl

theorem wishartAmbientMeasure_real_isFinite (alpha : ℝ)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℝ i) :
    IsFiniteMeasure (wishartAmbientMeasure n ℝ alpha) := by
  constructor
  rw [wishartAmbientMeasure_real_mass alpha ha]
  exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr
    (wishartBartlettNormalization_pos alpha (Real.sqrt Real.pi)⁻¹
      (inv_pos.mpr (Real.sqrt_pos.mpr Real.pi_pos)) ha))

theorem wishartAmbientMeasure_complex_isFinite (alpha : ℝ)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℂ i) :
    IsFiniteMeasure (wishartAmbientMeasure n ℂ alpha) := by
  constructor
  rw [wishartAmbientMeasure_complex_mass alpha ha]
  exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr
    (wishartBartlettNormalization_pos alpha Real.pi⁻¹ (inv_pos.mpr Real.pi_pos) ha))

end A3Research
