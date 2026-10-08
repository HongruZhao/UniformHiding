import A3.WishartDensityAlgebra
import A3.WishartCholeskyInjective
import A3.Shared.WeylIntegrationSeparatedDensity

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Function
open scoped BigOperators ENNReal NNReal ComplexOrder

noncomputable section
namespace A3Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {K : Type*} [RCLike K] [MeasureSpace K] [BorelSpace K]

def wishartCholeskyJacobianDensity (x : HermitianCoordinates n K) : ℝ≥0∞ :=
  ENNReal.ofReal (∏ i : Fin n, (Real.sqrt (x.1 i)) ^
    (Module.finrank ℝ K * (n - 1 - i.val)))

theorem measurable_wishartCholeskyJacobianDensity :
    Measurable (wishartCholeskyJacobianDensity : HermitianCoordinates n K → ℝ≥0∞) := by
  unfold wishartCholeskyJacobianDensity
  fun_prop

theorem wishartCholeskyJacobianDensity_eq (x : HermitianCoordinates n K)
    (hx : x ∈ wishartCholeskyDomain n K) :
    wishartCholeskyJacobianDensity x = ENNReal.ofReal |(fderiv ℝ wishartGramCoordinates x).det| := by
  rw [abs_of_pos (det_fderiv_wishartGramCoordinates_pos x hx),
    det_fderiv_wishartGramCoordinates x hx]
  rfl

/-- Actual Euclidean area formula for the full positive-pivot Cholesky chart. -/
theorem wishartCholesky_area [PolishSpace K] [IsAddHaarMeasure (volume : Measure K)] :
    Measure.map (wishartGramCoordinates : HermitianCoordinates n K → _)
      (((hermitianCoordinateVolume n K).restrict (wishartCholeskyDomain n K)).withDensity
        wishartCholeskyJacobianDensity) =
      (hermitianCoordinateVolume n K).restrict (wishartPositiveDefiniteDomain n K) := by
  let mu := hermitianCoordinateVolume n K
  letI : IsAddHaarMeasure mu := by
    dsimp [mu, hermitianCoordinateVolume]
    exact prod.instIsAddHaarMeasure _ _
  have hs : MeasurableSet (wishartCholeskyDomain n K) :=
    isOpen_wishartCholeskyDomain.measurableSet
  have hder (x : HermitianCoordinates n K) (hx : x ∈ wishartCholeskyDomain n K) :
      HasFDerivWithinAt wishartGramCoordinates (fderiv ℝ wishartGramCoordinates x)
        (wishartCholeskyDomain n K) x :=
    (contDiffAt_wishartGramCoordinates 1 x hx).differentiableAt_one.hasFDerivAt.hasFDerivWithinAt
  have harea := map_withDensity_abs_det_fderiv_eq_addHaar mu hs.nullMeasurableSet hder
    wishartGramCoordinates_injOn
  have hdensity : (mu.restrict (wishartCholeskyDomain n K)).withDensity
      wishartCholeskyJacobianDensity =
      (mu.restrict (wishartCholeskyDomain n K)).withDensity
        (fun x ↦ ENNReal.ofReal |(fderiv ℝ wishartGramCoordinates x).det|) := by
    apply withDensity_congr_ae
    exact (ae_restrict_mem hs).mono fun x hx ↦ wishartCholeskyJacobianDensity_eq x hx
  rw [hdensity]
  simpa only [wishartGramCoordinates_bijOn.image_eq] using harea

theorem wishartAmbientDensity_restrict :
    ((hermitianCoordinateVolume n K).restrict (wishartPositiveDefiniteDomain n K)).withDensity
      (wishartAmbientDensity n K alpha) = wishartAmbientMeasure n K alpha := by
  rw [← withDensity_indicator (measurableSet_wishartPositiveDefiniteDomain (n := n) (K := K))]
  congr 1
  funext x
  by_cases hx : x ∈ wishartPositiveDefiniteDomain n K
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx]
    simp only [wishartAmbientDensity, wishartPositiveDefiniteDomain, mem_setOf_eq] at hx ⊢
    rw [if_neg hx]

/-- The actual independent Gamma/Gaussian Bartlett law pushes to the explicit
ambient Hermitian Wishart density. All chart and Jacobian premises are proved. -/
theorem wishartBartlettGram_eq_ambientDensity
    [PolishSpace K] [IsAddHaarMeasure (volume : Measure K)] [SigmaFinite (volume : Measure K)]
    (alpha c : ℝ) (hc : 0 < c)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha K i)
    (gaussianField : Measure K) [IsProbabilityMeasure gaussianField]
    (hgauss : gaussianField = (volume : Measure K).withDensity
      (fun z ↦ ENNReal.ofReal (c * Real.exp (-RCLike.normSq z)))) :
    Measure.map wishartGramCoordinates (wishartBartlettMeasure n alpha gaussianField) =
      ENNReal.ofReal (wishartBartlettNormalization n K alpha c) • wishartAmbientMeasure n K alpha := by
  let mu := hermitianCoordinateVolume n K
  let s := wishartCholeskyDomain n K
  let j : HermitianCoordinates n K → ℝ≥0∞ := wishartCholeskyJacobianDensity
  let h : HermitianCoordinates n K → ℝ≥0∞ := wishartAmbientDensity n K alpha
  let C := ENNReal.ofReal (wishartBartlettNormalization n K alpha c)
  have hg : Measurable (fun z : K ↦ ENNReal.ofReal (c * Real.exp (-RCLike.normSq z))) := by
    exact (measurable_const.mul (RCLike.continuous_normSq.measurable.neg.exp)).ennreal_ofReal
  have hs : MeasurableSet s := isOpen_wishartCholeskyDomain.measurableSet
  have hj : Measurable j := measurable_wishartCholeskyJacobianDensity
  have hh : Measurable h := measurable_wishartAmbientDensity alpha
  have hphi : Measurable (wishartGramCoordinates : HermitianCoordinates n K → _) :=
    continuous_wishartGramCoordinates.measurable
  have hpull : Measurable (h ∘ wishartGramCoordinates) := hh.comp hphi
  have hsrc : wishartBartlettMeasure n alpha gaussianField =
      (mu.restrict s).withDensity (wishartBartlettDensity n alpha
        (fun z ↦ ENNReal.ofReal (c * Real.exp (-RCLike.normSq z)))) := by
    rw [← restrict_eq_self_of_ae_mem (wishartBartlettMeasure_ae_domain gaussianField ha),
      wishartBartlettMeasure_eq_withDensity gaussianField _ hg hgauss ha,
      restrict_withDensity hs]
  have heq : (mu.restrict s).withDensity (wishartBartlettDensity n alpha
      (fun z ↦ ENNReal.ofReal (c * Real.exp (-RCLike.normSq z)))) =
      (mu.restrict s).withDensity (C • (j * (h ∘ wishartGramCoordinates))) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [wishartBartlettDensity_identity alpha c hc ha x hx]
    dsimp [C, j, h]
    rw [wishartCholeskyJacobianDensity_eq x hx]
    rw [mul_comm (wishartAmbientDensity n K alpha (wishartGramCoordinates x))]
  rw [hsrc, heq, withDensity_smul C (hj.mul hpull), withDensity_mul _ hj hpull,
    Measure.map_smul, map_withDensity_comp _ _ hphi _ hh, wishartCholesky_area,
    wishartAmbientDensity_restrict]

theorem wishartRealBartlettGram_eq_ambientDensity (alpha : ℝ)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℝ i) :
    Measure.map wishartGramCoordinates (wishartRealBartlettMeasure n alpha) =
      ENNReal.ofReal (wishartBartlettNormalization n ℝ alpha (Real.sqrt Real.pi)⁻¹) •
        wishartAmbientMeasure n ℝ alpha := by
  apply wishartBartlettGram_eq_ambientDensity alpha (Real.sqrt Real.pi)⁻¹
    (inv_pos.mpr (Real.sqrt_pos.mpr Real.pi_pos)) ha
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 / 2 : ℝ≥0) ≠ 0)]
  congr 1
  funext x
  simp only [gaussianPDF_def, gaussianHalf_pdf_real, RCLike.normSq_eq_def', Real.norm_eq_abs,
    sq_abs]

theorem wishartComplexBartlettGram_eq_ambientDensity (alpha : ℝ)
    (ha : ∀ i : Fin n, 0 < wishartBartlettShape alpha ℂ i) :
    Measure.map wishartGramCoordinates (wishartComplexBartlettMeasure n alpha) =
      ENNReal.ofReal (wishartBartlettNormalization n ℂ alpha Real.pi⁻¹) •
        wishartAmbientMeasure n ℂ alpha := by
  letI := circularGaussian_isProbabilityMeasure
  apply wishartBartlettGram_eq_ambientDensity alpha Real.pi⁻¹ (inv_pos.mpr Real.pi_pos) ha
  rw [circularGaussian_eq_withDensity]
  congr 1
  funext z
  rw [complexHalfGaussianDensity_eq_kernel]
  rfl

end A3Research
