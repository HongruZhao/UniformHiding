import A3.BetaMatrixFiberIntegration

open scoped BigOperators Matrix.Norms.Elementwise ComplexOrder MatrixOrder ENNReal
open Matrix MeasureTheory Set
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]
  [MeasureSpace K] [BorelSpace K] [PolishSpace K]
  [(hermitianCoordinateVolume n K).IsAddHaarMeasure]

instance wishartAmbientMeasure_sigmaFinite (α : ℝ) :
    SigmaFinite (wishartAmbientMeasure n K α) := by
  unfold wishartAmbientMeasure
  exact SigmaFinite.withDensity_of_ne_top' (wishartAmbientDensity_ne_top α)

/-- The shear of two actual Hermitian coordinates preserves their product volume. -/
theorem measurePreserving_hermitianSumFiber :
    MeasurePreserving (fun p : HermitianCoordinates n K × HermitianCoordinates n K ↦
      (p.2, p.1 - p.2))
      ((hermitianCoordinateVolume n K).prod (hermitianCoordinateVolume n K))
      ((hermitianCoordinateVolume n K).prod (hermitianCoordinateVolume n K)) := by
  exact Measure.measurePreserving_swap.comp
    (measurePreserving_sub_prod (hermitianCoordinateVolume n K)
      (hermitianCoordinateVolume n K))

/-- Fubini and the proved fiber substitution give the full unnormalized matrix-beta law. -/
theorem wishartJacobi_pair_lintegral
    (hn : 1 ≤ n) (α δ : ℝ)
    (hstat : Measurable (betaMatrixJacobiCoordinates :
      HermitianCoordinates n K × HermitianCoordinates n K → _))
    (g : HermitianCoordinates n K → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p, (wishartAmbientDensity n K α p.1 * wishartAmbientDensity n K δ p.2) *
      g (betaMatrixJacobiCoordinates p)
        ∂((hermitianCoordinateVolume n K).prod (hermitianCoordinateVolume n K)) =
      (∫⁻ S, wishartAmbientDensity n K (α + δ) S ∂(hermitianCoordinateVolume n K)) *
        ∫⁻ x, betaMatrixDensity n K α δ x * g x ∂(hermitianCoordinateVolume n K) := by
  let f : HermitianCoordinates n K × HermitianCoordinates n K → ℝ≥0∞ := fun p ↦
    (wishartAmbientDensity n K α p.1 * wishartAmbientDensity n K δ p.2) *
      g (betaMatrixJacobiCoordinates p)
  have hf : Measurable f :=
    ((measurable_wishartAmbientDensity α).comp measurable_fst).mul
      ((measurable_wishartAmbientDensity δ).comp measurable_snd) |>.mul (hg.comp hstat)
  have hcompose : Measurable (fun p : HermitianCoordinates n K × HermitianCoordinates n K ↦
      f (p.2, p.1 - p.2)) :=
    hf.comp measurePreserving_hermitianSumFiber.measurable
  calc
    _ = ∫⁻ p : HermitianCoordinates n K × HermitianCoordinates n K,
        f (p.2, p.1 - p.2)
          ∂((hermitianCoordinateVolume n K).prod (hermitianCoordinateVolume n K)) :=
      (measurePreserving_hermitianSumFiber.lintegral_comp hf).symm
    _ = ∫⁻ S, ∫⁻ A, f (A, S - A) ∂(hermitianCoordinateVolume n K)
        ∂(hermitianCoordinateVolume n K) := lintegral_prod _ hcompose.aemeasurable
    _ = ∫⁻ S, wishartAmbientDensity n K (α + δ) S *
        (∫⁻ x, betaMatrixDensity n K α δ x * g x ∂(hermitianCoordinateVolume n K))
          ∂(hermitianCoordinateVolume n K) := by
      apply lintegral_congr
      intro S
      exact wishartJacobi_fiber_lintegral hn α δ g S
    _ = _ := lintegral_mul_const _ (measurable_wishartAmbientDensity (α + δ))

/-- Full measure equality before normalization; the total Wishart mass is explicit. -/
theorem map_wishartAmbientPair_jacobi
    (hn : 1 ≤ n) (α δ : ℝ)
    (hstat : Measurable (betaMatrixJacobiCoordinates :
      HermitianCoordinates n K × HermitianCoordinates n K → _)) :
    Measure.map betaMatrixJacobiCoordinates
        ((wishartAmbientMeasure n K α).prod (wishartAmbientMeasure n K δ)) =
      (wishartAmbientMeasure n K (α + δ) Set.univ) • betaMatrixRawMeasure n K α δ := by
  apply Measure.ext_of_lintegral _
  intro g hg
  rw [lintegral_map hg hstat, lintegral_smul_measure]
  have hd : Measurable (fun p : HermitianCoordinates n K × HermitianCoordinates n K ↦
      wishartAmbientDensity n K α p.1 * wishartAmbientDensity n K δ p.2) :=
    ((measurable_wishartAmbientDensity α).comp measurable_fst).mul
      ((measurable_wishartAmbientDensity δ).comp measurable_snd)
  have htest : Measurable (fun p : HermitianCoordinates n K × HermitianCoordinates n K ↦
      g (betaMatrixJacobiCoordinates p)) := hg.comp hstat
  unfold wishartAmbientMeasure betaMatrixRawMeasure
  rw [prod_withDensity (measurable_wishartAmbientDensity α)
      (measurable_wishartAmbientDensity δ),
    lintegral_withDensity_eq_lintegral_mul _ hd htest,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_betaMatrixDensity α δ) hg,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact wishartJacobi_pair_lintegral hn α δ hstat g hg

/-- Exact matrix-beta law for normalized independent Wishart densities. The
normalizing scalar is inferred from actual probability mass, not imported. -/
theorem map_normalizedWishartPair_jacobi
    (hn : 1 ≤ n) (α δ : ℝ)
    (hstat : Measurable (betaMatrixJacobiCoordinates :
      HermitianCoordinates n K × HermitianCoordinates n K → _))
    (cα cδ : ℝ≥0∞)
    [IsProbabilityMeasure (cα • wishartAmbientMeasure n K α)]
    [IsProbabilityMeasure (cδ • wishartAmbientMeasure n K δ)] :
    Measure.map betaMatrixJacobiCoordinates
        ((cα • wishartAmbientMeasure n K α).prod (cδ • wishartAmbientMeasure n K δ)) =
      (betaMatrixRawMeasure n K α δ Set.univ)⁻¹ • betaMatrixRawMeasure n K α δ := by
  have hprod : IsProbabilityMeasure
      ((cα • wishartAmbientMeasure n K α).prod (cδ • wishartAmbientMeasure n K δ)) := inferInstance
  let c : ℝ≥0∞ := cα * cδ * wishartAmbientMeasure n K (α + δ) Set.univ
  have hraw : Measure.map betaMatrixJacobiCoordinates
      ((cα • wishartAmbientMeasure n K α).prod (cδ • wishartAmbientMeasure n K δ)) =
        c • betaMatrixRawMeasure n K α δ := by
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.map_smul, map_wishartAmbientPair_jacobi hn α δ hstat, smul_smul]
  have hmass : c * betaMatrixRawMeasure n K α δ Set.univ = 1 := by
    have hprob : IsProbabilityMeasure (Measure.map betaMatrixJacobiCoordinates
      ((cα • wishartAmbientMeasure n K α).prod (cδ • wishartAmbientMeasure n K δ))) :=
      Measure.isProbabilityMeasure_map hstat.aemeasurable
    simpa only [hraw, Measure.smul_apply, smul_eq_mul] using
      (measure_univ (μ := Measure.map betaMatrixJacobiCoordinates
        ((cα • wishartAmbientMeasure n K α).prod (cδ • wishartAmbientMeasure n K δ))))
  have hZ0 : betaMatrixRawMeasure n K α δ Set.univ ≠ 0 := by
    intro h
    rw [h, mul_zero] at hmass
    exact zero_ne_one hmass
  have hZtop : betaMatrixRawMeasure n K α δ Set.univ ≠ ∞ := by
    intro h
    by_cases hc : c = 0
    · rw [hc, zero_mul] at hmass
      exact zero_ne_one hmass
    · rw [h, ENNReal.mul_top hc] at hmass
      exact ENNReal.top_ne_one hmass
  have hc : c = (betaMatrixRawMeasure n K α δ Set.univ)⁻¹ := by
    calc
      c = c * betaMatrixRawMeasure n K α δ Set.univ *
          (betaMatrixRawMeasure n K α δ Set.univ)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hZ0 hZtop, mul_one]
      _ = _ := by rw [hmass, one_mul]
  rw [hraw, hc]

end A3Research
