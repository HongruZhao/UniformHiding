import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.WickAngularLowerBound.MomentReduction

/-!
# First absolute moments in the circular Gaussian polar decomposition

This file develops the one-column analytic input needed by the Wick angular
estimate.  It contains only literal circular-Gaussian and spherical laws.
-/

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal Real BigOperators

namespace LogdetLean.GramHafnian

noncomputable section

namespace WickAngularLowerBound

/-- The exact first moment of the positive radius in complex dimension `k`. -/
theorem integral_positiveRadius_eq_gammaRatio
    {k : ℕ} (hk : 0 < k) :
    (∫ r : Ioi (0 : ℝ), (r.1 : ℝ)
        ∂circularGaussianPositiveRadiusMeasure k) =
      Real.Gamma ((k : ℝ) + 1 / 2) / Real.Gamma (k : ℝ) := by
  have hpush :
      (∫ r : Ioi (0 : ℝ), (r.1 : ℝ)
          ∂circularGaussianPositiveRadiusMeasure k) =
        ∫ q : ℝ, Real.sqrt q ∂circularGaussianSquaredRadiusMeasure k := by
    unfold circularGaussianSquaredRadiusMeasure
    rw [integral_map
      (μ := circularGaussianPositiveRadiusMeasure k)
      (φ := fun r : Ioi (0 : ℝ) ↦ r.1 ^ 2)
      (f := Real.sqrt) (by fun_prop) (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with r
    rw [Real.sqrt_sq_eq_abs, abs_of_pos r.2]
  rw [hpush, circularGaussianSquaredRadiusMeasure_eq_halfGamma hk,
    integral_map (by fun_prop) (by fun_prop)]
  have hmellin := LogdetLean.integral_rpow_gammaMeasure
    (a := (k : ℝ)) (r := (1 / 2 : ℝ)) (t := (1 / 2 : ℝ))
    (show (0 : ℝ) < k by exact_mod_cast hk) (by norm_num) (by positivity)
  simp_rw [Real.sqrt_eq_rpow]
  have hu_nonneg : ∀ᵐ u ∂gammaMeasure (k : ℝ) (1 / 2), 0 ≤ u := by
    unfold gammaMeasure
    have hmeas : Measurable (gammaPDF (k : ℝ) (1 / 2)) := by
      unfold gammaPDF
      exact (measurable_gammaPDFReal (k : ℝ) (1 / 2)).ennreal_ofReal
    rw [MeasureTheory.ae_withDensity_iff hmeas]
    filter_upwards [] with u
    intro hpdf
    by_contra hu
    have hu' : u < 0 := lt_of_not_ge hu
    apply hpdf
    simp [gammaPDF, gammaPDFReal, not_le.mpr hu']
  rw [integral_congr_ae (hu_nonneg.mono fun u hu ↦ by
    rw [show u / 2 = (1 / 2 : ℝ) * u by ring,
      Real.mul_rpow (by norm_num) hu])]
  rw [integral_const_mul, hmellin]
  have hhalf : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) *
      (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add (by norm_num : 0 < (1 / 2 : ℝ))]
    norm_num
  rw [mul_div_assoc, ← mul_assoc, hhalf, one_mul]

/-- The norm of a literal iid circular Gaussian vector has the same first
moment as its positive polar radius. -/
theorem integral_norm_iidCircularEuclidean_eq_gammaRatio
    {k : ℕ} (hk : 0 < k) :
    (∫ z : CircularEuclideanSpace k, ‖z‖
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)) =
      Real.Gamma ((k : ℝ) + 1 / 2) / Real.Gamma (k : ℝ) := by
  have hvec :
      (∫ z : CircularEuclideanSpace k, ‖z‖
          ∂(Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)) =
        ∫ q : ℝ, Real.sqrt q
          ∂((Measure.pi fun _ : Fin k ↦ circularGaussian).map
            (WithLp.toLp 2)).map circularVectorNormSq := by
    rw [integral_map (measurable_circularVectorNormSq (k := k)).aemeasurable
      (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with z
    simp [circularVectorNormSq, Real.sqrt_sq (norm_nonneg z)]
  have hrad :
      (∫ r : Ioi (0 : ℝ), (r.1 : ℝ)
          ∂circularGaussianPositiveRadiusMeasure k) =
        ∫ q : ℝ, Real.sqrt q ∂circularGaussianSquaredRadiusMeasure k := by
    unfold circularGaussianSquaredRadiusMeasure
    rw [integral_map (by fun_prop) (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with r
    rw [Real.sqrt_sq_eq_abs, abs_of_pos r.2]
  calc
    (∫ z : CircularEuclideanSpace k, ‖z‖
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian).map (WithLp.toLp 2)) =
        ∫ q : ℝ, Real.sqrt q
          ∂((Measure.pi fun _ : Fin k ↦ circularGaussian).map
            (WithLp.toLp 2)).map circularVectorNormSq := hvec
    _ = ∫ q : ℝ, Real.sqrt q ∂circularGaussianSquaredRadiusMeasure k := by
      rw [map_circularVectorNormSq_iid_circular_eq_half_gamma hk,
        circularGaussianSquaredRadiusMeasure_eq_halfGamma hk]
    _ = ∫ r : Ioi (0 : ℝ), (r.1 : ℝ)
          ∂circularGaussianPositiveRadiusMeasure k := hrad.symm
    _ = Real.Gamma ((k : ℝ) + 1 / 2) / Real.Gamma (k : ℝ) :=
      integral_positiveRadius_eq_gammaRatio hk

/-- Exact first absolute moment of the scalar circular Gaussian. -/
theorem integral_norm_circularGaussian :
    (∫ z : ℂ, ‖z‖ ∂circularGaussian) = Real.Gamma (3 / 2) := by
  let e := MeasurableEquiv.funUnique (Fin 1) ℂ
  have he : MeasurePreserving e
      (Measure.pi fun _ : Fin 1 ↦ circularGaussian) circularGaussian :=
    measurePreserving_funUnique circularGaussian (Fin 1)
  have hraw :
      (∫ z : ℂ, ‖z‖ ∂circularGaussian) =
        ∫ x : Fin 1 → ℂ, ‖WithLp.toLp 2 x‖
          ∂(Measure.pi fun _ : Fin 1 ↦ circularGaussian) := by
    calc
      (∫ z : ℂ, ‖z‖ ∂circularGaussian) =
          ∫ z : ℂ, ‖z‖
            ∂Measure.map e (Measure.pi fun _ : Fin 1 ↦ circularGaussian) := by
        rw [he.map_eq]
      _ = ∫ x : Fin 1 → ℂ, ‖e x‖
            ∂(Measure.pi fun _ : Fin 1 ↦ circularGaussian) := by
        rw [integral_map e.measurable.aemeasurable (by fun_prop)]
      _ = ∫ x : Fin 1 → ℂ, ‖WithLp.toLp 2 x‖
            ∂(Measure.pi fun _ : Fin 1 ↦ circularGaussian) := by
        apply integral_congr_ae
        filter_upwards [] with x
        change ‖x default‖ = ‖WithLp.toLp 2 x‖
        rw [PiLp.norm_eq_of_L2]
        simp [Real.sqrt_sq (norm_nonneg (x default))]
  calc
    (∫ z : ℂ, ‖z‖ ∂circularGaussian) =
        ∫ x : Fin 1 → ℂ, ‖WithLp.toLp 2 x‖
          ∂(Measure.pi fun _ : Fin 1 ↦ circularGaussian) := hraw
    _ = ∫ z : CircularEuclideanSpace 1, ‖z‖
          ∂(Measure.pi fun _ : Fin 1 ↦ circularGaussian).map (WithLp.toLp 2) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = Real.Gamma (((1 : ℕ) : ℝ) + 1 / 2) / Real.Gamma ((1 : ℕ) : ℝ) :=
      integral_norm_iidCircularEuclidean_eq_gammaRatio (by norm_num)
    _ = Real.Gamma (3 / 2) := by
      norm_num [Real.Gamma_one]

/-- First absolute moment of a transpose linear form of iid circular
Gaussians. -/
theorem integral_norm_iidCircularTransposeLinearForm
    {k : ℕ} (y : Fin k → ℂ) :
    (∫ z : Fin k → ℂ, ‖iidCircularTransposeLinearForm y z‖
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian)) =
      Real.sqrt (circularCoefficientEnergy y) * Real.Gamma (3 / 2) := by
  calc
    (∫ z : Fin k → ℂ, ‖iidCircularTransposeLinearForm y z‖
        ∂(Measure.pi fun _ : Fin k ↦ circularGaussian)) =
        ∫ w : ℂ, ‖w‖
          ∂(Measure.pi fun _ : Fin k ↦ circularGaussian).map
            (iidCircularTransposeLinearForm y) := by
      rw [integral_map (measurable_iidCircularTransposeLinearForm y).aemeasurable
        (by fun_prop)]
    _ = ∫ w : ℂ, ‖w‖
          ∂circularGaussian.map (fun z : ℂ ↦
            Real.sqrt (circularCoefficientEnergy y) • z) := by
      rw [map_iidCircularTransposeLinearForm_eq_scaled_circular]
    _ = ∫ z : ℂ, ‖Real.sqrt (circularCoefficientEnergy y) • z‖
          ∂circularGaussian := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = Real.sqrt (circularCoefficientEnergy y) *
          (∫ z : ℂ, ‖z‖ ∂circularGaussian) := by
      simp_rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [integral_const_mul]
    _ = Real.sqrt (circularCoefficientEnergy y) * Real.Gamma (3 / 2) := by
      rw [integral_norm_circularGaussian]

/-- Transpose linear form of a unit spherical direction. -/
def sphereTransposeLinearForm {k : ℕ} (y : Fin k → ℂ)
    (u : sphere (0 : CircularEuclideanSpace k) 1) : ℂ :=
  ∑ p, WithLp.ofLp u.1 p * y p

@[fun_prop]
theorem measurable_sphereTransposeLinearForm {k : ℕ} (y : Fin k → ℂ) :
    Measurable (sphereTransposeLinearForm y) := by
  unfold sphereTransposeLinearForm
  fun_prop

/-- Polar reconstruction separates the norm of a transpose form into its
positive radius and its spherical direction. -/
theorem norm_iidCircularTransposeLinearForm_polar
    {k : ℕ} (y : Fin k → ℂ)
    (u : sphere (0 : CircularEuclideanSpace k) 1) (r : Ioi (0 : ℝ)) :
    ‖iidCircularTransposeLinearForm y
        (circularGaussianPolarRawReconstruct k (u, r))‖ =
      ‖sphereTransposeLinearForm y u‖ * (r.1 : ℝ) := by
  unfold iidCircularTransposeLinearForm sphereTransposeLinearForm
  simp_rw [circularGaussianPolarRawReconstruct_apply]
  rw [show (∑ x, ((r.1 : ℂ) * WithLp.ofLp u.1 x) * y x) =
      (r.1 : ℂ) * ∑ x, WithLp.ofLp u.1 x * y x by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _hx
    ring]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (show 0 < (r.1 : ℝ) from r.2)]
  ring

/-- Exact first absolute moment of a spherical transpose linear form. -/
theorem integral_norm_sphereTransposeLinearForm
    {k : ℕ} (hk : 0 < k) (y : Fin k → ℂ) :
    (∫ u, ‖sphereTransposeLinearForm y u‖
        ∂circularGaussianSphereProbability k) =
      sphereCoordinateAbsMean k *
        Real.sqrt (circularCoefficientEnergy y) := by
  let S := circularGaussianSphereProbability k
  let R := circularGaussianPositiveRadiusMeasure k
  let P := Measure.pi fun _ : Fin k ↦ circularGaussian
  letI : IsProbabilityMeasure S := by
    exact ⟨by simpa [S] using circularGaussianSphereProbability_apply_univ hk⟩
  letI : IsProbabilityMeasure R := by
    simpa [R] using isProbabilityMeasure_circularGaussianPositiveRadiusMeasure hk
  let radiusMean : ℝ :=
    ∫ r : Ioi (0 : ℝ), (r.1 : ℝ)
      ∂circularGaussianPositiveRadiusMeasure k
  have hpolar :
      (∫ z, ‖iidCircularTransposeLinearForm y z‖ ∂P) =
        (∫ u, ‖sphereTransposeLinearForm y u‖ ∂S) *
          radiusMean := by
    calc
      (∫ z, ‖iidCircularTransposeLinearForm y z‖ ∂P) =
          ∫ q, ‖iidCircularTransposeLinearForm y q‖
            ∂Measure.map (circularGaussianPolarRawReconstruct k) (S.prod R) := by
        rw [map_circularGaussianPolarRawReconstruct hk]
        rfl
      _ = ∫ q, ‖iidCircularTransposeLinearForm y
              (circularGaussianPolarRawReconstruct k q)‖ ∂(S.prod R) := by
        rw [integral_map
          (measurable_circularGaussianPolarRawReconstruct k).aemeasurable
          ((measurable_iidCircularTransposeLinearForm y).norm.aestronglyMeasurable)]
      _ = ∫ q, ‖sphereTransposeLinearForm y q.1‖ * (q.2.1 : ℝ)
            ∂(S.prod R) := by
        apply integral_congr_ae
        filter_upwards [] with q
        exact norm_iidCircularTransposeLinearForm_polar y q.1 q.2
      _ = (∫ u, ‖sphereTransposeLinearForm y u‖ ∂S) *
            radiusMean := by
        simpa [radiusMean, R] using
          (integral_prod_mul
            (μ := S) (ν := R)
            (fun u ↦ ‖sphereTransposeLinearForm y u‖)
            (fun r : Ioi (0 : ℝ) ↦ (r.1 : ℝ)))
  have hnum := integral_norm_iidCircularTransposeLinearForm y
  have hrad := integral_positiveRadius_eq_gammaRatio hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hGk : 0 < Real.Gamma (k : ℝ) := Real.Gamma_pos_of_pos hkR
  have hGkh : 0 < Real.Gamma ((k : ℝ) + 1 / 2) :=
    Real.Gamma_pos_of_pos (by positivity)
  have hradPos : 0 < radiusMean := by
    rw [show radiusMean =
      Real.Gamma ((k : ℝ) + 1 / 2) / Real.Gamma (k : ℝ) by
      simpa [radiusMean] using hrad]
    exact div_pos hGkh hGk
  rw [show radiusMean =
    Real.Gamma ((k : ℝ) + 1 / 2) / Real.Gamma (k : ℝ) by
      simpa [radiusMean] using hrad] at hpolar
  rw [show (∫ z, ‖iidCircularTransposeLinearForm y z‖ ∂P) =
    Real.sqrt (circularCoefficientEnergy y) * Real.Gamma (3 / 2) by
      simpa [P] using hnum] at hpolar
  unfold sphereCoordinateAbsMean
  change (∫ u, ‖sphereTransposeLinearForm y u‖ ∂S) = _
  calc
    (∫ u, ‖sphereTransposeLinearForm y u‖ ∂S) =
        (Real.sqrt (circularCoefficientEnergy y) * Real.Gamma (3 / 2)) /
          (Real.Gamma ((k : ℝ) + 1 / 2) / Real.Gamma (k : ℝ)) := by
      apply (eq_div_iff (div_ne_zero hGkh.ne' hGk.ne')).2
      exact hpolar.symm
    _ = Real.Gamma (3 / 2) * Real.Gamma (k : ℝ) /
          Real.Gamma ((k : ℝ) + 1 / 2) *
            Real.sqrt (circularCoefficientEnergy y) := by
      field_simp [hGk.ne', hGkh.ne']

end WickAngularLowerBound

end

end LogdetLean.GramHafnian
