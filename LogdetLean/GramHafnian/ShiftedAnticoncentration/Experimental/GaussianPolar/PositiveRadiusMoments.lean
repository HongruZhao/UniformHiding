import LogdetLean.GramHafnian.ShiftedAnticoncentration.Experimental.GaussianPolar.CircularGaussianPolarGamma

/-!
# Probability normalization and moments of the positive circular Gaussian radius

This file is the small moment bridge used by the radial lower-bound argument.
It transports the already proved squared-radius Gamma law back to the positive
polar-radius marginal.
-/

open MeasureTheory ProbabilityTheory Set

namespace LogdetLean.GramHafnian

noncomputable section

/-- The positive polar-radius marginal of a nonzero-dimensional circular
Gaussian column is a probability measure. -/
theorem isProbabilityMeasure_circularGaussianPositiveRadiusMeasure
    {k : ℕ} (hk : 0 < k) :
    IsProbabilityMeasure (circularGaussianPositiveRadiusMeasure k) := by
  rw [← Measure.isProbabilityMeasure_map_iff
    (μ := circularGaussianPositiveRadiusMeasure k)
    (f := fun r : Ioi (0 : ℝ) ↦ r.1 ^ 2) (by fun_prop)]
  change IsProbabilityMeasure (circularGaussianSquaredRadiusMeasure k)
  rw [circularGaussianSquaredRadiusMeasure_eq_halfGamma hk]
  let _ : IsProbabilityMeasure (gammaMeasure (k : ℝ) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure
      (show (0 : ℝ) < k by exact_mod_cast hk) (by norm_num)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Exact first moment of the positive squared circular Gaussian radius. -/
theorem integral_sq_circularGaussianPositiveRadiusMeasure
    {k : ℕ} (hk : 0 < k) :
    ∫ r : Ioi (0 : ℝ), r.1 ^ 2
        ∂circularGaussianPositiveRadiusMeasure k = (k : ℝ) := by
  rw [← integral_map
    (μ := circularGaussianPositiveRadiusMeasure k)
    (φ := fun r : Ioi (0 : ℝ) ↦ r.1 ^ 2)
    (f := fun x : ℝ ↦ x) (by fun_prop) (by fun_prop)]
  change ∫ x : ℝ, x ∂circularGaussianSquaredRadiusMeasure k = (k : ℝ)
  rw [circularGaussianSquaredRadiusMeasure_eq_halfGamma hk,
    integral_map (by fun_prop) (by fun_prop)]
  have hmellin := LogdetLean.integral_rpow_gammaMeasure
    (a := (k : ℝ)) (r := (1 / 2 : ℝ)) (t := 1)
    (show (0 : ℝ) < k by exact_mod_cast hk) (by norm_num) (by linarith)
  have hgamma : Real.Gamma ((k : ℝ) + 1) =
      (k : ℝ) * Real.Gamma (k : ℝ) :=
    Real.Gamma_add_one
      (show (k : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hk))
  have hG : Real.Gamma (k : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (show (0 : ℝ) < k by exact_mod_cast hk)).ne'
  calc
    (∫ u : ℝ, u / 2 ∂gammaMeasure (k : ℝ) (1 / 2)) =
        (1 / 2 : ℝ) *
          ((1 / 2 : ℝ) ^ (-1 : ℝ) *
            Real.Gamma ((k : ℝ) + 1) / Real.Gamma (k : ℝ)) := by
      rw [integral_div, show (∫ u : ℝ, u
          ∂gammaMeasure (k : ℝ) (1 / 2)) =
          (1 / 2 : ℝ) ^ (-1 : ℝ) *
            Real.Gamma ((k : ℝ) + 1) / Real.Gamma (k : ℝ) by
        simpa only [Real.rpow_one, neg_one_mul] using hmellin]
      ring
    _ = (k : ℝ) := by
      rw [hgamma]
      norm_num [Real.rpow_neg_one]
      field_simp [hG]

/-- Exact inverse first moment of the positive squared circular Gaussian
radius. -/
theorem integral_inv_sq_circularGaussianPositiveRadiusMeasure
    {k : ℕ} (hk : 2 ≤ k) :
    ∫ r : Ioi (0 : ℝ), (r.1 ^ 2)⁻¹
        ∂circularGaussianPositiveRadiusMeasure k =
      ((k : ℝ) - 1)⁻¹ := by
  have hkpos : 0 < k := by omega
  rw [← integral_map
    (μ := circularGaussianPositiveRadiusMeasure k)
    (φ := fun r : Ioi (0 : ℝ) ↦ r.1 ^ 2)
    (f := fun x : ℝ ↦ x⁻¹) (by fun_prop) (by fun_prop)]
  change ∫ x : ℝ, x⁻¹ ∂circularGaussianSquaredRadiusMeasure k = _
  rw [circularGaussianSquaredRadiusMeasure_eq_halfGamma hkpos,
    integral_map (by fun_prop) (by fun_prop)]
  have hpoint : (fun u : ℝ ↦ (u / 2)⁻¹) = fun u ↦ 2 * u⁻¹ := by
    funext u
    field_simp
  rw [hpoint, integral_const_mul,
    integral_inv_gammaMeasure
      (show (1 : ℝ) < k by exact_mod_cast (show 1 < k by omega))
      (by norm_num : (0 : ℝ) < 1 / 2)]
  ring

end

end LogdetLean.GramHafnian
