import A4.WishartDensityGamma

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section
namespace A4Research

/-- Weighting a positive Gamma law by any admissible real power shifts its
shape. This is an equality of actual measures. -/
theorem gammaMeasure_withDensity_rpow {a p : ℝ} (ha : 0 < a) (hap : 0 < a + p) :
    (gammaMeasure a 1).withDensity (fun x : ℝ => ENNReal.ofReal (x ^ p)) =
      ENNReal.ofReal (Real.Gamma (a + p) / Real.Gamma a) • gammaMeasure (a + p) 1 := by
  let C : ℝ := Real.Gamma (a + p) / Real.Gamma a
  have hC : 0 < C := div_pos (Real.Gamma_pos_of_pos hap) (Real.Gamma_pos_of_pos ha)
  have hp : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ p)) :=
    (measurable_id.pow_const p).ennreal_ofReal
  have hpdfa : Measurable (gammaPDF a 1) := (measurable_gammaPDFReal a 1).ennreal_ofReal
  have hpdfap : Measurable (gammaPDF (a + p) 1) :=
    (measurable_gammaPDFReal (a + p) 1).ennreal_ofReal
  have heq : (gammaPDF a 1 * (fun x : ℝ => ENNReal.ofReal (x ^ p))) =ᵐ[volume]
      (ENNReal.ofReal C • gammaPDF (a + p) 1) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, gammaPDF]
    by_cases hpos : 0 < x
    · rw [← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha (by norm_num) x),
        ← ENNReal.ofReal_mul hC.le]
      congr 1
      simp only [gammaPDFReal, if_pos hpos.le, Real.one_rpow]
      rw [show a + p - 1 = (a - 1) + p by ring, Real.rpow_add hpos]
      dsimp [C]
      field_simp [(Real.Gamma_pos_of_pos ha).ne', (Real.Gamma_pos_of_pos hap).ne']
    · have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp hpos) hx
      simp only [gammaPDFReal, if_neg (not_le.mpr hneg), ENNReal.ofReal_zero,
        zero_mul, mul_zero]
  unfold gammaMeasure
  rw [← withDensity_mul volume hpdfa hp, withDensity_congr_ae heq,
    withDensity_smul _ hpdfap]

/-- Bochner expectations under the exact Gamma shape shift. -/
theorem gammaMeasure_integral_rpow_mul {a p : ℝ} (ha : 0 < a) (hap : 0 < a + p)
    (f : ℝ → ℝ) :
    (∫ x : ℝ, x ^ p * f x ∂gammaMeasure a 1) =
      (Real.Gamma (a + p) / Real.Gamma a) * (∫ x : ℝ, f x ∂gammaMeasure (a + p) 1) := by
  have hp : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ p)) :=
    (measurable_id.pow_const p).ennreal_ofReal
  have hEq := gammaMeasure_withDensity_rpow (p := p) ha hap
  have hInt := congrArg (fun mu : Measure ℝ => ∫ x : ℝ, f x ∂mu) hEq
  rw [integral_withDensity_eq_integral_toReal_smul hp
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_smul_measure] at hInt
  have heq : (fun x : ℝ => (ENNReal.ofReal (x ^ p)).toReal • f x) =ᵐ[gammaMeasure a 1]
      (fun x => x ^ p * f x) := by
    filter_upwards [gammaMeasure_ae_pos a 1] with x hx
    rw [ENNReal.toReal_ofReal (Real.rpow_pos_of_pos hx p).le, smul_eq_mul]
  rw [integral_congr_ae heq] at hInt
  simpa only [ENNReal.toReal_ofReal (div_pos (Real.Gamma_pos_of_pos hap)
    (Real.Gamma_pos_of_pos ha)).le, smul_eq_mul] using hInt

/-- Joint power and exponential transform, needed for the weighted full
Bartlett Laplace law. -/
theorem gammaMeasure_integral_rpow_mul_exp {a p t : ℝ}
    (ha : 0 < a) (hap : 0 < a + p) (ht : t < 1) :
    (∫ x : ℝ, x ^ p * Real.exp (t * x) ∂gammaMeasure a 1) =
      (Real.Gamma (a + p) / Real.Gamma a) * (1 - t) ^ (-(a + p)) := by
  rw [gammaMeasure_integral_rpow_mul ha hap, gammaMeasure_integral_exp hap (by norm_num) ht,
    one_div, ← Real.rpow_neg_eq_inv_rpow]

end A4Research
