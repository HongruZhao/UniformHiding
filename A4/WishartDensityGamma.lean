import A4.Target
import Mathlib.Probability.Distributions.Gamma

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set Filter

noncomputable section

namespace A4Research

/-- Gamma variables used for the Bartlett pivots are strictly positive almost
surely, including every real positive shape. -/
theorem gammaMeasure_ae_pos (a r : ℝ) :
    ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  rw [gammaMeasure, ae_withDensity_iff]
  · filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    intro hpdf
    by_contra hpos
    have hneg : x < 0 := lt_of_le_of_ne (not_lt.mp hpos) hx
    exact hpdf (gammaPDF_of_neg hneg)
  · exact (measurable_gammaPDFReal a r).ennreal_ofReal

/-- The arbitrary real power moment of a Gamma pivot. The condition is the
exact integrability threshold at the origin, including negative moments. -/
theorem gammaMeasure_integral_rpow {a r q : ℝ}
    (ha : 0 < a) (hr : 0 < r) (haq : 0 < a + q) :
    (∫ x : ℝ, x ^ q ∂gammaMeasure a r) =
      r ^ (-q) * Real.Gamma (a + q) / Real.Gamma a := by
  unfold gammaMeasure gammaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gammaPDFReal a r).ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _),
    smul_eq_mul]
  have heq : (fun x : ℝ => gammaPDFReal a r x * x ^ q) =ᵐ[volume]
      (Ioi (0 : ℝ)).indicator (fun x =>
        (r ^ a / Real.Gamma a) * (x ^ (a + q - 1) * Real.exp (-(r * x)))) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    by_cases hpos : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hpos)]
      simp only [gammaPDFReal, if_pos hpos.le]
      rw [show a + q - 1 = (a - 1) + q by ring,
        Real.rpow_add hpos]
      ring
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hpos)]
      simp only [gammaPDFReal, if_neg (not_le.mpr
        (lt_of_le_of_ne (not_lt.mp hpos) hx)), zero_mul]
  rw [integral_congr_ae heq, integral_indicator measurableSet_Ioi,
    integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi haq hr]
  have hp : r ^ a * (1 / r) ^ (a + q) = r ^ (-q) := by
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_add hr]
    congr 1
    ring
  calc
    r ^ a / Real.Gamma a * ((1 / r) ^ (a + q) * Real.Gamma (a + q)) =
        (r ^ a * (1 / r) ^ (a + q)) * Real.Gamma (a + q) / Real.Gamma a := by ring
    _ = r ^ (-q) * Real.Gamma (a + q) / Real.Gamma a := by rw [hp]

theorem gammaMeasure_integrable_rpow {a r q : ℝ}
    (ha : 0 < a) (hr : 0 < r) (haq : 0 < a + q) :
    Integrable (fun x : ℝ => x ^ q) (gammaMeasure a r) := by
  apply Integrable.of_integral_ne_zero
  rw [gammaMeasure_integral_rpow ha hr haq]
  exact (div_pos (mul_pos (Real.rpow_pos_of_pos hr _)
    (Real.Gamma_pos_of_pos haq)) (Real.Gamma_pos_of_pos ha)).ne'

/-- The scalar exponential transform used when a Bartlett pivot is integrated
out. Its shape is arbitrary real, and the rate may vary with a matrix Schur
complement. -/
theorem gammaMeasure_integral_exp {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    (∫ x : ℝ, Real.exp (t * x) ∂gammaMeasure a r) =
      (r / (r - t)) ^ a := by
  unfold gammaMeasure gammaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gammaPDFReal a r).ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _),
    smul_eq_mul]
  have heq : (fun x : ℝ => gammaPDFReal a r x * Real.exp (t * x)) =ᵐ[volume]
      (Ioi (0 : ℝ)).indicator (fun x =>
        (r ^ a / Real.Gamma a) *
          (x ^ (a - 1) * Real.exp (-((r - t) * x)))) := by
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    by_cases hpos : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hpos)]
      simp only [gammaPDFReal, if_pos hpos.le]
      rw [show -((r - t) * x) = -(r * x) + t * x by ring,
        Real.exp_add]
      ring
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hpos)]
      simp only [gammaPDFReal, if_neg (not_le.mpr
        (lt_of_le_of_ne (not_lt.mp hpos) hx)), zero_mul]
  rw [integral_congr_ae heq, integral_indicator measurableSet_Ioi,
    integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi ha (sub_pos.mpr ht)]
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  rw [mul_comm ((1 / (r - t)) ^ a) (Real.Gamma a), ← mul_assoc,
    div_mul_cancel₀ _ hG]
  rw [one_div, ← Real.mul_rpow hr.le (inv_nonneg.mpr (sub_pos.mpr ht).le),
    div_eq_mul_inv]

theorem gammaMeasure_integrable_exp {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (gammaMeasure a r) := by
  apply Integrable.of_integral_ne_zero
  rw [gammaMeasure_integral_exp ha hr ht]
  exact (Real.rpow_pos_of_pos (div_pos hr (sub_pos.mpr ht)) a).ne'

end A4Research
