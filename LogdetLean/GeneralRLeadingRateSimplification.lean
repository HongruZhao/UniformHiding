import LogdetLean.GeneralRConcreteRates
import LogdetLean.ComplexPolygammaSeries
import LogdetLean.WishartPopulationCorrection
import Mathlib.Tactic

/-!
# Deterministic simplification of the general-correlation third derivative

This file converts the exact spectral third-derivative envelope into the
three dimensionless rates used by the quantitative theorem.  The spectral
version is deliberately kept separate from the coarser energy-only envelope:
the former retains `sum_i |lambda_i(R-I)|^3`, whereas replacing that sum by
`a_R^(3/2)` loses the spectral rate.

No probability or Fourier inversion is used here.
-/

namespace LogdetLean

noncomputable section

open scoped BigOperators

/-- The sharp spectral envelope for the third logarithmic derivative.

It differs from the energy-only envelope only in its last term: here the
actual cubic eigenvalue mass is retained instead of being enlarged to
`a_R^(3/2)`.
-/
def generalRLeadingThirdEnvelopeSpectral {p : ℕ}
    (m : ℕ) (R : CorrelationMatrix p) : ℝ :=
  nullASeries m p + 16 * (p : ℝ) / (m : ℝ) ^ 3 +
    (12 * R.deviationEnergy) / (m : ℝ) ^ 2 +
    (8 * ∑ i, |R.deviationEigenvalues i| ^ 3) / (m : ℝ) ^ 2

/-- The population third derivative with the cubic eigenvalue sum retained.
The older energy-only statement follows from this one by the Schatten
inequality, but that final enlargement is intentionally not made here. -/
theorem norm_wishartPopulationCorrectionThree_imaginary_le_spectral
    {p : ℕ} (R : CorrelationMatrix p) {m u : ℝ} (hm : 0 < m) :
    ‖wishartPopulationCorrectionThree R m
        ((u : ℂ) * Complex.I)‖ ≤
      (12 * R.deviationEnergy) / m ^ 2 +
        (8 * ∑ i, |R.deviationEigenvalues i| ^ 3) / m ^ 2 := by
  unfold wishartPopulationCorrectionThree
  calc
    ‖∑ i, wishartScalarLogTermThree (m / 2)
        (1 + R.deviationEigenvalues i) ((u : ℂ) * Complex.I)‖ ≤
        ∑ i, ‖wishartScalarLogTermThree (m / 2)
          (1 + R.deviationEigenvalues i) ((u : ℂ) * Complex.I)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, (12 * R.deviationEigenvalues i ^ 2 +
          8 * |R.deviationEigenvalues i| ^ 3) / m ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [wishartScalarLogTermThree_imaginary_eq_expression
        (by positivity) (R.one_add_deviationEigenvalue_pos i)]
      have hlambda :
          1 + R.deviationEigenvalues i - 1 = R.deviationEigenvalues i := by
        ring
      rw [hlambda]
      exact norm_wishartScalarThirdExpression_half_dimension_le
        (r := 1 + R.deviationEigenvalues i)
        (lambda := R.deviationEigenvalues i) (u := u) hm
    _ = (12 * ∑ i, R.deviationEigenvalues i ^ 2) / m ^ 2 +
        (8 * ∑ i, |R.deviationEigenvalues i| ^ 3) / m ^ 2 := by
      calc
        ∑ i, (12 * R.deviationEigenvalues i ^ 2 +
              8 * |R.deviationEigenvalues i| ^ 3) / m ^ 2 =
            (∑ i, (12 * R.deviationEigenvalues i ^ 2 +
              8 * |R.deviationEigenvalues i| ^ 3)) / m ^ 2 := by
                rw [Finset.sum_div]
        _ = ((12 * ∑ i, R.deviationEigenvalues i ^ 2) +
              (8 * ∑ i, |R.deviationEigenvalues i| ^ 3)) / m ^ 2 := by
            congr 1
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = (12 * ∑ i, R.deviationEigenvalues i ^ 2) / m ^ 2 +
              (8 * ∑ i, |R.deviationEigenvalues i| ^ 3) / m ^ 2 :=
            add_div _ _ _
    _ = (12 * R.deviationEnergy) / m ^ 2 +
        (8 * ∑ i, |R.deviationEigenvalues i| ^ 3) / m ^ 2 := by
      rw [R.deviationEnergy_eq_sum_eigenvalues_sq]

/-- Global third-derivative estimate before introducing the actual transform
curve.  This is the exact analytic input consumed by that curve module. -/
theorem norm_wishartLeadingThirdAxis_le_spectral
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) (u : ℝ) :
    ‖wishartIdentityThirdAxis m p u +
        wishartPopulationCorrectionThree R (m : ℝ)
          ((u : ℂ) * Complex.I)‖ ≤
      generalRLeadingThirdEnvelopeSpectral m R := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  calc
    ‖wishartIdentityThirdAxis m p u +
        wishartPopulationCorrectionThree R (m : ℝ)
          ((u : ℂ) * Complex.I)‖ ≤
        ‖wishartIdentityThirdAxis m p u‖ +
          ‖wishartPopulationCorrectionThree R (m : ℝ)
            ((u : ℂ) * Complex.I)‖ := norm_add_le _ _
    _ ≤ (nullASeries m p + 16 * (p : ℝ) / (m : ℝ) ^ 3) +
        ((12 * R.deviationEnergy) / (m : ℝ) ^ 2 +
          (8 * ∑ i, |R.deviationEigenvalues i| ^ 3) / (m : ℝ) ^ 2) :=
      add_le_add (norm_wishartIdentityThirdAxis_le h u)
        (norm_wishartPopulationCorrectionThree_imaginary_le_spectral R hmR)
    _ = generalRLeadingThirdEnvelopeSpectral m R := by
      unfold generalRLeadingThirdEnvelopeSpectral
      ring

/-- The proxy scale dominates the null standard deviation. -/
theorem sqrt_nullVSeries_le_generalRProxyScale
    {m p : ℕ} (_h : Admissible m p) (R : CorrelationMatrix p) :
    Real.sqrt (nullVSeries m p) ≤ generalRProxyScale m R := by
  unfold generalRProxyScale generalRVarianceProxy
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_right
    (div_nonneg (mul_nonneg (by norm_num) R.deviationEnergy_nonneg)
      (Nat.cast_nonneg _))

/-- A convenient null lower bound on the proxy standard deviation. -/
theorem pred_div_dimension_le_generalRProxyScale
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    ((p : ℝ) - 1) / (m : ℝ) ≤ generalRProxyScale m R := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpR : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (show 1 < p by omega)
  have hq0 : 0 ≤ ((p : ℝ) - 1) / (m : ℝ) := by positivity
  have hs0 : 0 ≤ generalRProxyScale m R :=
    (generalRProxyScale_pos h R).le
  apply (sq_le_sq₀ hq0 hs0).mp
  rw [generalRProxyScale_sq h R]
  have hnull := nullVSeries_lower_p_mul_pred_div_m_sq h
  have hproxy :
      (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤
        generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy := by
    unfold generalRVarianceProxy
    exact hnull.trans (le_add_of_nonneg_right
      (div_nonneg (mul_nonneg (by norm_num) R.deviationEnergy_nonneg)
        (Nat.cast_nonneg _)))
  calc
    (((p : ℝ) - 1) / (m : ℝ)) ^ 2 ≤
        (p : ℝ) * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
      field_simp [hmR.ne']
      nlinarith [hpR.le]
    _ ≤ generalRVarianceProxy m (nullVSeries m p) R.deviationEnergy := hproxy

/-- The exact leading scale is no smaller than the proxy scale. -/
theorem generalRProxyScale_le_generalRLeadingScale
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRProxyScale m R ≤ generalRLeadingScale m R := by
  have hs0 := (generalRProxyScale_pos h R).le
  have hw0 := (generalRLeadingScale_pos h R).le
  apply (sq_le_sq₀ hs0 hw0).mp
  linarith [(generalRScale_difference_bounds h R).1]

/-- The identity radial correction contributes at most `32/(p-1)` after
normalization by the proxy scale. -/
theorem identity_radial_third_rate_le
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    (16 * (p : ℝ) / (m : ℝ) ^ 3) /
        generalRProxyScale m R ^ 3 ≤ 32 / ((p : ℝ) - 1) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpR : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (show 1 < p by omega)
  have hpTwoR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hqpos : 0 < ((p : ℝ) - 1) / (m : ℝ) := by positivity
  have hspos := generalRProxyScale_pos h R
  have hscale := pred_div_dimension_le_generalRProxyScale h R
  have hpow := pow_le_pow_left₀ hqpos.le hscale 3
  calc
    (16 * (p : ℝ) / (m : ℝ) ^ 3) /
        generalRProxyScale m R ^ 3 ≤
        (16 * (p : ℝ) / (m : ℝ) ^ 3) /
          (((p : ℝ) - 1) / (m : ℝ)) ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hqpos 3) hpow
    _ = 16 * (p : ℝ) / ((p : ℝ) - 1) ^ 3 := by
      field_simp [hmR.ne', sub_ne_zero.mpr hpR.ne']
    _ ≤ 32 / ((p : ℝ) - 1) := by
      apply (div_le_div_iff₀ (pow_pos (sub_pos.mpr hpR) 3)
        (sub_pos.mpr hpR)).2
      have hpTwo : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by nlinarith
      have hpPred : 1 ≤ (p : ℝ) - 1 := by nlinarith
      nlinarith [sq_nonneg ((p : ℝ) - 1)]

/-- The quadratic population correction contributes at most `6/(p-1)`.
-/
theorem population_quadratic_third_rate_le
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    ((12 * R.deviationEnergy) / (m : ℝ) ^ 2) /
        generalRProxyScale m R ^ 3 ≤ 6 / ((p : ℝ) - 1) := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpR : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (show 1 < p by omega)
  have hspos := generalRProxyScale_pos h R
  have hcorr :
      2 * R.deviationEnergy / (m : ℝ) ≤
        generalRProxyScale m R ^ 2 := by
    rw [generalRProxyScale_sq h R]
    unfold generalRVarianceProxy
    exact le_add_of_nonneg_left (nullVSeries_nonneg h.2)
  have hscale := pred_div_dimension_le_generalRProxyScale h R
  have hmScale : (p : ℝ) - 1 ≤
      (m : ℝ) * generalRProxyScale m R := by
    simpa [mul_comm] using (div_le_iff₀ hmR).mp hscale
  apply (div_le_div_iff₀ (pow_pos hspos 3) (sub_pos.mpr hpR)).2
  calc
    (12 * R.deviationEnergy / (m : ℝ) ^ 2) * ((p : ℝ) - 1) ≤
        (12 * R.deviationEnergy / (m : ℝ) ^ 2) *
          ((m : ℝ) * generalRProxyScale m R) :=
      mul_le_mul_of_nonneg_left hmScale
        (div_nonneg
          (mul_nonneg (by norm_num) R.deviationEnergy_nonneg)
          (sq_nonneg _))
    _ = (6 * generalRProxyScale m R) *
          (2 * R.deviationEnergy / (m : ℝ)) := by
      field_simp [hmR.ne']
      ring
    _ ≤ (6 * generalRProxyScale m R) *
          generalRProxyScale m R ^ 2 :=
      mul_le_mul_of_nonneg_left hcorr (by positivity)
    _ = 6 * generalRProxyScale m R ^ 3 := by ring

/-- Proxy-scale simplification of the sharp spectral envelope.

The constant `38=32+6` is intentionally elementary rather than optimized.
-/
theorem generalRLeadingThirdEnvelopeSpectral_div_proxyScale_cube_le
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRLeadingThirdEnvelopeSpectral m R /
        generalRProxyScale m R ^ 3 ≤
      nullLambdaSeries m p + 38 / ((p : ℝ) - 1) +
        8 * generalRSpectralCubicRate m R := by
  have hA0 := (nullASeries_pos h).le
  have hVroot := Real.sqrt_pos.2 (nullVSeries_pos h)
  have hspos := generalRProxyScale_pos h R
  have hnullScale := sqrt_nullVSeries_le_generalRProxyScale h R
  have hnullPow := pow_le_pow_left₀ hVroot.le hnullScale 3
  have hnull :
      nullASeries m p / generalRProxyScale m R ^ 3 ≤
        nullLambdaSeries m p := by
    calc
      nullASeries m p / generalRProxyScale m R ^ 3 ≤
          nullASeries m p / (Real.sqrt (nullVSeries m p)) ^ 3 :=
        div_le_div_of_nonneg_left hA0 (pow_pos hVroot 3) hnullPow
      _ = nullLambdaSeries m p := by
        rw [nullLambdaSeries_eq, nullVSeries_rpow_three_halves h]
  have hid := identity_radial_third_rate_le h R
  have hquad := population_quadratic_third_rate_le h R
  have hcubic :
      ((8 * ∑ i, |R.deviationEigenvalues i| ^ 3) / (m : ℝ) ^ 2) /
          generalRProxyScale m R ^ 3 =
        8 * generalRSpectralCubicRate m R := by
    unfold generalRSpectralCubicRate generalRCubicRateRho
    ring
  unfold generalRLeadingThirdEnvelopeSpectral generalRSpectralCubicRate
    generalRCubicRateRho
  rw [add_div, add_div, add_div]
  rw [hcubic]
  calc
    nullASeries m p / generalRProxyScale m R ^ 3 +
          (16 * (p : ℝ) / (m : ℝ) ^ 3) /
              generalRProxyScale m R ^ 3 +
        ((12 * R.deviationEnergy) / (m : ℝ) ^ 2) /
            generalRProxyScale m R ^ 3 +
      8 * ((∑ i, |R.deviationEigenvalues i| ^ 3) /
            ((m : ℝ) ^ 2 * generalRProxyScale m R ^ 3)) ≤
        nullLambdaSeries m p + 32 / ((p : ℝ) - 1) +
          6 / ((p : ℝ) - 1) +
          8 * ((∑ i, |R.deviationEigenvalues i| ^ 3) /
            ((m : ℝ) ^ 2 * generalRProxyScale m R ^ 3)) := by
      gcongr
    _ = nullLambdaSeries m p + 38 / ((p : ℝ) - 1) +
          8 * ((∑ i, |R.deviationEigenvalues i| ^ 3) /
            ((m : ℝ) ^ 2 * generalRProxyScale m R ^ 3)) := by ring

/-- Leading-scale version.  It follows because the exact leading standard
deviation is no smaller than the proxy standard deviation. -/
theorem generalRLeadingThirdEnvelopeSpectral_div_leadingScale_cube_le
    {m p : ℕ} (h : Admissible m p) (R : CorrelationMatrix p) :
    generalRLeadingThirdEnvelopeSpectral m R /
        generalRLeadingScale m R ^ 3 ≤
      nullLambdaSeries m p + 38 / ((p : ℝ) - 1) +
        8 * generalRSpectralCubicRate m R := by
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hm : 0 < m := by omega
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have henv : 0 ≤ generalRLeadingThirdEnvelopeSpectral m R := by
    unfold generalRLeadingThirdEnvelopeSpectral
    exact add_nonneg
      (add_nonneg
        (add_nonneg (nullASeries_nonneg h.2)
          (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
            (pow_nonneg hmR.le 3)))
        (div_nonneg (mul_nonneg (by norm_num) R.deviationEnergy_nonneg)
          (pow_nonneg hmR.le 2)))
      (div_nonneg
        (mul_nonneg (by norm_num)
          (Finset.sum_nonneg fun i _ ↦ pow_nonneg (abs_nonneg _) 3))
        (pow_nonneg hmR.le 2))
  have hspos := generalRProxyScale_pos h R
  have hscale := generalRProxyScale_le_generalRLeadingScale h R
  have hpow := pow_le_pow_left₀ hspos.le hscale 3
  exact (div_le_div_of_nonneg_left henv (pow_pos hspos 3) hpow).trans
    (generalRLeadingThirdEnvelopeSpectral_div_proxyScale_cube_le h R)

end

end LogdetLean
