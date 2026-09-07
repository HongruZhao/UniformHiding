import LogdetLean.WishartPopulationCorrection
import LogdetLean.CorrelationEigenvalues
import Mathlib.Tactic

/-!
# Derivative coordinates and zero-frequency values of the population correction

This file names the first two derivatives already computed term by term in
`WishartPopulationCorrection`, then verifies their values at zero.  The
identities are elementary consequences of
`sum_i lambda_i(R-I)=tr(R-I)=0` and
`sum_i lambda_i(R-I)^2=a_R`.
-/

namespace LogdetLean

noncomputable section

open Complex Matrix Set
open scoped BigOperators

/-- First derivative of the finite population correction. -/
def wishartPopulationCorrectionOne {p : ℕ}
    (R : CorrelationMatrix p) (m : ℝ) (z : ℂ) : ℂ :=
  ∑ i, wishartScalarLogTermOne (m / 2)
    (1 + R.deviationEigenvalues i) z

/-- Second derivative of the finite population correction. -/
def wishartPopulationCorrectionTwo {p : ℕ}
    (R : CorrelationMatrix p) (m : ℝ) (z : ℂ) : ℂ :=
  ∑ i, wishartScalarLogTermTwo (m / 2)
    (1 + R.deviationEigenvalues i) z

/-- First differentiation, specialized to the imaginary axis where all
branch hypotheses follow from positive definiteness. -/
theorem hasDerivAt_wishartPopulationCorrection_axis
    {p : ℕ} (R : CorrelationMatrix p) {m : ℝ} (hm : 0 < m) (u : ℝ) :
    HasDerivAt (wishartPopulationCorrection R m)
      (wishartPopulationCorrectionOne R m ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
  apply hasDerivAt_wishartPopulationCorrection
  · intro i
    exact wishart_affine_imaginary_mem_slitPlane
      (alpha := m / 2) (r := 1 + R.deviationEigenvalues i) (u := u)
      (by positivity) (R.one_add_deviationEigenvalue_pos i)
  · simpa only [Complex.ofReal_one, one_mul] using
      (wishart_affine_imaginary_mem_slitPlane
        (alpha := m / 2) (r := 1) (u := u)
        (by positivity) (by norm_num))

/-- Second differentiation on the imaginary axis. -/
theorem hasDerivAt_wishartPopulationCorrectionOne_axis
    {p : ℕ} (R : CorrelationMatrix p) {m : ℝ} (hm : 0 < m) (u : ℝ) :
    HasDerivAt (wishartPopulationCorrectionOne R m)
      (wishartPopulationCorrectionTwo R m ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
  unfold wishartPopulationCorrectionOne wishartPopulationCorrectionTwo
  apply hasDerivAt_wishartPopulationCorrectionOne
  · intro i
    exact wishart_affine_imaginary_mem_slitPlane
      (alpha := m / 2) (r := 1 + R.deviationEigenvalues i) (u := u)
      (by positivity) (R.one_add_deviationEigenvalue_pos i)
  · simpa only [Complex.ofReal_one, one_mul] using
      (wishart_affine_imaginary_mem_slitPlane
        (alpha := m / 2) (r := 1) (u := u)
        (by positivity) (by norm_num))

/-- Third differentiation on the imaginary axis. -/
theorem hasDerivAt_wishartPopulationCorrectionTwo_axis
    {p : ℕ} (R : CorrelationMatrix p) {m : ℝ} (hm : 0 < m) (u : ℝ) :
    HasDerivAt (wishartPopulationCorrectionTwo R m)
      (wishartPopulationCorrectionThree R m ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
  unfold wishartPopulationCorrectionTwo
  apply hasDerivAt_wishartPopulationCorrectionTwo
  · intro i
    exact wishart_affine_imaginary_mem_slitPlane
      (alpha := m / 2) (r := 1 + R.deviationEigenvalues i) (u := u)
      (by positivity) (R.one_add_deviationEigenvalue_pos i)
  · simpa only [Complex.ofReal_one, one_mul] using
      (wishart_affine_imaginary_mem_slitPlane
        (alpha := m / 2) (r := 1) (u := u)
        (by positivity) (by norm_num))

namespace CorrelationMatrix

/-- The deviation eigenvalues sum to zero because a correlation matrix has
unit diagonal. -/
theorem sum_deviationEigenvalues_eq_zero {p : ℕ}
    (R : CorrelationMatrix p) :
    ∑ i, R.deviationEigenvalues i = 0 := by
  have htrace := R.deviation_isHermitian.trace_eq_sum_eigenvalues
  rw [R.trace_deviation] at htrace
  simpa [deviationEigenvalues] using htrace.symm

end CorrelationMatrix

private theorem wishartScalarLogTermOne_zero
    {alpha r : ℝ} (ha : 0 < alpha) :
    wishartScalarLogTermOne alpha r 0 = -((r - 1 : ℝ) : ℂ) := by
  unfold wishartScalarLogTermOne wishartScalarLogDiff
    wishartScalarLogDiffOne
  have haC : (alpha : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [show (alpha : ℂ) + (r : ℂ) * 0 = alpha by ring,
    show (alpha : ℂ) + 0 = alpha by ring]
  push_cast
  field_simp [haC]
  ring

private theorem wishartScalarLogTermTwo_zero
    {alpha r : ℝ} (ha : 0 < alpha) :
    wishartScalarLogTermTwo alpha r 0 =
      ((((r - 1) ^ 2 / alpha : ℝ)) : ℂ) := by
  unfold wishartScalarLogTermTwo wishartScalarLogDiffOne
    wishartScalarLogDiffTwo
  have haC : (alpha : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [show (alpha : ℂ) + (r : ℂ) * 0 = alpha by ring,
    show (alpha : ℂ) + 0 = alpha by ring]
  push_cast
  field_simp [haC]
  ring

/-- Centering cancellation in the population correction. -/
@[simp]
theorem wishartPopulationCorrectionOne_zero
    {p : ℕ} (R : CorrelationMatrix p) {m : ℝ} (hm : 0 < m) :
    wishartPopulationCorrectionOne R m 0 = 0 := by
  unfold wishartPopulationCorrectionOne
  simp_rw [wishartScalarLogTermOne_zero (show 0 < m / 2 by positivity)]
  calc
    ∑ i, -(((1 + R.deviationEigenvalues i) - 1 : ℝ) : ℂ) =
        -(∑ i, (R.deviationEigenvalues i : ℂ)) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      push_cast
      ring
    _ = -((∑ i, R.deviationEigenvalues i : ℝ) : ℂ) := by
      push_cast
      rfl
    _ = 0 := by rw [R.sum_deviationEigenvalues_eq_zero]; simp

/-- Exact quadratic population contribution to the leading variance. -/
theorem wishartPopulationCorrectionTwo_zero
    {p : ℕ} (R : CorrelationMatrix p) {m : ℝ} (hm : 0 < m) :
    wishartPopulationCorrectionTwo R m 0 =
      ((2 * R.deviationEnergy / m : ℝ) : ℂ) := by
  unfold wishartPopulationCorrectionTwo
  simp_rw [wishartScalarLogTermTwo_zero (show 0 < m / 2 by positivity)]
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hterm (i : Fin p) :
      ((((1 + R.deviationEigenvalues i) - 1) ^ 2 / (m / 2) : ℝ) : ℂ) =
        (2 / (m : ℂ)) * (R.deviationEigenvalues i : ℂ) ^ 2 := by
    push_cast
    field_simp [hm0]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, R.deviationEnergy_eq_sum_eigenvalues_sq]
  push_cast
  field_simp [hm.ne']

end

end LogdetLean
