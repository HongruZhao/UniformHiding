import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Reusable exponential perturbation inequalities

Both the null Edgeworth argument and the general-correlation analytic-log
argument first control a logarithmic characteristic-function remainder and
then exponentiate it.  This file performs that deterministic step once.
-/

namespace LogdetLean

noncomputable section

/-- Global perturbation inequality for the complex exponential. -/
theorem norm_cexp_add_sub_cexp_le
    (z r : ℂ) :
    ‖Complex.exp (z + r) - Complex.exp z‖ ≤
      ‖Complex.exp z‖ * ‖r‖ * Real.exp ‖r‖ := by
  have hr := Complex.norm_exp_sub_sum_le_norm_mul_exp r 1
  have hrexp : ‖Complex.exp r - 1‖ ≤ ‖r‖ * Real.exp ‖r‖ := by
    simpa using hr
  rw [Complex.exp_add]
  have hid : Complex.exp z * Complex.exp r - Complex.exp z =
      Complex.exp z * (Complex.exp r - 1) := by ring
  rw [hid, norm_mul]
  simpa [mul_assoc] using
    mul_le_mul_of_nonneg_left hrexp (norm_nonneg (Complex.exp z))

/-- If the base exponent is real, the preceding inequality has the familiar
`exp(base + |remainder|)` form. -/
theorem norm_cexp_ofReal_add_sub_cexp_le
    (a : ℝ) (r : ℂ) :
    ‖Complex.exp ((a : ℂ) + r) - Complex.exp (a : ℂ)‖ ≤
      ‖r‖ * Real.exp (a + ‖r‖) := by
  calc
    ‖Complex.exp ((a : ℂ) + r) - Complex.exp (a : ℂ)‖ ≤
        ‖Complex.exp (a : ℂ)‖ * ‖r‖ * Real.exp ‖r‖ :=
      norm_cexp_add_sub_cexp_le (a : ℂ) r
    _ = ‖r‖ * Real.exp (a + ‖r‖) := by
      rw [Complex.norm_exp_ofReal, Real.exp_add]
      ring

/-- The local form used in the papers: if the logarithmic error is at most
`t^2/6`, Gaussian damping only weakens from `exp(-t^2/2)` to
`exp(-t^2/3)`. -/
theorem norm_cexp_gaussian_add_sub_gaussian_le
    (t : ℝ) (r : ℂ) (hr : ‖r‖ ≤ t ^ 2 / 6) :
    ‖Complex.exp (((-(t ^ 2 / 2) : ℝ) : ℂ) + r) -
        Complex.exp (((-(t ^ 2 / 2) : ℝ) : ℂ))‖ ≤
      ‖r‖ * Real.exp (-(t ^ 2) / 3) := by
  calc
    ‖Complex.exp (((-(t ^ 2 / 2) : ℝ) : ℂ) + r) -
        Complex.exp (((-(t ^ 2 / 2) : ℝ) : ℂ))‖ ≤
      ‖r‖ * Real.exp (-(t ^ 2 / 2) + ‖r‖) := by
        exact norm_cexp_ofReal_add_sub_cexp_le (-(t ^ 2 / 2)) r
    _ ≤ ‖r‖ * Real.exp (-(t ^ 2) / 3) := by
      gcongr
      linarith

end

end LogdetLean
