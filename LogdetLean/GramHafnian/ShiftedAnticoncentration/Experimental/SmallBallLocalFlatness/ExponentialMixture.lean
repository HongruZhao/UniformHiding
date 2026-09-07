import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Finite local flatness for positive exponential mixtures

This file isolates the universal analytic part of the small-ball argument.
For a positive mixing variable `X`, it studies

* `rho(t) = E[X⁻¹ exp (-t / X)]`,
* `F(t)   = E[1 - exp (-t / X)]`,
* `Lambda = E[X⁻¹]`, and
* `L2     = E[X⁻²]`.

The hafnian-specific higher inverse-moment estimate is deliberately not an
input to this module.  In particular, the results below introduce no new
scientific axiom and impose no dimension hypothesis.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian

noncomputable section

/-! ## Scalar exponential inequalities -/

/-- The second-order alternating bound for the negative exponential. -/
theorem exp_neg_le_one_sub_add_sq_div_two {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  let P : ℝ := 1 + u + u ^ 2 / 2
  let Q : ℝ := 1 - u + u ^ 2 / 2
  have hPpos : 0 < P := by
    dsimp [P]
    nlinarith [sq_nonneg u]
  have hquad : P ≤ Real.exp u := by
    simpa [P, add_assoc] using Real.quadratic_le_exp_of_nonneg hu
  have hmul : P * Real.exp (-u) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hquad (Real.exp_pos (-u)).le
    simpa [← Real.exp_add] using h
  have hPQ : 1 ≤ P * Q := by
    dsimp [P, Q]
    nlinarith [sq_nonneg (u ^ 2)]
  have hcompare : P * Real.exp (-u) ≤ P * Q := hmul.trans hPQ
  exact le_of_mul_le_mul_left hcompare hPpos

/-- First-order loss of the exponential kernel. -/
theorem one_sub_exp_neg_le {u : ℝ} (_hu : 0 ≤ u) :
    1 - Real.exp (-u) ≤ u := by
  linarith [Real.one_sub_le_exp_neg u]

/-- Second-order loss of the exponential distribution function. -/
theorem sub_one_add_exp_neg_le_sq_div_two {u : ℝ} (hu : 0 ≤ u) :
    u - (1 - Real.exp (-u)) ≤ u ^ 2 / 2 := by
  linarith [exp_neg_le_one_sub_add_sq_div_two hu]

/-! ## Pointwise kernels -/

def exponentialMixtureDensityKernel (x t : ℝ) : ℝ :=
  x⁻¹ * Real.exp (-t / x)

def exponentialMixtureCDFKernel (x t : ℝ) : ℝ :=
  1 - Real.exp (-t / x)

/-- The density kernel is at most its value at zero. -/
theorem exponentialMixtureDensityKernel_le_inv
    {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    exponentialMixtureDensityKernel x t ≤ x⁻¹ := by
  unfold exponentialMixtureDensityKernel
  have hexp : Real.exp (-t / x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa [neg_div] using neg_nonpos.mpr (div_nonneg ht hx.le)
  exact mul_le_of_le_one_right (inv_nonneg.mpr hx.le) hexp

/-- The density loss is nonnegative. -/
theorem exponentialMixtureDensityLoss_nonneg
    {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    0 ≤ x⁻¹ - exponentialMixtureDensityKernel x t := by
  exact sub_nonneg.mpr (exponentialMixtureDensityKernel_le_inv hx ht)

/-- Exact first-order pointwise density-loss estimate. -/
theorem exponentialMixtureDensityLoss_le
    {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    x⁻¹ - exponentialMixtureDensityKernel x t ≤ t * x⁻¹ ^ 2 := by
  have hu : 0 ≤ t / x := div_nonneg ht hx.le
  have h := one_sub_exp_neg_le hu
  unfold exponentialMixtureDensityKernel
  field_simp [hx.ne'] at h ⊢
  nlinarith

/-- The exponential-mixture CDF kernel is nonnegative. -/
theorem exponentialMixtureCDFKernel_nonneg
    {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    0 ≤ exponentialMixtureCDFKernel x t := by
  unfold exponentialMixtureCDFKernel
  have : Real.exp (-t / x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    simpa [neg_div] using neg_nonpos.mpr (div_nonneg ht hx.le)
  linarith

/-- The CDF kernel lies below its tangent at the origin. -/
theorem exponentialMixtureCDFKernel_le_linear
    {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    exponentialMixtureCDFKernel x t ≤ t * x⁻¹ := by
  have hu : 0 ≤ t / x := div_nonneg ht hx.le
  have h := one_sub_exp_neg_le hu
  unfold exponentialMixtureCDFKernel
  field_simp [hx.ne'] at h ⊢
  nlinarith

/-- Exact second-order pointwise CDF-loss estimate. -/
theorem exponentialMixtureCDFLoss_le
    {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    t * x⁻¹ - exponentialMixtureCDFKernel x t ≤
      t ^ 2 * x⁻¹ ^ 2 / 2 := by
  have hu : 0 ≤ t / x := div_nonneg ht hx.le
  have h := sub_one_add_exp_neg_le_sq_div_two hu
  unfold exponentialMixtureCDFKernel
  field_simp [hx.ne'] at h ⊢
  nlinarith

/-- The linearized CDF loss is nonnegative. -/
theorem exponentialMixtureCDFLoss_nonneg
    {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    0 ≤ t * x⁻¹ - exponentialMixtureCDFKernel x t := by
  exact sub_nonneg.mpr (exponentialMixtureCDFKernel_le_linear hx ht)

end

end LogdetLean.GramHafnian
