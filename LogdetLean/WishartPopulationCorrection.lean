import LogdetLean.CorrelationEigenvalues
import LogdetLean.WishartScalarDifferentiation
import Mathlib.Tactic

/-!
# Branch-safe population correction in the Wishart transform

This file packages the part of the general-correlation matrix-Gamma
calculation that is independent of the multivariate integral.  After
diagonalizing `R`, the compatible logarithm of

`(alpha + r z) / (alpha + z)`

is defined as the difference of the two principal logarithms.  On the
half-plane used by Zhao both affine terms have positive real part, so this is
a single-valued holomorphic branch and its exponential is exactly the
quotient.  The finite sum is the term called `D_A` in Zhao,
arXiv:2608.00565v1, equations (5.20)--(5.23), and in Appendix Lemmas 1--2 of
`work/audits/generalR_proof_audit.md`.

The three differentiations and their global imaginary-axis bound are
assembled here from the kernel-checked scalar results in
`WishartScalarDifferentiation` and `WishartScalarThird`.
-/

namespace LogdetLean

noncomputable section

open Complex Matrix Set
open scoped BigOperators

/-- The scalar eigenvalue ratio whose logarithm occurs in `D_A`. -/
def wishartScalarRatio (alpha r : ℝ) (z : ℂ) : ℂ :=
  ((alpha : ℂ) + (r : ℂ) * z) / ((alpha : ℂ) + z)

/-- A quotient of two numbers in the open right half-plane cannot lie on the
nonpositive real axis. -/
theorem div_mem_slitPlane_of_re_pos {a b : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) :
    a / b ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (a / b).im = 0
  · left
    have hb0 : b ≠ 0 := by
      intro hzero
      subst b
      simp at hb
    have hab : (a / b) * b = a := div_mul_cancel₀ a hb0
    have hre : a.re = (a / b).re * b.re := by
      have := congrArg Complex.re hab
      simpa [him] using this.symm
    by_contra hq
    have hqle : (a / b).re ≤ 0 := le_of_not_gt hq
    have : a.re ≤ 0 := by
      rw [hre]
      exact mul_nonpos_of_nonpos_of_nonneg hqle hb.le
    linarith
  · exact Or.inr him

/-- The compatible difference-of-logs branch exponentiates to the exact
scalar ratio. -/
theorem exp_wishartScalarLogDiff_eq_ratio
    {alpha r : ℝ} {z : ℂ}
    (hnum : 0 < (((alpha : ℂ) + (r : ℂ) * z).re))
    (hden : 0 < (((alpha : ℂ) + z).re)) :
    Complex.exp (wishartScalarLogDiff alpha r z) =
      wishartScalarRatio alpha r z := by
  have hnum0 : (alpha : ℂ) + (r : ℂ) * z ≠ 0 := by
    intro hzero
    rw [hzero] at hnum
    simp at hnum
  have hden0 : (alpha : ℂ) + z ≠ 0 := by
    intro hzero
    rw [hzero] at hden
    simp at hden
  unfold wishartScalarLogDiff wishartScalarRatio
  rw [Complex.exp_sub, Complex.exp_log hnum0, Complex.exp_log hden0]

/-- On the same domain the ratio itself lies in the slit plane.  Thus the
branch contains no hidden multiple of `2*pi*I`. -/
theorem wishartScalarRatio_mem_slitPlane
    {alpha r : ℝ} {z : ℂ}
    (hnum : 0 < (((alpha : ℂ) + (r : ℂ) * z).re))
    (hden : 0 < (((alpha : ℂ) + z).re)) :
    wishartScalarRatio alpha r z ∈ Complex.slitPlane := by
  exact div_mem_slitPlane_of_re_pos hnum hden

/-- Population-dependent logarithmic correction, written in the compatible
eigenvalue branch. -/
def wishartPopulationCorrection {p : ℕ}
    (R : CorrelationMatrix p) (m : ℝ) (z : ℂ) : ℂ :=
  ∑ i, wishartScalarLogTerm (m / 2)
    (1 + R.deviationEigenvalues i) z

/-- The explicit third derivative of the population correction. -/
def wishartPopulationCorrectionThree {p : ℕ}
    (R : CorrelationMatrix p) (m : ℝ) (z : ℂ) : ℂ :=
  ∑ i, wishartScalarLogTermThree (m / 2)
    (1 + R.deviationEigenvalues i) z

@[simp]
theorem wishartPopulationCorrection_zero {p : ℕ}
    (R : CorrelationMatrix p) (m : ℝ) :
    wishartPopulationCorrection R m 0 = 0 := by
  simp [wishartPopulationCorrection, wishartScalarLogTerm,
    wishartScalarLogDiff]

/-- First derivative of the finite compatible-branch sum. -/
theorem hasDerivAt_wishartPopulationCorrection
    {p : ℕ} {R : CorrelationMatrix p} {m : ℝ} {z : ℂ}
    (hnum : ∀ i, ((m / 2 : ℝ) : ℂ) +
      (1 + R.deviationEigenvalues i : ℝ) * z ∈ Complex.slitPlane)
    (hden : ((m / 2 : ℝ) : ℂ) + z ∈ Complex.slitPlane) :
    HasDerivAt (wishartPopulationCorrection R m)
      (∑ i, wishartScalarLogTermOne (m / 2)
        (1 + R.deviationEigenvalues i) z) z := by
  unfold wishartPopulationCorrection
  exact HasDerivAt.fun_sum fun i _ ↦
    hasDerivAt_wishartScalarLogTerm (hnum i) hden

/-- Second derivative of the finite compatible-branch sum. -/
theorem hasDerivAt_wishartPopulationCorrectionOne
    {p : ℕ} {R : CorrelationMatrix p} {m : ℝ} {z : ℂ}
    (hnum : ∀ i, ((m / 2 : ℝ) : ℂ) +
      (1 + R.deviationEigenvalues i : ℝ) * z ∈ Complex.slitPlane)
    (hden : ((m / 2 : ℝ) : ℂ) + z ∈ Complex.slitPlane) :
    HasDerivAt
      (fun w ↦ ∑ i, wishartScalarLogTermOne (m / 2)
        (1 + R.deviationEigenvalues i) w)
      (∑ i, wishartScalarLogTermTwo (m / 2)
        (1 + R.deviationEigenvalues i) z) z := by
  exact HasDerivAt.fun_sum fun i _ ↦
    hasDerivAt_wishartScalarLogTermOne (hnum i) hden

/-- Third derivative of the finite compatible-branch sum. -/
theorem hasDerivAt_wishartPopulationCorrectionTwo
    {p : ℕ} {R : CorrelationMatrix p} {m : ℝ} {z : ℂ}
    (hnum : ∀ i, ((m / 2 : ℝ) : ℂ) +
      (1 + R.deviationEigenvalues i : ℝ) * z ∈ Complex.slitPlane)
    (hden : ((m / 2 : ℝ) : ℂ) + z ∈ Complex.slitPlane) :
    HasDerivAt
      (fun w ↦ ∑ i, wishartScalarLogTermTwo (m / 2)
        (1 + R.deviationEigenvalues i) w)
      (wishartPopulationCorrectionThree R m z) z := by
  unfold wishartPopulationCorrectionThree
  exact HasDerivAt.fun_sum fun i _ ↦
    hasDerivAt_wishartScalarLogTermTwo (hnum i) hden

/-- Global third-derivative envelope for the population correction.  It is
uniform even when the smallest eigenvalue of `R` approaches zero. -/
theorem norm_wishartPopulationCorrectionThree_imaginary_le
    {p : ℕ} (R : CorrelationMatrix p) {m u : ℝ} (hm : 0 < m) :
    ‖wishartPopulationCorrectionThree R m ((u : ℂ) * Complex.I)‖ ≤
      (12 * R.deviationEnergy) / m ^ 2 +
        (8 * (Real.sqrt R.deviationEnergy * R.deviationEnergy)) / m ^ 2 := by
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
    _ ≤ (12 * R.deviationEnergy) / m ^ 2 +
        (8 * (Real.sqrt R.deviationEnergy * R.deviationEnergy)) / m ^ 2 := by
      rw [← R.deviationEnergy_eq_sum_eigenvalues_sq]
      gcongr
      exact R.sum_abs_deviationEigenvalues_cube_le

end

end LogdetLean
