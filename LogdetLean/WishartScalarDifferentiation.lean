import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic
import LogdetLean.WishartScalarThird

/-!
# Three verified differentiations of the scalar Wishart log term

After diagonalizing a correlation matrix, the non-null part of the analytic
Wishart log transform is a sum of the functions defined below.  This module
checks the three differentiations in the manuscript rather than accepting the
rational third derivative as a symbolic-computation input.

The logarithms are differentiated only when their arguments belong to
`Complex.slitPlane`.  On the imaginary axis, positive `alpha` and positive
`r` imply those hypotheses automatically.  The later matrix-transform module
must still prove that its analytic branch is this scalar logarithmic branch.
-/

namespace LogdetLean

open Complex Set

noncomputable section

/-- Difference of the two compatible scalar logarithms. -/
def wishartScalarLogDiff (alpha r : ℝ) (z : ℂ) : ℂ :=
  Complex.log ((alpha : ℂ) + (r : ℂ) * z) -
    Complex.log ((alpha : ℂ) + z)

def wishartScalarLogDiffOne (alpha r : ℝ) (z : ℂ) : ℂ :=
  (r : ℂ) / ((alpha : ℂ) + (r : ℂ) * z) -
    1 / ((alpha : ℂ) + z)

def wishartScalarLogDiffTwo (alpha r : ℝ) (z : ℂ) : ℂ :=
  -((r : ℂ) ^ 2) /
      (((alpha : ℂ) + (r : ℂ) * z) ^ 2) +
    1 / (((alpha : ℂ) + z) ^ 2)

def wishartScalarLogDiffThree (alpha r : ℝ) (z : ℂ) : ℂ :=
  2 * (r : ℂ) ^ 3 /
      (((alpha : ℂ) + (r : ℂ) * z) ^ 3) -
    2 / (((alpha : ℂ) + z) ^ 3)

private theorem hasDerivAt_affine_r (alpha r : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ (alpha : ℂ) + (r : ℂ) * w) (r : ℂ) z := by
  have h := ((hasDerivAt_id z).const_mul (r : ℂ)).const_add (alpha : ℂ)
  have h' : HasDerivAt
      (fun w : ℂ ↦ (alpha : ℂ) + (r : ℂ) * id w) (r : ℂ) z :=
    h.congr_deriv (by simp)
  exact h'

private theorem hasDerivAt_affine_one (alpha : ℝ) (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ (alpha : ℂ) + w) 1 z := by
  exact (hasDerivAt_id z).const_add (alpha : ℂ)

theorem hasDerivAt_wishartScalarLogDiff
    {alpha r : ℝ} {z : ℂ}
    (hr : (alpha : ℂ) + (r : ℂ) * z ∈ Complex.slitPlane)
    (h1 : (alpha : ℂ) + z ∈ Complex.slitPlane) :
    HasDerivAt (wishartScalarLogDiff alpha r)
      (wishartScalarLogDiffOne alpha r z) z := by
  exact ((hasDerivAt_affine_r alpha r z).clog hr).sub
    ((hasDerivAt_affine_one alpha z).clog h1)

theorem hasDerivAt_wishartScalarLogDiffOne
    {alpha r : ℝ} {z : ℂ}
    (hr0 : (alpha : ℂ) + (r : ℂ) * z ≠ 0)
    (h10 : (alpha : ℂ) + z ≠ 0) :
    HasDerivAt (wishartScalarLogDiffOne alpha r)
      (wishartScalarLogDiffTwo alpha r z) z := by
  have hR := hasDerivAt_affine_r alpha r z
  have hOne := hasDerivAt_affine_one alpha z
  have hleft := (hR.inv hr0).const_mul (r : ℂ)
  have hright := hOne.inv h10
  have hfun : wishartScalarLogDiffOne alpha r =
      (fun y ↦ (r : ℂ) * ((alpha : ℂ) + (r : ℂ) * y)⁻¹ -
        ((alpha : ℂ) + y)⁻¹) := by
    funext w
    simp [wishartScalarLogDiffOne, div_eq_mul_inv]
  rw [hfun]
  refine (hleft.sub hright).congr_deriv ?_
  unfold wishartScalarLogDiffTwo
  field_simp [hr0, h10]
  ring

theorem hasDerivAt_wishartScalarLogDiffTwo
    {alpha r : ℝ} {z : ℂ}
    (hr0 : (alpha : ℂ) + (r : ℂ) * z ≠ 0)
    (h10 : (alpha : ℂ) + z ≠ 0) :
    HasDerivAt (wishartScalarLogDiffTwo alpha r)
      (wishartScalarLogDiffThree alpha r z) z := by
  have hR := hasDerivAt_affine_r alpha r z
  have hOne := hasDerivAt_affine_one alpha z
  have hleft := ((hR.inv hr0).pow 2).const_mul (-((r : ℂ) ^ 2))
  have hright := (hOne.inv h10).pow 2
  have hfun : wishartScalarLogDiffTwo alpha r =
      (fun y ↦ -((r : ℂ) ^ 2) *
        (((alpha : ℂ) + (r : ℂ) * y)⁻¹) ^ 2 +
        (((alpha : ℂ) + y)⁻¹) ^ 2) := by
    funext w
    simp [wishartScalarLogDiffTwo, div_eq_mul_inv]
  rw [hfun]
  refine (hleft.add hright).congr_deriv ?_
  unfold wishartScalarLogDiffThree
  simp only [Pi.inv_apply]
  norm_num
  field_simp [hr0, h10]
  ring

/-- The scalar contribution to the non-null Wishart log transform. -/
def wishartScalarLogTerm (alpha r : ℝ) (z : ℂ) : ℂ :=
  -((alpha : ℂ) + z) * wishartScalarLogDiff alpha r z

def wishartScalarLogTermOne (alpha r : ℝ) (z : ℂ) : ℂ :=
  -(wishartScalarLogDiff alpha r z +
    ((alpha : ℂ) + z) * wishartScalarLogDiffOne alpha r z)

def wishartScalarLogTermTwo (alpha r : ℝ) (z : ℂ) : ℂ :=
  -(2 * wishartScalarLogDiffOne alpha r z +
    ((alpha : ℂ) + z) * wishartScalarLogDiffTwo alpha r z)

def wishartScalarLogTermThree (alpha r : ℝ) (z : ℂ) : ℂ :=
  -(3 * wishartScalarLogDiffTwo alpha r z +
    ((alpha : ℂ) + z) * wishartScalarLogDiffThree alpha r z)

theorem hasDerivAt_wishartScalarLogTerm
    {alpha r : ℝ} {z : ℂ}
    (hr : (alpha : ℂ) + (r : ℂ) * z ∈ Complex.slitPlane)
    (h1 : (alpha : ℂ) + z ∈ Complex.slitPlane) :
    HasDerivAt (wishartScalarLogTerm alpha r)
      (wishartScalarLogTermOne alpha r z) z := by
  have hg := hasDerivAt_affine_one alpha z
  have hl := hasDerivAt_wishartScalarLogDiff hr h1
  have hfun : wishartScalarLogTerm alpha r =
      -((fun w ↦ (alpha : ℂ) + w) * wishartScalarLogDiff alpha r) := by
    funext w
    simp [wishartScalarLogTerm]
    ring
  rw [hfun]
  refine (hg.mul hl).neg.congr_deriv ?_
  unfold wishartScalarLogTermOne
  ring

theorem hasDerivAt_wishartScalarLogTermOne
    {alpha r : ℝ} {z : ℂ}
    (hr : (alpha : ℂ) + (r : ℂ) * z ∈ Complex.slitPlane)
    (h1 : (alpha : ℂ) + z ∈ Complex.slitPlane) :
    HasDerivAt (wishartScalarLogTermOne alpha r)
      (wishartScalarLogTermTwo alpha r z) z := by
  have hr0 := Complex.slitPlane_ne_zero hr
  have h10 := Complex.slitPlane_ne_zero h1
  have hg := hasDerivAt_affine_one alpha z
  have hl := hasDerivAt_wishartScalarLogDiff hr h1
  have hl1 := hasDerivAt_wishartScalarLogDiffOne hr0 h10
  have hfun : wishartScalarLogTermOne alpha r =
      -(wishartScalarLogDiff alpha r +
        (fun w ↦ (alpha : ℂ) + w) * wishartScalarLogDiffOne alpha r) := by
    funext w
    rfl
  rw [hfun]
  refine (hl.add (hg.mul hl1)).neg.congr_deriv ?_
  unfold wishartScalarLogTermTwo
  ring

theorem hasDerivAt_wishartScalarLogTermTwo
    {alpha r : ℝ} {z : ℂ}
    (hr : (alpha : ℂ) + (r : ℂ) * z ∈ Complex.slitPlane)
    (h1 : (alpha : ℂ) + z ∈ Complex.slitPlane) :
    HasDerivAt (wishartScalarLogTermTwo alpha r)
      (wishartScalarLogTermThree alpha r z) z := by
  have hr0 := Complex.slitPlane_ne_zero hr
  have h10 := Complex.slitPlane_ne_zero h1
  have hg := hasDerivAt_affine_one alpha z
  have hl1 := hasDerivAt_wishartScalarLogDiffOne hr0 h10
  have hl2 := hasDerivAt_wishartScalarLogDiffTwo hr0 h10
  have hfun : wishartScalarLogTermTwo alpha r =
      -((fun y ↦ 2 * wishartScalarLogDiffOne alpha r y) +
        (fun w ↦ (alpha : ℂ) + w) * wishartScalarLogDiffTwo alpha r) := by
    funext w
    rfl
  rw [hfun]
  refine ((hl1.const_mul 2).add (hg.mul hl2)).neg.congr_deriv ?_
  unfold wishartScalarLogTermThree
  ring

/-- Positive real parts put both affine logarithm arguments in the slit
plane, uniformly on the imaginary axis. -/
theorem wishart_affine_imaginary_mem_slitPlane
    {alpha r u : ℝ} (halpha : 0 < alpha) (_hr : 0 < r) :
    (alpha : ℂ) + (r : ℂ) * ((u : ℂ) * Complex.I) ∈
      Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simpa using halpha

/-- Algebraic closed form of the third derivative, before restricting to the
imaginary axis.  Keeping the two affine denominators unexpanded is useful both
mathematically and to make the nonvanishing hypotheses explicit. -/
theorem wishartScalarLogTermThree_eq_closedForm
    {alpha r : ℝ} {z : ℂ}
    (hr0 : (alpha : ℂ) + (r : ℂ) * z ≠ 0)
    (h10 : (alpha : ℂ) + z ≠ 0) :
    wishartScalarLogTermThree alpha r z =
      -(3 * (alpha : ℂ) ^ 2 * ((r : ℂ) - 1) ^ 2) /
          (((alpha : ℂ) + z) ^ 2 *
            ((alpha : ℂ) + (r : ℂ) * z) ^ 2) -
        (2 * (alpha : ℂ) ^ 3 * ((r : ℂ) - 1) ^ 3) /
          (((alpha : ℂ) + z) ^ 2 *
            ((alpha : ℂ) + (r : ℂ) * z) ^ 3) := by
  unfold wishartScalarLogTermThree wishartScalarLogDiffTwo
    wishartScalarLogDiffThree
  field_simp [hr0, h10]
  ring

/-- The verified third derivative is exactly the rational expression used by
the global bound. -/
theorem wishartScalarLogTermThree_imaginary_eq_expression
    {alpha r u : ℝ} (halpha : 0 < alpha) (hr : 0 < r) :
    wishartScalarLogTermThree alpha r ((u : ℂ) * Complex.I) =
      wishartScalarThirdExpression alpha r (r - 1) u := by
  have hR0 : (alpha : ℂ) + (r : ℂ) * ((u : ℂ) * Complex.I) ≠ 0 :=
    Complex.slitPlane_ne_zero
      (wishart_affine_imaginary_mem_slitPlane halpha hr)
  have h10 : (alpha : ℂ) + ((u : ℂ) * Complex.I) ≠ 0 :=
    Complex.slitPlane_ne_zero (by
      simpa using (wishart_affine_imaginary_mem_slitPlane
        (r := (1 : ℝ)) (u := u) halpha (by norm_num)))
  rw [wishartScalarLogTermThree_eq_closedForm hR0 h10]
  unfold wishartScalarThirdExpression
  push_cast
  ring

end

end LogdetLean
