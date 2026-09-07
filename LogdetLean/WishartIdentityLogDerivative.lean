import LogdetLean.ComplexDigammaSeries
import LogdetLean.WishartComplexTransform
import LogdetLean.GeneralRLeadingVarianceAlgebra
import Mathlib.Tactic

/-!
# The branch-free logarithmic derivative of the identity Wishart transform

The Gamma function has no zeros, but choosing a global complex logarithm of
Gamma is unnecessary.  This file instead differentiates the logarithm only
through its single-valued logarithmic derivative `Complex.digamma`.

The finite expression below is the logarithmic derivative of
`complexWishartIdentityTransform`.  It is written in the beta-difference
coordinates of Zhao, arXiv:2608.00565v1, Lemma 5.4, so its second derivative
is literally the cancellation-preserving series `wishartIdentityThirdAxis`.
The complex polygamma identities used in the differentiation were proved
from DLMF 5.15.1 in `ComplexDigammaSeries`.
-/

namespace LogdetLean

noncomputable section

open Complex Set
open scoped BigOperators

/-- Logarithmic derivative of the identity-correlation Wishart transform.
The first finite sum separates the `p-1` beta ratios from their common total
shape; the last term contains the radial Gamma factor. -/
def wishartIdentityLogDerivative (m p : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc 2 p,
      (Complex.digamma ((betaShapeA m j : ℂ) + z) -
        Complex.digamma ((betaShapeTotal m : ℂ) + z)) +
    (p : ℂ) *
      (Complex.digamma ((betaShapeTotal m : ℂ) + z) +
        (Real.log m : ℂ) - Complex.log ((betaShapeTotal m : ℂ) + z) - 1)

/-- First derivative of `wishartIdentityLogDerivative`. -/
def wishartIdentityLogDerivativeOne (m p : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc 2 p,
      (complexTrigammaSeries ((betaShapeA m j : ℂ) + z) -
        complexTrigammaSeries ((betaShapeTotal m : ℂ) + z)) +
    (p : ℂ) *
      (complexTrigammaSeries ((betaShapeTotal m : ℂ) + z) -
        (((betaShapeTotal m : ℂ) + z)⁻¹))

/-- Second derivative of `wishartIdentityLogDerivative`. -/
def wishartIdentityLogDerivativeTwo (m p : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc 2 p,
      (-complexNegPsiTwoSeries ((betaShapeA m j : ℂ) + z) +
        complexNegPsiTwoSeries ((betaShapeTotal m : ℂ) + z)) +
    (p : ℂ) *
      (-complexNegPsiTwoSeries ((betaShapeTotal m : ℂ) + z) +
        (((betaShapeTotal m : ℂ) + z)⁻¹) ^ 2)

private theorem positive_real_axis_mem_slitPlane {x : ℝ} (hx : 0 < x)
    (u : ℝ) :
    (x : ℂ) + (u : ℂ) * Complex.I ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simpa using hx

/-- First verified differentiation on every vertical line through the
positive half-plane. -/
theorem hasDerivAt_wishartIdentityLogDerivative_axis
    {m p : ℕ} (h : Admissible m p) (u : ℝ) :
    HasDerivAt (wishartIdentityLogDerivative m p)
      (wishartIdentityLogDerivativeOne m p ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
  have hM : 0 < betaShapeTotal m := betaShapeTotal_pos h
  have hMre : 0 < (((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I).re) := by
    simpa using hM
  have hsum : HasDerivAt
      (fun z : ℂ ↦ ∑ j ∈ Finset.Icc 2 p,
        (Complex.digamma ((betaShapeA m j : ℂ) + z) -
          Complex.digamma ((betaShapeTotal m : ℂ) + z)))
      (∑ j ∈ Finset.Icc 2 p,
        (complexTrigammaSeries
            ((betaShapeA m j : ℂ) + (u : ℂ) * Complex.I) -
          complexTrigammaSeries
            ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)))
      ((u : ℂ) * Complex.I) := by
    apply HasDerivAt.fun_sum
    intro j hj
    have haj := betaShapeA_pos_of_mem_Icc h.2 hj
    have hshiftA : HasDerivAt
        (fun z : ℂ ↦ (betaShapeA m j : ℂ) + z) 1
        ((u : ℂ) * Complex.I) :=
      (hasDerivAt_id ((u : ℂ) * Complex.I)).const_add
        (betaShapeA m j : ℂ)
    have hshiftM : HasDerivAt
        (fun z : ℂ ↦ (betaShapeTotal m : ℂ) + z) 1
        ((u : ℂ) * Complex.I) :=
      (hasDerivAt_id ((u : ℂ) * Complex.I)).const_add
        (betaShapeTotal m : ℂ)
    change HasDerivAt
      ((fun z : ℂ ↦ Complex.digamma ((betaShapeA m j : ℂ) + z)) -
        (fun z : ℂ ↦ Complex.digamma ((betaShapeTotal m : ℂ) + z)))
      _ _
    have hA := (hasDerivAt_complex_digamma (by simpa using haj)).comp
      ((u : ℂ) * Complex.I) hshiftA
    have hT := (hasDerivAt_complex_digamma hMre).comp
      ((u : ℂ) * Complex.I) hshiftM
    have hraw := (hA.sub hT).congr_deriv (show
      complexTrigammaSeries
          ((betaShapeA m j : ℂ) + (u : ℂ) * Complex.I) * 1 -
        complexTrigammaSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) * 1 =
        complexTrigammaSeries
          ((betaShapeA m j : ℂ) + (u : ℂ) * Complex.I) -
        complexTrigammaSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) by ring)
    exact hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _z ↦ rfl)
  have hshiftM : HasDerivAt
      (fun z : ℂ ↦ (betaShapeTotal m : ℂ) + z) 1
      ((u : ℂ) * Complex.I) :=
    (hasDerivAt_id ((u : ℂ) * Complex.I)).const_add
      (betaShapeTotal m : ℂ)
  have htotal : HasDerivAt
      (fun z : ℂ ↦ Complex.digamma ((betaShapeTotal m : ℂ) + z))
      (complexTrigammaSeries
        ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
    change HasDerivAt
      (Complex.digamma ∘ (fun z : ℂ ↦ (betaShapeTotal m : ℂ) + z)) _ _
    have hraw := (hasDerivAt_complex_digamma hMre).comp
      ((u : ℂ) * Complex.I) hshiftM
    have hraw' := hraw.congr_deriv (show
      complexTrigammaSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) * 1 =
        complexTrigammaSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) by ring)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _z ↦ rfl)
  have hlog :=
    hshiftM.clog (positive_real_axis_mem_slitPlane hM u)
  have hradial : HasDerivAt
      (fun z : ℂ ↦ Complex.digamma ((betaShapeTotal m : ℂ) + z) +
        (Real.log m : ℂ) - Complex.log ((betaShapeTotal m : ℂ) + z) - 1)
      (complexTrigammaSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) -
        (((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)⁻¹))
      ((u : ℂ) * Complex.I) := by
    change HasDerivAt
      ((((fun z : ℂ ↦ Complex.digamma ((betaShapeTotal m : ℂ) + z)) +
        (fun _ : ℂ ↦ (Real.log m : ℂ))) -
        (fun z : ℂ ↦ Complex.log ((betaShapeTotal m : ℂ) + z))) -
        (fun _ : ℂ ↦ 1)) _ _
    have hraw := ((htotal.add_const (Real.log m : ℂ)).sub hlog).sub_const 1
    have hraw' := hraw.congr_deriv (show
      complexTrigammaSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) -
          1 / ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) =
        complexTrigammaSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) -
          (((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)⁻¹) by
      rw [one_div])
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _z ↦ rfl)
  unfold wishartIdentityLogDerivative wishartIdentityLogDerivativeOne
  change HasDerivAt
    ((fun z : ℂ ↦ ∑ j ∈ Finset.Icc 2 p,
      (Complex.digamma ((betaShapeA m j : ℂ) + z) -
        Complex.digamma ((betaShapeTotal m : ℂ) + z))) +
      (fun z : ℂ ↦ (p : ℂ) *
        (Complex.digamma ((betaShapeTotal m : ℂ) + z) +
          (Real.log m : ℂ) - Complex.log ((betaShapeTotal m : ℂ) + z) - 1)))
    _ _
  exact hsum.add (hradial.const_mul (p : ℂ))

/-- Second verified differentiation on the imaginary axis. -/
theorem hasDerivAt_wishartIdentityLogDerivativeOne_axis
    {m p : ℕ} (h : Admissible m p) (u : ℝ) :
    HasDerivAt (wishartIdentityLogDerivativeOne m p)
      (wishartIdentityLogDerivativeTwo m p ((u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
  have hM : 0 < betaShapeTotal m := betaShapeTotal_pos h
  have hsum : HasDerivAt
      (fun z : ℂ ↦ ∑ j ∈ Finset.Icc 2 p,
        (complexTrigammaSeries ((betaShapeA m j : ℂ) + z) -
          complexTrigammaSeries ((betaShapeTotal m : ℂ) + z)))
      (∑ j ∈ Finset.Icc 2 p,
        (-complexNegPsiTwoSeries
            ((betaShapeA m j : ℂ) + (u : ℂ) * Complex.I) +
          complexNegPsiTwoSeries
            ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)))
      ((u : ℂ) * Complex.I) := by
    apply HasDerivAt.fun_sum
    intro j hj
    have haj := betaShapeA_pos_of_mem_Icc h.2 hj
    have hshiftA : HasDerivAt
        (fun z : ℂ ↦ (betaShapeA m j : ℂ) + z) 1
        ((u : ℂ) * Complex.I) :=
      (hasDerivAt_id ((u : ℂ) * Complex.I)).const_add
        (betaShapeA m j : ℂ)
    have hshiftM : HasDerivAt
        (fun z : ℂ ↦ (betaShapeTotal m : ℂ) + z) 1
        ((u : ℂ) * Complex.I) :=
      (hasDerivAt_id ((u : ℂ) * Complex.I)).const_add
        (betaShapeTotal m : ℂ)
    change HasDerivAt
      ((fun z : ℂ ↦ complexTrigammaSeries ((betaShapeA m j : ℂ) + z)) -
        (fun z : ℂ ↦ complexTrigammaSeries ((betaShapeTotal m : ℂ) + z)))
      _ _
    have hA := (hasDerivAt_complexTrigammaSeries (by simpa using haj)).comp
      ((u : ℂ) * Complex.I) hshiftA
    have hT := (hasDerivAt_complexTrigammaSeries (by simpa using hM)).comp
      ((u : ℂ) * Complex.I) hshiftM
    have hraw := (hA.sub hT).congr_deriv (show
      (-complexNegPsiTwoSeries
          ((betaShapeA m j : ℂ) + (u : ℂ) * Complex.I)) * 1 -
        (-complexNegPsiTwoSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)) * 1 =
        -complexNegPsiTwoSeries
          ((betaShapeA m j : ℂ) + (u : ℂ) * Complex.I) +
        complexNegPsiTwoSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) by ring)
    exact hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _z ↦ rfl)
  have hshiftM : HasDerivAt
      (fun z : ℂ ↦ (betaShapeTotal m : ℂ) + z) 1
      ((u : ℂ) * Complex.I) :=
    (hasDerivAt_id ((u : ℂ) * Complex.I)).const_add
      (betaShapeTotal m : ℂ)
  have htrig : HasDerivAt
      (fun z : ℂ ↦ complexTrigammaSeries ((betaShapeTotal m : ℂ) + z))
      (-complexNegPsiTwoSeries
        ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I))
      ((u : ℂ) * Complex.I) := by
    change HasDerivAt
      (complexTrigammaSeries ∘
        (fun z : ℂ ↦ (betaShapeTotal m : ℂ) + z)) _ _
    have hraw := (hasDerivAt_complexTrigammaSeries (by simpa using hM)).comp
      ((u : ℂ) * Complex.I) hshiftM
    have hraw' := hraw.congr_deriv (show
      (-complexNegPsiTwoSeries
        ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)) * 1 =
      -complexNegPsiTwoSeries
        ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) by ring)
    exact hraw'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _z ↦ rfl)
  have hinv :=
    (hshiftM.inv
        (Complex.slitPlane_ne_zero (positive_real_axis_mem_slitPlane hM u)))
  have hradial : HasDerivAt
      (fun z : ℂ ↦ complexTrigammaSeries ((betaShapeTotal m : ℂ) + z) -
        (((betaShapeTotal m : ℂ) + z)⁻¹))
      (-complexNegPsiTwoSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) +
        (((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2)
      ((u : ℂ) * Complex.I) := by
    change HasDerivAt
      ((fun z : ℂ ↦ complexTrigammaSeries ((betaShapeTotal m : ℂ) + z)) -
        (fun z : ℂ ↦ ((betaShapeTotal m : ℂ) + z)⁻¹)) _ _
    have hraw := (htrig.sub hinv).congr_deriv (show
      -complexNegPsiTwoSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) -
          (-1 / (((betaShapeTotal m : ℂ) +
            (u : ℂ) * Complex.I) ^ 2)) =
        -complexNegPsiTwoSeries
          ((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I) +
          (((betaShapeTotal m : ℂ) + (u : ℂ) * Complex.I)⁻¹) ^ 2 by
      rw [neg_div, one_div, ← inv_pow]
      ring)
    exact hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _z ↦ rfl)
  unfold wishartIdentityLogDerivativeOne wishartIdentityLogDerivativeTwo
  change HasDerivAt
    ((fun z : ℂ ↦ ∑ j ∈ Finset.Icc 2 p,
      (complexTrigammaSeries ((betaShapeA m j : ℂ) + z) -
        complexTrigammaSeries ((betaShapeTotal m : ℂ) + z))) +
      (fun z : ℂ ↦ (p : ℂ) *
        (complexTrigammaSeries ((betaShapeTotal m : ℂ) + z) -
          (((betaShapeTotal m : ℂ) + z)⁻¹)))) _ _
  exact hsum.add (hradial.const_mul (p : ℂ))

/-- On the imaginary axis the second logarithmic derivative is exactly the
cancellation-preserving identity series used by the global envelope. -/
theorem wishartIdentityLogDerivativeTwo_axis
    (m p : ℕ) (u : ℝ) :
    wishartIdentityLogDerivativeTwo m p ((u : ℂ) * Complex.I) =
      wishartIdentityThirdAxis m p u := by
  unfold wishartIdentityLogDerivativeTwo wishartIdentityThirdAxis
  simp_rw [complexNegPsiTwoSeries_axis]

/-- The identity first logarithmic derivative at zero is exactly the null
variance plus the radial trigamma correction. -/
theorem wishartIdentityLogDerivativeOne_zero
    {m p : ℕ} (h : Admissible m p) :
    wishartIdentityLogDerivativeOne m p 0 =
      ((nullVSeries m p + (p : ℝ) *
        (trigammaSeries (betaShapeTotal m) - 2 / (m : ℝ)) : ℝ) : ℂ) := by
  have hM : 0 < betaShapeTotal m := betaShapeTotal_pos h
  have hsumCast :
      (∑ j ∈ Finset.Icc 2 p,
        complexTrigammaSeries (betaShapeA m j : ℂ)) =
        ((∑ j ∈ Finset.Icc 2 p,
          trigammaSeries (betaShapeA m j) : ℝ) : ℂ) := by
    push_cast
    apply Finset.sum_congr rfl
    intro j hj
    rw [complexTrigammaSeries_ofReal
      (betaShapeA_pos_of_mem_Icc h.2 hj)]
  unfold wishartIdentityLogDerivativeOne nullVSeries
  simp only [add_zero]
  simp_rw [Finset.sum_sub_distrib]
  simp_rw [hsumCast, complexTrigammaSeries_ofReal hM]
  push_cast
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hmNat : 0 < m := by omega
  have hm : (m : ℝ) ≠ 0 := by
    exact_mod_cast hmNat.ne'
  unfold betaShapeTotal
  simp only [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
  have hcard : p + 1 - 2 = p - 1 := by omega
  rw [hcard]
  push_cast
  field_simp [hm]

end

end LogdetLean
