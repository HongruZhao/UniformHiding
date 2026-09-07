import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Scalar core of the finite sparse Haar block estimate

This file formalizes the deterministic logarithmic inequality used after the
exact Haar block density and matrix beta differentiation have reduced the
Kullback Leibler divergence to a finite scalar sum.

There are no probabilistic assumptions in this file.  In particular, the
matrix beta integral and the identification of the Haar likelihood ratio are
kept separate from the scalar estimate proved here.
-/

open scoped BigOperators

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

/-- The scalar summand in the exact finite Haar block KL formula. -/
noncomputable def klSummand (h x : ℝ) : ℝ :=
  Real.log (1 - x) + (h - x) / (1 - x)

/-- The pointwise inequality behind the finite sparse KL estimate.

The proof uses only `log y ≤ y - 1`.  It is stronger than the power series
argument because the omitted remainder is exactly controlled by
`(1 - h) * x^2 ≥ 0`.
-/
theorem klSummand_le_linear {h x : ℝ}
    (hx1 : x < 1) (hh : h ≤ 1) :
    klSummand h x ≤ h + (h - 2) * x := by
  have hden : 0 < 1 - x := sub_pos.mpr hx1
  have hlog : Real.log (1 - x) ≤ -x := by
    have h := Real.log_le_sub_one_of_pos hden
    linarith
  have hquad : 0 ≤ (1 - h) * x ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg x)
  have hrat : -x + (h - x) / (1 - x) ≤ h + (h - 2) * x := by
    have hfrac :
        (h - x) / (1 - x) ≤ h + (h - 2) * x + x := by
      rw [div_le_iff₀ hden]
      nlinarith
    linarith
  unfold klSummand
  linarith

/-- Summing the pointwise estimate and using the exact first moment gives the
quadratic KL bound. -/
theorem sum_klSummand_le_half_card_mul_sq
    {ι : Type*} [Fintype ι] (x : ι → ℝ) (h : ℝ)
    (hx1 : ∀ i, x i < 1) (hh : h ≤ 1)
    (hsum : ∑ i, x i = (Fintype.card ι : ℝ) * h / 2) :
    ∑ i, klSummand h (x i) ≤ (Fintype.card ι : ℝ) * h ^ 2 / 2 := by
  calc
    ∑ i, klSummand h (x i)
        ≤ ∑ i, (h + (h - 2) * x i) := by
            exact Finset.sum_le_sum fun i _ ↦
              klSummand_le_linear (hx1 i) hh
    _ = (Fintype.card ι : ℝ) * h + (h - 2) * ∑ i, x i := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (Fintype.card ι : ℝ) * h ^ 2 / 2 := by
          rw [hsum]
          ring

/-- Abstract finite form of the Haar block scalar KL bound.

The hypotheses are precisely the output of the exact density calculation:
there are `p*q` summands, each normalized index lies in `[0,1)`, and their
sum is `p*q*(p+q)/(2*M)`.
-/
theorem finite_sparse_scalar_kl_bound
    {ι : Type*} [Fintype ι]
    (p q M : ℝ) (x : ι → ℝ)
    (hcard : (Fintype.card ι : ℝ) = p * q)
    (hM : 0 < M) (hs : p + q ≤ M)
    (hx1 : ∀ i, x i < 1)
    (hsum : ∑ i, x i = p * q * ((p + q) / M) / 2) :
    ∑ i, klSummand ((p + q) / M) (x i)
      ≤ p * q * (p + q) ^ 2 / (2 * M ^ 2) := by
  have hh : (p + q) / M ≤ 1 := (div_le_one hM).mpr hs
  have hsum' :
      ∑ i, x i = (Fintype.card ι : ℝ) * ((p + q) / M) / 2 := by
    rw [hcard]
    exact hsum
  have hmain := sum_klSummand_le_half_card_mul_sq x ((p + q) / M)
    hx1 hh hsum'
  rw [hcard] at hmain
  calc
    ∑ i, klSummand ((p + q) / M) (x i)
        ≤ p * q * ((p + q) / M) ^ 2 / 2 := hmain
    _ = p * q * (p + q) ^ 2 / (2 * M ^ 2) := by
          field_simp

end LogdetLean.GramHafnian.UltimateHiding.Sparse
