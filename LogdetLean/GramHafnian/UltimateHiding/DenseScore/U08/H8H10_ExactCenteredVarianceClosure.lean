import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10_ExactTraceRecurrenceAdapter
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10_ExactCenteredVarianceReduction
import Mathlib.Tactic

/-!
# All-dimensional exact H8/H10 centered-variance closure

This module rewrites the two denominator centered variances into the exact
ten-moment scalar forms, applies the recurrence solver, and closes the literal
H8 and H10 packages in every dimension in their stated range.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.Wishart
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 3600000
set_option maxRecDepth 100000

private theorem integral_five_linear_combination_h8h10
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    (f1 f2 f3 f4 f5 : X → ℝ) (a1 a2 a3 a4 a5 : ℝ)
    (h1 : Integrable f1 mu) (h2 : Integrable f2 mu)
    (h3 : Integrable f3 mu) (h4 : Integrable f4 mu)
    (h5 : Integrable f5 mu) :
    (∫ x, a1 * f1 x + a2 * f2 x + a3 * f3 x + a4 * f4 x + a5 * f5 x ∂mu) =
      a1 * (∫ x, f1 x ∂mu) + a2 * (∫ x, f2 x ∂mu) +
        a3 * (∫ x, f3 x ∂mu) + a4 * (∫ x, f4 x ∂mu) +
        a5 * (∫ x, f5 x ∂mu) := by
  have h1' := h1.const_mul a1
  have h2' := h2.const_mul a2
  have h3' := h3.const_mul a3
  have h4' := h4.const_mul a4
  have h5' := h5.const_mul a5
  have hs2 :
      (∫ x, a1 * f1 x + a2 * f2 x ∂mu) =
        (∫ x, a1 * f1 x ∂mu) + ∫ x, a2 * f2 x ∂mu := by
    simpa only [Pi.add_apply] using integral_add h1' h2'
  have hs3 :
      (∫ x, a1 * f1 x + a2 * f2 x + a3 * f3 x ∂mu) =
        (∫ x, a1 * f1 x + a2 * f2 x ∂mu) +
          ∫ x, a3 * f3 x ∂mu := by
    simpa only [Pi.add_apply] using integral_add (h1'.add h2') h3'
  have hs4 :
      (∫ x, a1 * f1 x + a2 * f2 x + a3 * f3 x + a4 * f4 x ∂mu) =
        (∫ x, a1 * f1 x + a2 * f2 x + a3 * f3 x ∂mu) +
          ∫ x, a4 * f4 x ∂mu := by
    simpa only [Pi.add_apply] using
      integral_add ((h1'.add h2').add h3') h4'
  have hs5 :
      (∫ x, a1 * f1 x + a2 * f2 x + a3 * f3 x + a4 * f4 x + a5 * f5 x ∂mu) =
        (∫ x, a1 * f1 x + a2 * f2 x + a3 * f3 x + a4 * f4 x ∂mu) +
          ∫ x, a5 * f5 x ∂mu := by
    simpa only [Pi.add_apply] using
      integral_add (((h1'.add h2').add h3').add h4') h5'
  rw [hs5, hs4, hs3, hs2]
  simp only [integral_const_mul]

/-! ## Exact raw-moment expansions -/

theorem h8DenominatorSecondRawMoment_eq_traceMoments_internal
    (N K : ℕ) :
    h8DenominatorSecondRawMoment N K =
      ((N : ℝ) + 1) ^ 2 * h8H10TraceOneSqMoment N K +
        2 * ((N : ℝ) + 1) * h8H10TraceTwoMoment N K := by
  unfold h8DenominatorSecondRawMoment h8H10TraceOneSqMoment
    h8H10TraceTwoMoment
  rw [h9InverseWishartDenominatorLaw_eq_u08StandardGaussian]
  simp_rw [h9ScaledInverseWishart_eq_u08ScaledInverseWishartMatrix]
  simp only [Nat.cast_add, Nat.cast_one]

theorem h10DenominatorFirstRawMoment_eq_traceMoments_internal
    (N K : ℕ) :
    h10DenominatorFirstRawMoment N K =
      ((N : ℝ) + 1) * ((N : ℝ) + 2) * h8H10TraceTwoMoment N K +
        ((N : ℝ) + 1) * h8H10TraceOneSqMoment N K := by
  unfold h10DenominatorFirstRawMoment h8H10TraceOneSqMoment
    h8H10TraceTwoMoment
  rw [h9InverseWishartDenominatorLaw_eq_u08StandardGaussian]
  simp_rw [h9ScaledInverseWishart_eq_u08ScaledInverseWishartMatrix]
  simp only [Nat.cast_add, Nat.cast_one]
  norm_num

theorem h8DenominatorFourthRawMoment_eq_traceMoments_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    h8DenominatorFourthRawMoment N K =
      ((N : ℝ) + 1) ^ 4 * h8H10TraceOneFourthMoment N K +
        12 * ((N : ℝ) + 1) ^ 3 * h8H10TraceOneSqTraceTwoMoment N K +
        12 * ((N : ℝ) + 1) ^ 2 * h8H10TraceTwoSqMoment N K +
        32 * ((N : ℝ) + 1) ^ 2 * h8H10TraceOneTraceThreeMoment N K +
        48 * ((N : ℝ) + 1) * h8H10TraceFourMoment N K := by
  let mu := standardRealGaussianMatrixMeasure (K - N) N
  let D := scaledInverseWishartMatrix N K
  have L := h8H10_scaledInverseFourthTraceMomentLedger_internal N K hN hdense
  have hlin := integral_five_linear_combination_h8h10
    (mu := mu)
    (fun B ↦ Matrix.trace (D B) ^ 4)
    (fun B ↦ Matrix.trace (D B) ^ 2 * Matrix.trace ((D B) ^ 2))
    (fun B ↦ Matrix.trace ((D B) ^ 2) ^ 2)
    (fun B ↦ Matrix.trace (D B) * Matrix.trace ((D B) ^ 3))
    (fun B ↦ Matrix.trace ((D B) ^ 4))
    (((N : ℝ) + 1) ^ 4)
    (12 * ((N : ℝ) + 1) ^ 3)
    (12 * ((N : ℝ) + 1) ^ 2)
    (32 * ((N : ℝ) + 1) ^ 2)
    (48 * ((N : ℝ) + 1))
    (by simpa only [D, mu] using L.traceOneFourth_integrable)
    (by simpa only [D, mu] using L.traceOneSqTraceTwo_integrable)
    (by simpa only [D, mu] using L.traceTwoSquare_integrable)
    (by simpa only [D, mu] using L.traceOneTraceThree_integrable)
    (by simpa only [D, mu] using L.traceFour_integrable)
  unfold h8DenominatorFourthRawMoment h14TraceOneFourthWickPolynomial
  simp only [Nat.cast_add, Nat.cast_one] at ⊢
  simp only [D, mu] at hlin
  unfold h8H10TraceOneFourthMoment h8H10TraceOneSqTraceTwoMoment
    h8H10TraceTwoSqMoment h8H10TraceOneTraceThreeMoment h8H10TraceFourMoment
  rw [h9InverseWishartDenominatorLaw_eq_u08StandardGaussian]
  simp_rw [h9ScaledInverseWishart_eq_u08ScaledInverseWishartMatrix]
  ring_nf at hlin ⊢
  exact hlin

theorem h10DenominatorSecondRawMoment_eq_traceMoments_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    h10DenominatorSecondRawMoment N K =
      ((N : ℝ) + 1) ^ 2 * h8H10TraceOneFourthMoment N K +
        (2 * ((N : ℝ) + 1) ^ 3 + 2 * ((N : ℝ) + 1) ^ 2 +
          8 * ((N : ℝ) + 1)) * h8H10TraceOneSqTraceTwoMoment N K +
        (((N : ℝ) + 1) ^ 4 + 2 * ((N : ℝ) + 1) ^ 3 +
          5 * ((N : ℝ) + 1) ^ 2 + 4 * ((N : ℝ) + 1)) *
            h8H10TraceTwoSqMoment N K +
        16 * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
          h8H10TraceOneTraceThreeMoment N K +
        (8 * ((N : ℝ) + 1) ^ 3 + 20 * ((N : ℝ) + 1) ^ 2 +
          20 * ((N : ℝ) + 1)) * h8H10TraceFourMoment N K := by
  let mu := standardRealGaussianMatrixMeasure (K - N) N
  let D := scaledInverseWishartMatrix N K
  have L := h8H10_scaledInverseFourthTraceMomentLedger_internal N K hN hdense
  have hlin := integral_five_linear_combination_h8h10
    (mu := mu)
    (fun B ↦ Matrix.trace (D B) ^ 4)
    (fun B ↦ Matrix.trace (D B) ^ 2 * Matrix.trace ((D B) ^ 2))
    (fun B ↦ Matrix.trace ((D B) ^ 2) ^ 2)
    (fun B ↦ Matrix.trace (D B) * Matrix.trace ((D B) ^ 3))
    (fun B ↦ Matrix.trace ((D B) ^ 4))
    (((N : ℝ) + 1) ^ 2)
    (2 * ((N : ℝ) + 1) ^ 3 + 2 * ((N : ℝ) + 1) ^ 2 +
      8 * ((N : ℝ) + 1))
    (((N : ℝ) + 1) ^ 4 + 2 * ((N : ℝ) + 1) ^ 3 +
      5 * ((N : ℝ) + 1) ^ 2 + 4 * ((N : ℝ) + 1))
    (16 * ((N : ℝ) + 1) * ((N : ℝ) + 2))
    (8 * ((N : ℝ) + 1) ^ 3 + 20 * ((N : ℝ) + 1) ^ 2 +
      20 * ((N : ℝ) + 1))
    (by simpa only [D, mu] using L.traceOneFourth_integrable)
    (by simpa only [D, mu] using L.traceOneSqTraceTwo_integrable)
    (by simpa only [D, mu] using L.traceTwoSquare_integrable)
    (by simpa only [D, mu] using L.traceOneTraceThree_integrable)
    (by simpa only [D, mu] using L.traceFour_integrable)
  unfold h10DenominatorSecondRawMoment h14TraceTwoSquareWickPolynomial
  simp only [Nat.cast_add, Nat.cast_one] at ⊢
  simp only [D, mu] at hlin
  unfold h8H10TraceOneFourthMoment h8H10TraceOneSqTraceTwoMoment
    h8H10TraceTwoSqMoment h8H10TraceOneTraceThreeMoment h8H10TraceFourMoment
  rw [h9InverseWishartDenominatorLaw_eq_u08StandardGaussian]
  simp_rw [h9ScaledInverseWishart_eq_u08ScaledInverseWishartMatrix]
  ring_nf at hlin ⊢
  exact hlin

/-! ## Exact centered-variance rewrites -/

theorem h8DenominatorCenteredVariance_eq_traceRecurrence_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    h8DenominatorCenteredVariance N K =
      h8TraceRecurrenceVariance (N : ℝ)
        (h8H10TraceOneSqMoment N K)
        (h8H10TraceTwoMoment N K)
        (h8H10TraceOneFourthMoment N K)
        (h8H10TraceOneSqTraceTwoMoment N K)
        (h8H10TraceTwoSqMoment N K)
        (h8H10TraceOneTraceThreeMoment N K)
        (h8H10TraceFourMoment N K) := by
  unfold h8DenominatorCenteredVariance h8TraceRecurrenceVariance
  rw [h8DenominatorFourthRawMoment_eq_traceMoments_internal hN hdense,
    h8DenominatorSecondRawMoment_eq_traceMoments_internal]

theorem h10DenominatorCenteredVariance_eq_traceRecurrence_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    h10DenominatorCenteredVariance N K =
      h10TraceRecurrenceVariance (N : ℝ)
        (h8H10TraceOneSqMoment N K)
        (h8H10TraceTwoMoment N K)
        (h8H10TraceOneFourthMoment N K)
        (h8H10TraceOneSqTraceTwoMoment N K)
        (h8H10TraceTwoSqMoment N K)
        (h8H10TraceOneTraceThreeMoment N K)
        (h8H10TraceFourMoment N K) := by
  unfold h10DenominatorCenteredVariance h10TraceRecurrenceVariance
  rw [h10DenominatorSecondRawMoment_eq_traceMoments_internal hN hdense,
    h10DenominatorFirstRawMoment_eq_traceMoments_internal]

/-! ## Dense all-dimensional bounds -/

private theorem concreteCOEExponent_dense_lower_h8h10
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    13 * (N : ℝ) ≤ concreteCOEExponent N K := by
  have hdenseR : 16 * (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdense
  unfold concreteCOEExponent
  nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]

theorem h8DenominatorCenteredVariance_le_twoPow40_sq_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    h8DenominatorCenteredVariance N K ≤
      ((2 : ℝ) ^ 40 * (N : ℝ) ^ 3) ^ 2 := by
  rw [h8DenominatorCenteredVariance_eq_traceRecurrence_internal hN hdense]
  exact h8_traceRecurrenceVariance_le_twoPow40_sq_dense
    (h8H10ExactTraceRecurrenceSystem_internal hN hdense)
    (by exact_mod_cast hN)
    (concreteCOEExponent_dense_lower_h8h10 hN hdense)

theorem h10DenominatorCenteredVariance_le_twoPow40_sq_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    h10DenominatorCenteredVariance N K ≤
      ((2 : ℝ) ^ 40 * (N : ℝ) ^ 2) ^ 2 := by
  rw [h10DenominatorCenteredVariance_eq_traceRecurrence_internal hN hdense]
  exact h10_traceRecurrenceVariance_le_twoPow40_sq_dense
    (h8H10ExactTraceRecurrenceSystem_internal hN hdense)
    (by exact_mod_cast hN)
    (concreteCOEExponent_dense_lower_h8h10 hN hdense)

theorem h8SharpCenteredVariance_internal
    {N K : ℕ} (hN : 1 ≤ N) : H8SharpCenteredVarianceContract N K := by
  intro hdense
  have h := h8DenominatorCenteredVariance_le_twoPow40_sq_internal hN hdense
  norm_num [denseClassicalMomentConstant] at h ⊢
  exact h

theorem h10SharpCenteredVariance_internal
    {N K : ℕ} (hN : 1 ≤ N) : H10SharpCenteredVarianceContract N K := by
  intro hdense
  have h := h10DenominatorCenteredVariance_le_twoPow40_sq_internal hN hdense
  norm_num [denseClassicalMomentConstant] at h ⊢
  exact h

/-- The exact two-endpoint fourth-moment transport, with no dimension
ceiling. -/
theorem h8H10ExactFourthMomentTransport_internal
    {N K : ℕ} (hN : 1 ≤ N) : H8H10ExactFourthMomentTransport N K :=
  h8H10ExactFourthMomentTransport_of_sharpCenteredVariance
    (h8SharpCenteredVariance_internal hN)
    (h10SharpCenteredVariance_internal hN)

/-- Literal H8 moment package in every dimension in the stated range. -/
theorem betaPrimeYTraceOneSquare_centered_two_momentPackage_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
        (fun u ↦ betaPrimeYTraceOne N K u ^ 2 -
          ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm
            (fun u ↦ betaPrimeYTraceOne N K u ^ 2 -
              ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
            2 (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ) ^ 3) :=
  betaPrimeYTraceOneSquare_centered_two_momentPackage_of_sharpVariance
    hN hgap (h8SharpCenteredVariance_internal hN)

/-- Literal H10 moment package in every dimension in the stated range. -/
theorem betaPrimeYTraceTwo_centered_two_momentPackage_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
        (fun u ↦ betaPrimeYTraceTwo N K u -
          ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm
            (fun u ↦ betaPrimeYTraceTwo N K u -
              ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
            2 (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ) ^ 2) :=
  betaPrimeYTraceTwo_centered_two_momentPackage_of_sharpVariance
    hN hgap (h10SharpCenteredVariance_internal hN)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
