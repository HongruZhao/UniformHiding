import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H12_RawFourthExactRecurrenceAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10_ExactCenteredVarianceClosure
import Mathlib.Tactic

/-!
# Exact `1218` Gaussian-source fourth bounds

This module instantiates the foundations-only raw recurrence certificate with
the concrete inverse-Wishart denominator moments and transports it through
the already checked finite Gaussian Wick formula.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.DenseScore

def h12RawGaussianSourceFourthConstant : ℝ := 1218

theorem h12RawGaussianSourceFourthConstant_eq :
    h12RawGaussianSourceFourthConstant = 1218 := rfl

def h12RawTraceOneFourthConstantTwoPlus : ℝ := 34
def h12RawTraceTwoSquareConstantTwoPlus : ℝ := 88
def h12RawTraceOneSquareMeanConstantTwoPlus : ℝ := 4
def h12RawTraceTwoMeanConstantTwoPlus : ℝ := 5
def h12ProjectiveTraceTwoSquareConstantTwoPlus : ℝ := 22
def h12CompleteProjectiveFourthConstantTwoPlus : ℝ := 3151

theorem h12RawTraceOneFourthConstantTwoPlus_eq :
    h12RawTraceOneFourthConstantTwoPlus = 34 := rfl

theorem h12RawTraceTwoSquareConstantTwoPlus_eq :
    h12RawTraceTwoSquareConstantTwoPlus = 88 := rfl

theorem h12RawTraceOneSquareMeanConstantTwoPlus_eq :
    h12RawTraceOneSquareMeanConstantTwoPlus = 4 := rfl

theorem h12RawTraceTwoMeanConstantTwoPlus_eq :
    h12RawTraceTwoMeanConstantTwoPlus = 5 := rfl

theorem h12ProjectiveTraceTwoSquareConstantTwoPlus_eq :
    h12ProjectiveTraceTwoSquareConstantTwoPlus = 22 := rfl

theorem h12CompleteProjectiveFourthConstantTwoPlus_eq :
    h12CompleteProjectiveFourthConstantTwoPlus = 3151 := rfl

private theorem concreteCOEExponent_thirteen_dimension_le_h12_raw
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    13 * (N : ℝ) ≤ concreteCOEExponent N K := by
  have hdenseR : 16 * (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdense
  unfold concreteCOEExponent
  nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]

/-- The first denominator Wick polynomial has its exact `1218*N^8` bound. -/
theorem h8DenominatorFourthRawMoment_le_1218_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    h8DenominatorFourthRawMoment N K ≤
      h12RawGaussianSourceFourthConstant * (N : ℝ) ^ 8 := by
  rw [h8DenominatorFourthRawMoment_eq_traceMoments_internal hN hdense]
  simpa only [h12TraceOneRawFourthRecurrenceMoment,
    h12RawGaussianSourceFourthConstant] using
    h12TraceOneRawFourthRecurrenceMoment_le_1218_dense
      (h8H10ExactTraceRecurrenceSystem_internal hN hdense)
      (by exact_mod_cast hN)
      (concreteCOEExponent_thirteen_dimension_le_h12_raw hN hdense)

/-- The second denominator Wick polynomial has its exact `1218*N^6` bound. -/
theorem h10DenominatorSecondRawMoment_le_1218_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    h10DenominatorSecondRawMoment N K ≤
      h12RawGaussianSourceFourthConstant * (N : ℝ) ^ 6 := by
  rw [h10DenominatorSecondRawMoment_eq_traceMoments_internal hN hdense]
  simpa only [h12TraceTwoRawSquareRecurrenceMoment,
    h12RawGaussianSourceFourthConstant] using
    h12TraceTwoRawSquareRecurrenceMoment_le_1218_dense
      (h8H10ExactTraceRecurrenceSystem_internal hN hdense)
      (by exact_mod_cast hN)
      (concreteCOEExponent_thirteen_dimension_le_h12_raw hN hdense)

/-! ## Dimension-at-least-two denominator bounds -/

theorem h8DenominatorFourthRawMoment_le_34_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    h8DenominatorFourthRawMoment N K ≤
      h12RawTraceOneFourthConstantTwoPlus * (N : ℝ) ^ 8 := by
  have hNOne : 1 ≤ N := by omega
  rw [h8DenominatorFourthRawMoment_eq_traceMoments_internal hNOne hdense]
  simpa only [h12TraceOneRawFourthRecurrenceMoment,
    h12RawTraceOneFourthConstantTwoPlus] using
    h12TraceOneRawFourthRecurrenceMoment_le_34_dense
      (h8H10ExactTraceRecurrenceSystem_internal hNOne hdense)
      (by exact_mod_cast hN)
      (concreteCOEExponent_thirteen_dimension_le_h12_raw hNOne hdense)

theorem h10DenominatorSecondRawMoment_le_88_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    h10DenominatorSecondRawMoment N K ≤
      h12RawTraceTwoSquareConstantTwoPlus * (N : ℝ) ^ 6 := by
  have hNOne : 1 ≤ N := by omega
  rw [h10DenominatorSecondRawMoment_eq_traceMoments_internal hNOne hdense]
  simpa only [h12TraceTwoRawSquareRecurrenceMoment,
    h12RawTraceTwoSquareConstantTwoPlus] using
    h12TraceTwoRawSquareRecurrenceMoment_le_88_dense
      (h8H10ExactTraceRecurrenceSystem_internal hNOne hdense)
      (by exact_mod_cast hN)
      (concreteCOEExponent_thirteen_dimension_le_h12_raw hNOne hdense)

theorem h8DenominatorSecondRawMoment_le_4_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    h8DenominatorSecondRawMoment N K ≤
      h12RawTraceOneSquareMeanConstantTwoPlus * (N : ℝ) ^ 4 := by
  have hNOne : 1 ≤ N := by omega
  rw [h8DenominatorSecondRawMoment_eq_traceMoments_internal]
  simpa only [h12TraceOneRawMeanRecurrenceMoment,
    h12RawTraceOneSquareMeanConstantTwoPlus] using
    h12TraceOneRawMeanRecurrenceMoment_le_4_dense
      (h8H10ExactTraceRecurrenceSystem_internal hNOne hdense)
      (by exact_mod_cast hN)
      (concreteCOEExponent_thirteen_dimension_le_h12_raw hNOne hdense)

theorem h10DenominatorFirstRawMoment_le_5_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    h10DenominatorFirstRawMoment N K ≤
      h12RawTraceTwoMeanConstantTwoPlus * (N : ℝ) ^ 3 := by
  have hNOne : 1 ≤ N := by omega
  rw [h10DenominatorFirstRawMoment_eq_traceMoments_internal]
  simpa only [h12TraceTwoRawMeanRecurrenceMoment,
    h12RawTraceTwoMeanConstantTwoPlus] using
    h12TraceTwoRawMeanRecurrenceMoment_le_5_dense
      (h8H10ExactTraceRecurrenceSystem_internal hNOne hdense)
      (by exact_mod_cast hN)
      (concreteCOEExponent_thirteen_dimension_le_h12_raw hNOne hdense)

theorem h10DenominatorSecondRawMoment_projective_le_22_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    (((N : ℝ) - 1) / (N : ℝ)) ^ 2 *
        h10DenominatorSecondRawMoment N K ≤
      h12ProjectiveTraceTwoSquareConstantTwoPlus * (N : ℝ) ^ 6 := by
  have hNOne : 1 ≤ N := by omega
  rw [h10DenominatorSecondRawMoment_eq_traceMoments_internal hNOne hdense]
  simpa only [h12TraceTwoRawSquareRecurrenceMoment,
    h12ProjectiveTraceTwoSquareConstantTwoPlus] using
    h12TraceTwoRawSquareRecurrenceMoment_projective_le_22_dense
      (h8H10ExactTraceRecurrenceSystem_internal hNOne hdense)
      (by exact_mod_cast hN)
      (concreteCOEExponent_thirteen_dimension_le_h12_raw hNOne hdense)

theorem h10DenominatorSecondRawMoment_projective_144_le_3151_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    144 * (((N : ℝ) - 1) / (N : ℝ)) ^ 2 *
        h10DenominatorSecondRawMoment N K ≤
      h12CompleteProjectiveFourthConstantTwoPlus * (N : ℝ) ^ 6 := by
  have hNOne : 1 ≤ N := by omega
  rw [h10DenominatorSecondRawMoment_eq_traceMoments_internal hNOne hdense]
  simpa only [h12TraceTwoRawSquareRecurrenceMoment,
    h12CompleteProjectiveFourthConstantTwoPlus] using
    h12TraceTwoRawSquareRecurrenceMoment_projective_144_le_3151_dense
      (h8H10ExactTraceRecurrenceSystem_internal hNOne hdense)
      (by exact_mod_cast hN)
      (concreteCOEExponent_thirteen_dimension_le_h12_raw hNOne hdense)

/-- Concrete first Gaussian-source raw fourth moment. -/
theorem betaPrimeTraceOneSource_fourth_integral_le_1218_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ source, betaPrimeTraceOneSource N K source ^ 4
      ∂realBetaPrimeGaussianSourceLaw N K) ≤
      h12RawGaussianSourceFourthConstant * (N : ℝ) ^ 8 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [betaPrimeTraceOneSource_fourth_integral_eq_denominator_internal
    N K hgap (h14FiniteGaussianFourthWickFormula_internal N K)]
  exact h8DenominatorFourthRawMoment_le_1218_internal hN hdense

/-- Concrete second Gaussian-source raw square moment. -/
theorem betaPrimeTraceTwoSource_square_integral_le_1218_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ source, betaPrimeTraceTwoSource N K source ^ 2
      ∂realBetaPrimeGaussianSourceLaw N K) ≤
      h12RawGaussianSourceFourthConstant * (N : ℝ) ^ 6 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [betaPrimeTraceTwoSource_square_integral_eq_denominator_internal
    N K hgap (h14FiniteGaussianFourthWickFormula_internal N K)]
  exact h10DenominatorSecondRawMoment_le_1218_internal hN hdense

/-! ## Dimension-at-least-two source bounds -/

theorem betaPrimeTraceOneSource_fourth_integral_le_34_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ source, betaPrimeTraceOneSource N K source ^ 4
      ∂realBetaPrimeGaussianSourceLaw N K) ≤
      h12RawTraceOneFourthConstantTwoPlus * (N : ℝ) ^ 8 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [betaPrimeTraceOneSource_fourth_integral_eq_denominator_internal
    N K hgap (h14FiniteGaussianFourthWickFormula_internal N K)]
  exact h8DenominatorFourthRawMoment_le_34_internal hN hdense

theorem betaPrimeTraceTwoSource_square_integral_le_88_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ source, betaPrimeTraceTwoSource N K source ^ 2
      ∂realBetaPrimeGaussianSourceLaw N K) ≤
      h12RawTraceTwoSquareConstantTwoPlus * (N : ℝ) ^ 6 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [betaPrimeTraceTwoSource_square_integral_eq_denominator_internal
    N K hgap (h14FiniteGaussianFourthWickFormula_internal N K)]
  exact h10DenominatorSecondRawMoment_le_88_internal hN hdense

theorem betaPrimeTraceOneSource_square_integral_le_4_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ source, betaPrimeTraceOneSource N K source ^ 2
      ∂realBetaPrimeGaussianSourceLaw N K) ≤
      h12RawTraceOneSquareMeanConstantTwoPlus * (N : ℝ) ^ 4 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [betaPrimeTraceOneSource_square_integral_eq_denominator_internal N K hgap]
  exact h8DenominatorSecondRawMoment_le_4_internal hN hdense

theorem betaPrimeTraceTwoSource_integral_le_5_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ source, betaPrimeTraceTwoSource N K source
      ∂realBetaPrimeGaussianSourceLaw N K) ≤
      h12RawTraceTwoMeanConstantTwoPlus * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [betaPrimeTraceTwoSource_integral_eq_denominator_internal N K hgap]
  exact h10DenominatorFirstRawMoment_le_5_internal hN hdense

theorem betaPrimeTraceTwoSource_square_integral_projective_le_22_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    (((N : ℝ) - 1) / (N : ℝ)) ^ 2 *
        (∫ source, betaPrimeTraceTwoSource N K source ^ 2
          ∂realBetaPrimeGaussianSourceLaw N K) ≤
      h12ProjectiveTraceTwoSquareConstantTwoPlus * (N : ℝ) ^ 6 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [betaPrimeTraceTwoSource_square_integral_eq_denominator_internal
    N K hgap (h14FiniteGaussianFourthWickFormula_internal N K)]
  exact h10DenominatorSecondRawMoment_projective_le_22_internal hN hdense

theorem betaPrimeTraceTwoSource_square_integral_projective_144_le_3151_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    144 * (((N : ℝ) - 1) / (N : ℝ)) ^ 2 *
        (∫ source, betaPrimeTraceTwoSource N K source ^ 2
          ∂realBetaPrimeGaussianSourceLaw N K) ≤
      h12CompleteProjectiveFourthConstantTwoPlus * (N : ℝ) ^ 6 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [betaPrimeTraceTwoSource_square_integral_eq_denominator_internal
    N K hgap (h14FiniteGaussianFourthWickFormula_internal N K)]
  exact h10DenominatorSecondRawMoment_projective_144_le_3151_internal
    hN hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
