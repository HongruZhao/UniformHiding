import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H12_RawFourthExactRecurrenceBound
import Mathlib.Tactic

/-!
# Direct exact recurrence certificate for the sharp H14 envelope

The four coefficients of `h14ProjectiveCancellationSharpEnvelope` are kept
inside one exact rational certificate.  For `n ≥ 2`, `c ≥ 13n`, their
combined expectation is at most `9990 n²`.  Bounding the four terms
separately would give the larger rounded constant `14496`.

This module is foundations-only scalar/finite-Gaussian algebra.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 7200000
set_option maxRecDepth 100000

/-- Quotient `D₉ / D₂` between the exact common fourth denominator and
the exact degree-two mean denominator. -/
def h14DirectSharpMeanLiftDenominator (c : ℝ) : ℝ :=
  (c + 3) * (c + 2) * (c + 1) * (c - 1) * (c - 2) * (c - 4) * (c - 6)

theorem h14DirectSharp_commonDenominator_factorization (c : ℝ) :
    h8H10DegreeTwoDenominator c * h14DirectSharpMeanLiftDenominator c =
      h8H10CommonVarianceDenominator c := by
  unfold h8H10DegreeTwoDenominator h14DirectSharpMeanLiftDenominator
    h8H10CommonVarianceDenominator
  ring

/-- Cleared numerator of the complete sharp H14 expectation. -/
def h14DirectSharpCombinedNumerator (n c : ℝ) : ℝ :=
  1536 * h12TraceOneRawMeanNumerator n c * n ^ 2 * c ^ 2 *
      h14DirectSharpMeanLiftDenominator c +
    1280 * h12TraceTwoRawMeanNumerator n c * n ^ 2 * c ^ 2 *
      h14DirectSharpMeanLiftDenominator c +
    3072 * h12TraceOneRawFourthNumerator n c +
    2560 * h12TraceTwoRawSquareNumerator n c * n ^ 2

/-- The coefficient-positive `9990` certificate.  After substituting
`n=2+e`, `c=13(2+e)+d`, the cleared difference has only nonnegative
coefficients. -/
theorem h14DirectSharpCombinedNumerator_le_9990_dense
    {n c : ℝ} (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h14DirectSharpCombinedNumerator n c ≤
      9990 * n ^ 6 * c ^ 2 * h8H10CommonVarianceDenominator c := by
  let e : ℝ := n - 2
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnRep : n = 2 + e := by dsimp only [e]; ring
  have hcRep : c = 13 * (2 + e) + d := by dsimp only [e, d]; ring
  rw [hnRep, hcRep]
  unfold h14DirectSharpCombinedNumerator h14DirectSharpMeanLiftDenominator
    h12TraceOneRawFourthNumerator h12TraceTwoRawSquareNumerator
    h12TraceOneRawMeanNumerator h12TraceTwoRawMeanNumerator
    h12RawMeanDenominatorQuotient h8ExactVarianceNumerator
    h10ExactVarianceNumerator h8H10CommonVarianceDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- The four exact recurrence moments with the literal sharp-envelope
coefficients and normalizations. -/
def h14DirectSharpTraceRecurrenceExpectation
    (n c x2 y x4 x2y y2 xz q : ℝ) : ℝ :=
  1536 * h12TraceOneRawMeanRecurrenceMoment n x2 y / n ^ 2 +
    1280 * h12TraceTwoRawMeanRecurrenceMoment n x2 y / n ^ 2 +
    3072 * h12TraceOneRawFourthRecurrenceMoment n x4 x2y y2 xz q /
      (n ^ 4 * c ^ 2) +
    2560 * h12TraceTwoRawSquareRecurrenceMoment n x4 x2y y2 xz q /
      (n ^ 2 * c ^ 2)

theorem h14DirectSharpTraceRecurrenceExpectation_eq_exact
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h14DirectSharpTraceRecurrenceExpectation n c x2 y x4 x2y y2 xz q =
      h14DirectSharpCombinedNumerator n c /
        (n ^ 4 * c ^ 2 * h8H10CommonVarianceDenominator c) := by
  have hnOne : 1 ≤ n := by linarith
  have hnPos : 0 < n := by linarith
  have hcPos : 0 < c := by nlinarith
  obtain ⟨_hc, h2, _h3, _h4⟩ :=
    h8H10_traceRecurrence_denominators_ne_zero_of_dense hnOne hdense
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hnOne hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  unfold h14DirectSharpTraceRecurrenceExpectation
  rw [h12TraceOneRawMeanRecurrenceMoment_eq_exact h hnOne hdense,
    h12TraceTwoRawMeanRecurrenceMoment_eq_exact h hnOne hdense,
    h12TraceOneRawFourthRecurrenceMoment_eq_exact h hnOne hdense,
    h12TraceTwoRawSquareRecurrenceMoment_eq_exact h hnOne hdense]
  unfold h14DirectSharpCombinedNumerator h14DirectSharpMeanLiftDenominator
  field_simp [h2, ne_of_gt hnPos, ne_of_gt hcPos, ne_of_gt hdenPos]
  unfold h8H10DegreeTwoDenominator h8H10CommonVarianceDenominator
  ring

theorem h14DirectSharpTraceRecurrenceExpectation_le_9990_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h14DirectSharpTraceRecurrenceExpectation n c x2 y x4 x2y y2 xz q ≤
      9990 * n ^ 2 := by
  have hnOne : 1 ≤ n := by linarith
  have hnPos : 0 < n := by linarith
  have hcPos : 0 < c := by nlinarith
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hnOne hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  rw [h14DirectSharpTraceRecurrenceExpectation_eq_exact h hn hdense]
  apply (div_le_iff₀ (by positivity :
    0 < n ^ 4 * c ^ 2 * h8H10CommonVarianceDenominator c)).2
  calc
    h14DirectSharpCombinedNumerator n c ≤
        9990 * n ^ 6 * c ^ 2 * h8H10CommonVarianceDenominator c :=
      h14DirectSharpCombinedNumerator_le_9990_dense hn hdense
    _ = 9990 * n ^ 2 *
        (n ^ 4 * c ^ 2 * h8H10CommonVarianceDenominator c) := by ring

private theorem concreteCOEExponent_thirteen_dimension_le_h14_direct
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    13 * (N : ℝ) ≤ concreteCOEExponent N K := by
  have hdenseR : 16 * (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdense
  unfold concreteCOEExponent
  nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]

/-- Concrete Gaussian-source form of the complete sharp H14 expectation. -/
theorem h14DirectSharpGaussianSourceExpectation_le_9990_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    1536 *
          (∫ source, betaPrimeTraceOneSource N K source ^ 2
            ∂realBetaPrimeGaussianSourceLaw N K) / (N : ℝ) ^ 2 +
        1280 *
          (∫ source, betaPrimeTraceTwoSource N K source
            ∂realBetaPrimeGaussianSourceLaw N K) / (N : ℝ) ^ 2 +
        3072 *
          (∫ source, betaPrimeTraceOneSource N K source ^ 4
            ∂realBetaPrimeGaussianSourceLaw N K) /
          ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
        2560 *
          (∫ source, betaPrimeTraceTwoSource N K source ^ 2
            ∂realBetaPrimeGaussianSourceLaw N K) /
          ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2) ≤
      9990 * (N : ℝ) ^ 2 := by
  have hNOne : 1 ≤ N := by omega
  have hgap : 2 * N + 8 ≤ K := by omega
  have hc13 : 13 * (N : ℝ) ≤ concreteCOEExponent N K :=
    concreteCOEExponent_thirteen_dimension_le_h14_direct hNOne hdense
  rw [betaPrimeTraceOneSource_square_integral_eq_denominator_internal N K hgap,
    betaPrimeTraceTwoSource_integral_eq_denominator_internal N K hgap,
    betaPrimeTraceOneSource_fourth_integral_eq_denominator_internal N K hgap
      (h14FiniteGaussianFourthWickFormula_internal N K),
    betaPrimeTraceTwoSource_square_integral_eq_denominator_internal N K hgap
      (h14FiniteGaussianFourthWickFormula_internal N K),
    h8DenominatorSecondRawMoment_eq_traceMoments_internal,
    h10DenominatorFirstRawMoment_eq_traceMoments_internal,
    h8DenominatorFourthRawMoment_eq_traceMoments_internal hNOne hdense,
    h10DenominatorSecondRawMoment_eq_traceMoments_internal hNOne hdense]
  simpa only [h14DirectSharpTraceRecurrenceExpectation,
    h12TraceOneRawMeanRecurrenceMoment,
    h12TraceTwoRawMeanRecurrenceMoment,
    h12TraceOneRawFourthRecurrenceMoment,
    h12TraceTwoRawSquareRecurrenceMoment] using
    h14DirectSharpTraceRecurrenceExpectation_le_9990_dense
      (h8H10ExactTraceRecurrenceSystem_internal hNOne hdense)
      (by exact_mod_cast hN) hc13

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
