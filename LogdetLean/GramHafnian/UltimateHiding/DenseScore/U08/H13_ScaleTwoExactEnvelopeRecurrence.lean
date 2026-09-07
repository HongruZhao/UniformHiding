import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H12_RawFourthExactRecurrenceBound
import Mathlib.Tactic

/-!
# Direct exact recurrence certificate for the scale-two H13 envelope

The deterministic H13 contraction costs exactly twice the closed H14 radial
envelope.  Keeping its four trace monomials in a single rational expression,
rather than estimating them separately, gives the coefficient `52204` for
`n >= 2`, `c >= 13n`.

This file is foundations-only scalar and finite-Gaussian algebra.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.DenseScore

set_option maxHeartbeats 7200000
set_option maxRecDepth 100000

/-- Quotient `D9 / D2` between the exact common fourth denominator and the
exact degree-two mean denominator. -/
def h13ScaleTwoMeanLiftDenominator (c : ℝ) : ℝ :=
  (c + 3) * (c + 2) * (c + 1) * (c - 1) * (c - 2) * (c - 4) * (c - 6)

theorem h13ScaleTwo_commonDenominator_factorization (c : ℝ) :
    h8H10DegreeTwoDenominator c * h13ScaleTwoMeanLiftDenominator c =
      h8H10CommonVarianceDenominator c := by
  unfold h8H10DegreeTwoDenominator h13ScaleTwoMeanLiftDenominator
    h8H10CommonVarianceDenominator
  ring

/-- Cleared numerator of the complete scale-two H13 expectation. -/
def h13ScaleTwoCombinedNumerator (n c : ℝ) : ℝ :=
  8192 *
    (h12TraceOneRawMeanNumerator n c * n ^ 2 * c ^ 2 *
        h13ScaleTwoMeanLiftDenominator c +
      h12TraceTwoRawMeanNumerator n c * n ^ 2 * c ^ 2 *
        h13ScaleTwoMeanLiftDenominator c +
      h12TraceOneRawFourthNumerator n c +
      h12TraceTwoRawSquareNumerator n c * n ^ 2)

/-- The coefficient-positive `52204` certificate.  After substituting
`n=2+e`, `c=13(2+e)+d`, the cleared difference has only nonnegative
coefficients. -/
theorem h13ScaleTwoCombinedNumerator_le_52204_dense
    {n c : ℝ} (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h13ScaleTwoCombinedNumerator n c ≤
      52204 * n ^ 6 * c ^ 2 * h8H10CommonVarianceDenominator c := by
  let e : ℝ := n - 2
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnRep : n = 2 + e := by dsimp only [e]; ring
  have hcRep : c = 13 * (2 + e) + d := by dsimp only [e, d]; ring
  rw [hnRep, hcRep]
  unfold h13ScaleTwoCombinedNumerator h13ScaleTwoMeanLiftDenominator
    h12TraceOneRawFourthNumerator h12TraceTwoRawSquareNumerator
    h12TraceOneRawMeanNumerator h12TraceTwoRawMeanNumerator
    h12RawMeanDenominatorQuotient h8ExactVarianceNumerator
    h10ExactVarianceNumerator h8H10CommonVarianceDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- The four exact recurrence moments with the literal scale-two H13
coefficients and normalizations. -/
def h13ScaleTwoTraceRecurrenceExpectation
    (n c x2 y x4 x2y y2 xz q : ℝ) : ℝ :=
  8192 *
    (h12TraceOneRawMeanRecurrenceMoment n x2 y / n ^ 2 +
      h12TraceTwoRawMeanRecurrenceMoment n x2 y / n ^ 2 +
      h12TraceOneRawFourthRecurrenceMoment n x4 x2y y2 xz q /
        (n ^ 4 * c ^ 2) +
      h12TraceTwoRawSquareRecurrenceMoment n x4 x2y y2 xz q /
        (n ^ 2 * c ^ 2))

theorem h13ScaleTwoTraceRecurrenceExpectation_eq_exact
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h13ScaleTwoTraceRecurrenceExpectation n c x2 y x4 x2y y2 xz q =
      h13ScaleTwoCombinedNumerator n c /
        (n ^ 4 * c ^ 2 * h8H10CommonVarianceDenominator c) := by
  have hnOne : 1 ≤ n := by linarith
  have hnPos : 0 < n := by linarith
  have hcPos : 0 < c := by nlinarith
  obtain ⟨_hc, h2, _h3, _h4⟩ :=
    h8H10_traceRecurrence_denominators_ne_zero_of_dense hnOne hdense
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hnOne hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  unfold h13ScaleTwoTraceRecurrenceExpectation
  rw [h12TraceOneRawMeanRecurrenceMoment_eq_exact h hnOne hdense,
    h12TraceTwoRawMeanRecurrenceMoment_eq_exact h hnOne hdense,
    h12TraceOneRawFourthRecurrenceMoment_eq_exact h hnOne hdense,
    h12TraceTwoRawSquareRecurrenceMoment_eq_exact h hnOne hdense]
  unfold h13ScaleTwoCombinedNumerator h13ScaleTwoMeanLiftDenominator
  field_simp [h2, ne_of_gt hnPos, ne_of_gt hcPos, ne_of_gt hdenPos]
  unfold h8H10DegreeTwoDenominator h8H10CommonVarianceDenominator
  ring

theorem h13ScaleTwoTraceRecurrenceExpectation_le_52204_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h13ScaleTwoTraceRecurrenceExpectation n c x2 y x4 x2y y2 xz q ≤
      52204 * n ^ 2 := by
  have hnOne : 1 ≤ n := by linarith
  have hnPos : 0 < n := by linarith
  have hcPos : 0 < c := by nlinarith
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hnOne hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  rw [h13ScaleTwoTraceRecurrenceExpectation_eq_exact h hn hdense]
  apply (div_le_iff₀ (by positivity :
    0 < n ^ 4 * c ^ 2 * h8H10CommonVarianceDenominator c)).2
  calc
    h13ScaleTwoCombinedNumerator n c ≤
        52204 * n ^ 6 * c ^ 2 * h8H10CommonVarianceDenominator c :=
      h13ScaleTwoCombinedNumerator_le_52204_dense hn hdense
    _ = 52204 * n ^ 2 *
        (n ^ 4 * c ^ 2 * h8H10CommonVarianceDenominator c) := by ring

private theorem concreteCOEExponent_thirteen_dimension_le_h13_scaleTwo
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    13 * (N : ℝ) ≤ concreteCOEExponent N K := by
  have hdenseR : 16 * (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdense
  unfold concreteCOEExponent
  nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]

/-- Concrete Gaussian-source form of the complete scale-two H13
expectation. -/
theorem h13ScaleTwoGaussianSourceExpectation_le_52204_internal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    8192 *
        ((∫ source, betaPrimeTraceOneSource N K source ^ 2
            ∂realBetaPrimeGaussianSourceLaw N K) / (N : ℝ) ^ 2 +
          (∫ source, betaPrimeTraceTwoSource N K source
            ∂realBetaPrimeGaussianSourceLaw N K) / (N : ℝ) ^ 2 +
          (∫ source, betaPrimeTraceOneSource N K source ^ 4
            ∂realBetaPrimeGaussianSourceLaw N K) /
              ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
          (∫ source, betaPrimeTraceTwoSource N K source ^ 2
            ∂realBetaPrimeGaussianSourceLaw N K) /
              ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)) ≤
      52204 * (N : ℝ) ^ 2 := by
  have hNOne : 1 ≤ N := by omega
  have hgap : 2 * N + 8 ≤ K := by omega
  have hc13 : 13 * (N : ℝ) ≤ concreteCOEExponent N K :=
    concreteCOEExponent_thirteen_dimension_le_h13_scaleTwo hNOne hdense
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
  simpa only [h13ScaleTwoTraceRecurrenceExpectation,
    h12TraceOneRawMeanRecurrenceMoment,
    h12TraceTwoRawMeanRecurrenceMoment,
    h12TraceOneRawFourthRecurrenceMoment,
    h12TraceTwoRawSquareRecurrenceMoment] using
    h13ScaleTwoTraceRecurrenceExpectation_le_52204_dense
      (h8H10ExactTraceRecurrenceSystem_internal hNOne hdense)
      (by exact_mod_cast hN) hc13

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
