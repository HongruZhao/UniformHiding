import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveFourthTraceMoment
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_CubicTraceTwoMeanAdapterConditional
import Mathlib.Tactic

/-!
# H14 projective-cancellation algebra

This module contains only the two algebraic ingredients authorized for the
first checked H14 repair step:

* the cubic upper bound for U08's exact raw beta-prime trace-two ledger;
* the trace-zero specialization of the exact complex-projective fourth
  moment.

It contains no H14 endpoint, probability-contract hypothesis, score
majorant, or operator-radius fallback.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Pure ordered-field bound for the exact U08 beta-prime trace-two mean
ledger

`p(p+1)c(2(p+1)c+p²+p+2)/((c+1)(c-2))`.

The raw mean is genuinely cubic; the projective H14 proof will use this only
after the sphere cancellation has supplied its inverse powers of `p`. -/
theorem h14_betaPrimeYTraceTwoMeanLedgerFormula_abs_le_twenty_cube
    {p c : ℝ} (hp : 1 ≤ p) (hc : 13 * p ≤ c) :
    |p * (p + 1) * c *
          (2 * (p + 1) * c + p ^ 2 + p + 2) /
        ((c + 1) * (c - 2))| ≤
      20 * p ^ 3 := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hpm1 : 0 ≤ p - 1 := by linarith
  have hc13 : 13 ≤ c := by nlinarith
  have hc0 : 0 ≤ c := by linarith
  have hd : 0 < (c + 1) * (c - 2) := by
    exact mul_pos (by linarith) (by linarith)
  have hpSqGeP : p ≤ p ^ 2 := by
    nlinarith [mul_nonneg hp0 hpm1]
  have hpSqGeOne : 1 ≤ p ^ 2 := by
    have hpp1 : 0 ≤ p + 1 := by linarith
    nlinarith [mul_nonneg hpm1 hpp1]
  have hpp : p * (p + 1) ≤ 2 * p ^ 2 := by
    nlinarith [mul_nonneg hp0 hpm1]
  have hpc13 : 13 * p ^ 2 ≤ p * c := by
    have hmul := mul_le_mul_of_nonneg_left hc hp0
    nlinarith
  have hsmall : p ^ 2 + p + 2 ≤ p * c := by
    have : p ^ 2 + p + 2 ≤ 13 * p ^ 2 := by
      nlinarith
    exact this.trans hpc13
  have hlead : 2 * (p + 1) * c ≤ 4 * p * c := by
    have hp1 : p + 1 ≤ 2 * p := by linarith
    have hmul := mul_le_mul_of_nonneg_right hp1 hc0
    nlinarith
  have hbracket :
      2 * (p + 1) * c + p ^ 2 + p + 2 ≤ 5 * p * c := by
    nlinarith [hlead, hsmall]
  have hbracket0 :
      0 ≤ 2 * (p + 1) * c + p ^ 2 + p + 2 := by
    positivity
  have hnum :
      p * (p + 1) * c *
          (2 * (p + 1) * c + p ^ 2 + p + 2) ≤
        10 * p ^ 3 * c ^ 2 := by
    calc
      p * (p + 1) * c *
          (2 * (p + 1) * c + p ^ 2 + p + 2) =
          (p * (p + 1)) *
            (c * (2 * (p + 1) * c + p ^ 2 + p + 2)) := by ring
      _ ≤ (2 * p ^ 2) *
            (c * (2 * (p + 1) * c + p ^ 2 + p + 2)) := by
        exact mul_le_mul_of_nonneg_right hpp
          (mul_nonneg hc0 hbracket0)
      _ ≤ (2 * p ^ 2) * (c * (5 * p * c)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hbracket hc0)
          (mul_nonneg (by norm_num) (sq_nonneg p))
      _ = 10 * p ^ 3 * c ^ 2 := by ring
  have hden : c ^ 2 ≤ 2 * ((c + 1) * (c - 2)) := by
    have hc4 : (4 : ℝ) ≤ c :=
      (show (4 : ℝ) ≤ 13 by norm_num).trans hc13
    have hcm4 : 0 ≤ c - 4 := sub_nonneg.mpr hc4
    have hcp2 : 0 ≤ c + 2 := add_nonneg hc0 (by norm_num)
    have hprod : 0 ≤ (c - 4) * (c + 2) :=
      mul_nonneg hcm4 hcp2
    nlinarith
  have hscaledDen :
      10 * p ^ 3 * c ^ 2 ≤
        20 * p ^ 3 * ((c + 1) * (c - 2)) := by
    have hmul := mul_le_mul_of_nonneg_left hden
      (show 0 ≤ 10 * p ^ 3 by positivity)
    nlinarith
  have hnum0 :
      0 ≤ p * (p + 1) * c *
        (2 * (p + 1) * c + p ^ 2 + p + 2) := by
    positivity
  rw [abs_of_nonneg (div_nonneg hnum0 (le_of_lt hd))]
  exact (div_le_iff₀ hd).2 (hnum.trans hscaledDen)

/-- Unconditional cross-worker splice: U08 supplies the exact beta-prime
formal-mean identity and its dense side conditions, while the preceding U10
theorem supplies only the generic ordered-field estimate.  Neither result is
reproved here. -/
theorem h14_betaPrimeYTraceTwoFormalMeanU08_abs_le_twenty_cube_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    |U08.betaPrimeYTraceTwoFormalMeanU08 N K| ≤
      20 * (N : ℝ) ^ 3 := by
  exact U08.betaPrimeYTraceTwoFormalMeanU08_abs_le_twenty_cube_conditional
    hN hdense
    (fun {p c} hp hc ↦
      h14_betaPrimeYTraceTwoMeanLedgerFormula_abs_le_twenty_cube hp hc)

/-- If the matrix trace is zero, the fixed-point-containing cycle types in
the exact order-four projective moment vanish.  Only the `2+2` and `4` cycle
types remain, with coefficients `3` and `6`. -/
theorem integral_complexProjectiveTracePair_fourth_of_trace_zero_h14
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (htrace : Matrix.trace A = 0) :
    (∫ v : ComplexUnitSphere N,
      complexProjectiveTracePair v A ^ 4
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
        ((N : ℝ) + 3))⁻¹ : ℝ) : ℂ) *
        (3 * Matrix.trace (A * A) ^ 2 +
          6 * Matrix.trace (A * A * A * A)) := by
  simpa [htrace] using integral_complexProjectiveTracePair_fourth hN A

#print axioms h14_betaPrimeYTraceTwoMeanLedgerFormula_abs_le_twenty_cube
#print axioms h14_betaPrimeYTraceTwoFormalMeanU08_abs_le_twenty_cube_internal
#print axioms integral_complexProjectiveTracePair_fourth_of_trace_zero_h14

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
