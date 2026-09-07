import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10_ExactCenteredVarianceClosure
import Mathlib.Tactic

/-!
# Sharp dense H8/H10 centered-variance bounds

The exact trace-recurrence formulas admit a much sharper estimate in the
canonical dense range `13*n ≤ c`.  After writing `n = 1+e` and
`c = 13*(1+e)+d`, the differences between `1128*n^k` times the common
denominator and the respective exact numerator have nonnegative
coefficients.  This yields variance constant `1128`; the integer square-root
ceiling used by the `L²` packages is `34`.

No new probabilistic or scientific input is introduced.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

set_option maxHeartbeats 3600000
set_option maxRecDepth 100000

private theorem h8ExactVarianceNumerator_le_1128_mul_denominator_dense
    {n c : ℝ} (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h8ExactVarianceNumerator n c ≤
      1128 * n ^ 6 * h8H10CommonVarianceDenominator c := by
  let e : ℝ := n - 1
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by
    dsimp only [e]
    linarith
  have hd : 0 ≤ d := by
    dsimp only [d]
    linarith
  have hnrep : n = 1 + e := by
    dsimp only [e]
    ring
  have hcrep : c = 13 * (1 + e) + d := by
    dsimp only [e, d]
    ring
  rw [hnrep, hcrep]
  unfold h8ExactVarianceNumerator h8H10CommonVarianceDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem h10ExactVarianceNumerator_le_1128_mul_denominator_dense
    {n c : ℝ} (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h10ExactVarianceNumerator n c ≤
      1128 * n ^ 4 * h8H10CommonVarianceDenominator c := by
  let e : ℝ := n - 1
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by
    dsimp only [e]
    linarith
  have hd : 0 ≤ d := by
    dsimp only [d]
    linarith
  have hnrep : n = 1 + e := by
    dsimp only [e]
    ring
  have hcrep : c = 13 * (1 + e) + d := by
    dsimp only [e, d]
    ring
  rw [hnrep, hcrep]
  unfold h10ExactVarianceNumerator h8H10CommonVarianceDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- Sharp exact-recurrence H8 variance bound.  The integer coefficient 1128
is the smallest one certified by the coefficient-positivity proof. -/
theorem h8_traceRecurrenceVariance_le_1128_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h8TraceRecurrenceVariance n x2 y x4 x2y y2 xz q ≤
      1128 * n ^ 6 := by
  have hlow := h8H10_commonVarianceDenominator_lower_dense hn hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hlow
  rw [h8_exact_variance_identity_of_traceRecurrences_dense h hn hdense]
  apply (div_le_iff₀ hdenPos).2
  exact h8ExactVarianceNumerator_le_1128_mul_denominator_dense hn hdense

/-- Sharp exact-recurrence H10 variance bound. -/
theorem h10_traceRecurrenceVariance_le_1128_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h10TraceRecurrenceVariance n x2 y x4 x2y y2 xz q ≤
      1128 * n ^ 4 := by
  have hlow := h8H10_commonVarianceDenominator_lower_dense hn hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hlow
  rw [h10_exact_variance_identity_of_traceRecurrences_dense h hn hdense]
  apply (div_le_iff₀ hdenPos).2
  exact h10ExactVarianceNumerator_le_1128_mul_denominator_dense hn hdense

/-- Concrete H8 denominator variance bound. -/
theorem h8DenominatorCenteredVariance_le_1128_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    h8DenominatorCenteredVariance N K ≤ 1128 * (N : ℝ) ^ 6 := by
  rw [h8DenominatorCenteredVariance_eq_traceRecurrence_internal hN hdense]
  exact h8_traceRecurrenceVariance_le_1128_dense
    (h8H10ExactTraceRecurrenceSystem_internal hN hdense)
    (by exact_mod_cast hN)
    (thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense)

/-- Concrete H10 denominator variance bound. -/
theorem h10DenominatorCenteredVariance_le_1128_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    h10DenominatorCenteredVariance N K ≤ 1128 * (N : ℝ) ^ 4 := by
  rw [h10DenominatorCenteredVariance_eq_traceRecurrence_internal hN hdense]
  exact h10_traceRecurrenceVariance_le_1128_dense
    (h8H10ExactTraceRecurrenceSystem_internal hN hdense)
    (by exact_mod_cast hN)
    (thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Integer `L²` ceiling for the sharp H8/H10 variance coefficient 1128. -/
def sharp34CenteredTraceTwoL2Constant : ℝ := 34

/-- Sharp H8 centered trace-square package with `L²` constant 34. -/
theorem betaPrimeYTraceOneSquare_centered_two_momentPackage_sharp34
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
          sharp34CenteredTraceTwoL2Constant * (N : ℝ) ^ 3) := by
  have hCore :=
    U08.betaPrimeYTraceOneSquare_centered_memLp_two_and_lpNorm_eq_sqrt_internal
      hgap (U08.h14FiniteGaussianFourthWickFormula_internal N K)
  refine ⟨hCore.1, ?_⟩
  intro hdense
  rw [hCore.2]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by unfold sharp34CenteredTraceTwoL2Constant; positivity, ?_⟩
  calc
    U08.h8DenominatorCenteredVariance N K ≤ 1128 * (N : ℝ) ^ 6 :=
      U08.h8DenominatorCenteredVariance_le_1128_internal hN hdense
    _ ≤ (sharp34CenteredTraceTwoL2Constant * (N : ℝ) ^ 3) ^ 2 := by
      unfold sharp34CenteredTraceTwoL2Constant
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      nlinarith [sq_nonneg ((N : ℝ) ^ 3)]

/-- Sharp H10 centered second-trace package with `L²` constant 34. -/
theorem betaPrimeYTraceTwo_centered_two_momentPackage_sharp34
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
          sharp34CenteredTraceTwoL2Constant * (N : ℝ) ^ 2) := by
  have hCore :=
    U08.betaPrimeYTraceTwo_centered_memLp_two_and_lpNorm_eq_sqrt_internal
      hgap (U08.h14FiniteGaussianFourthWickFormula_internal N K)
  refine ⟨hCore.1, ?_⟩
  intro hdense
  rw [hCore.2]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by unfold sharp34CenteredTraceTwoL2Constant; positivity, ?_⟩
  calc
    U08.h10DenominatorCenteredVariance N K ≤ 1128 * (N : ℝ) ^ 4 :=
      U08.h10DenominatorCenteredVariance_le_1128_internal hN hdense
    _ ≤ (sharp34CenteredTraceTwoL2Constant * (N : ℝ) ^ 2) ^ 2 := by
      unfold sharp34CenteredTraceTwoL2Constant
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      nlinarith [sq_nonneg ((N : ℝ) ^ 2)]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
