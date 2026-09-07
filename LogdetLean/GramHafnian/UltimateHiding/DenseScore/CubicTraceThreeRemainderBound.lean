import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CubicTraceThreeNormalizationRoute
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCenteredBasicDerived
import Mathlib.Tactic

/-!
# Internal lower-trace remainder bound for the raw third trace

This module closes the normalization route for `Tr Y^3`.  The exact centered
cubic density is first collected into the five lower-trace monomials
`(Tr Y)^3`, `(Tr Y)^2`, `Tr Y * Tr Y^2`, `Tr Y^2`, and `Tr Y`.  Their retained
or internally derived moment packages then give an `L^1 = O(N)` remainder.
Together with total-mass cancellation and positivity, this proves the sharp
`L^1 = O(N^4)` raw-third-trace package without the former raw-third moment
axiom.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

def cubicTraceThreeRemainderDenominator (n c : ℝ) : ℝ :=
  n ^ 3 * (n + 1) * (n + 2) * c ^ 2

def cubicTraceThreeRemainderCoeffCubeNumerator (n c : ℝ) : ℝ :=
  48 * n * c + 16 * n ^ 2 + 32 * c ^ 2

def cubicTraceThreeRemainderCoeffSquareNumerator (n c : ℝ) : ℝ :=
  -192 * n * c + 48 * n * c ^ 2 + 48 * n ^ 2 * c +
    24 * n ^ 2 * c ^ 2 + 24 * n ^ 3 * c - 192 * c ^ 2

def cubicTraceThreeRemainderCoeffMixedNumerator (n c : ℝ) : ℝ :=
  48 * n * c - 48 * n * c ^ 2 - 192 * n - 48 * n ^ 2 * c +
    48 * n ^ 2 - 192 * c

def cubicTraceThreeRemainderCoeffTwoNumerator (n c : ℝ) : ℝ :=
  -288 * n * c + 192 * n * c ^ 2 - 48 * n ^ 2 * c ^ 2 +
    24 * n ^ 3 * c - 24 * n ^ 3 * c ^ 2 + 384 * c

def cubicTraceThreeRemainderCoeffOneNumerator (n c : ℝ) : ℝ :=
  -96 * n * c ^ 2 - 64 * n ^ 2 * c ^ 2 + 24 * n ^ 3 * c ^ 2 +
    8 * n ^ 4 * c ^ 2 + 128 * c ^ 2

def cubicTraceThreeRemainderCoeffCube (n c : ℝ) : ℝ :=
  cubicTraceThreeRemainderCoeffCubeNumerator n c /
    cubicTraceThreeRemainderDenominator n c

def cubicTraceThreeRemainderCoeffSquare (n c : ℝ) : ℝ :=
  cubicTraceThreeRemainderCoeffSquareNumerator n c /
    cubicTraceThreeRemainderDenominator n c

def cubicTraceThreeRemainderCoeffMixed (n c : ℝ) : ℝ :=
  cubicTraceThreeRemainderCoeffMixedNumerator n c /
    cubicTraceThreeRemainderDenominator n c

def cubicTraceThreeRemainderCoeffTwo (n c : ℝ) : ℝ :=
  cubicTraceThreeRemainderCoeffTwoNumerator n c /
    cubicTraceThreeRemainderDenominator n c

def cubicTraceThreeRemainderCoeffOne (n c : ℝ) : ℝ :=
  cubicTraceThreeRemainderCoeffOneNumerator n c /
    cubicTraceThreeRemainderDenominator n c

/-- Exact collection of the lower-trace remainder into five monomials. -/
theorem scalarAveragedCenteredCubicDensity_zero_eq_lowerTracePolynomial
    {n c : ℝ} (hn : 0 < n) (hc : c ≠ 0)
    (x y : ℝ) :
    scalarAveragedCenteredCubicDensity n c x y 0 =
      cubicTraceThreeRemainderCoeffCube n c * x ^ 3 +
      cubicTraceThreeRemainderCoeffSquare n c * x ^ 2 +
      cubicTraceThreeRemainderCoeffMixed n c * (x * y) +
      cubicTraceThreeRemainderCoeffTwo n c * y +
      cubicTraceThreeRemainderCoeffOne n c * x := by
  have hn1 : n + 1 ≠ 0 := by
    positivity
  have hn2 : n + 2 ≠ 0 := by
    positivity
  simp only [scalarAveragedCenteredCubicDensity,
    scalarAveragedRankOneCubicDensity, scalarMixedScalarQuadraticDensity,
    scalarCentralDensityScoreThree, scalarCenteredTraceOne,
    scalarCenteredTraceTwo, scalarCenteredTraceThree,
    averagedCubicNonWExpression, averagedCubicWTraceExpression,
    cubicTraceCoefficientThree, cubicTraceCoefficientTwo,
    cubicTraceCoefficientOne, cubicTraceCoefficientZero,
    centeredQuadraticTraceBracket, centralDerivativeQuadraticTraceBracket,
    centralTraceOneDerivative, centralTraceTwoDerivative,
    quadraticTraceCoeffTwo, quadraticTraceCoeffSquare,
    quadraticTraceCoeffOne,
    cubicTraceThreeRemainderCoeffCube,
    cubicTraceThreeRemainderCoeffSquare,
    cubicTraceThreeRemainderCoeffMixed,
    cubicTraceThreeRemainderCoeffTwo,
    cubicTraceThreeRemainderCoeffOne,
    cubicTraceThreeRemainderCoeffCubeNumerator,
    cubicTraceThreeRemainderCoeffSquareNumerator,
    cubicTraceThreeRemainderCoeffMixedNumerator,
    cubicTraceThreeRemainderCoeffTwoNumerator,
    cubicTraceThreeRemainderCoeffOneNumerator,
    cubicTraceThreeRemainderDenominator]
  field_simp [ne_of_gt hn, hc, hn1, hn2]
  ring

private theorem cubicTraceThreeRemainderDenominator_lower_bound
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) :
    n ^ 5 * c ^ 2 ≤ cubicTraceThreeRemainderDenominator n c := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hc0 : 0 ≤ c := hn0.trans hc
  have hpair : n ^ 2 ≤ (n + 1) * (n + 2) := by
    nlinarith [sq_nonneg n]
  unfold cubicTraceThreeRemainderDenominator
  calc
    n ^ 5 * c ^ 2 = n ^ 3 * n ^ 2 * c ^ 2 := by ring
    _ ≤ n ^ 3 * ((n + 1) * (n + 2)) * c ^ 2 := by gcongr
    _ = n ^ 3 * (n + 1) * (n + 2) * c ^ 2 := by ring

private theorem cubicTraceThreeRemainderCoeffCubeNumerator_abs_le
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) :
    |cubicTraceThreeRemainderCoeffCubeNumerator n c| ≤ 96 * c ^ 2 := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hc0 : 0 ≤ c := hn0.trans hc
  have hnc : n * c ≤ c ^ 2 := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc)]
  have hn2 : n ^ 2 ≤ c ^ 2 := by nlinarith
  rw [abs_of_nonneg]
  · unfold cubicTraceThreeRemainderCoeffCubeNumerator
    nlinarith
  · unfold cubicTraceThreeRemainderCoeffCubeNumerator
    positivity

theorem cubicTraceThreeRemainderCoeffCube_abs_le
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) :
    |cubicTraceThreeRemainderCoeffCube n c| ≤ 100 / n ^ 5 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hcpos : 0 < c := hnpos.trans_le hc
  have hdenpos : 0 < cubicTraceThreeRemainderDenominator n c := by
    unfold cubicTraceThreeRemainderDenominator
    positivity
  have hden := cubicTraceThreeRemainderDenominator_lower_bound hn hc
  unfold cubicTraceThreeRemainderCoeffCube
  rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
  calc
    |cubicTraceThreeRemainderCoeffCubeNumerator n c| ≤ 96 * c ^ 2 :=
      cubicTraceThreeRemainderCoeffCubeNumerator_abs_le hn hc
    _ ≤ 100 * c ^ 2 := by nlinarith [sq_nonneg c]
    _ = (100 / n ^ 5) * (n ^ 5 * c ^ 2) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ (100 / n ^ 5) * cubicTraceThreeRemainderDenominator n c := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

private theorem cubicTraceThreeRemainderCoeffSquareNumerator_abs_le
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) :
    |cubicTraceThreeRemainderCoeffSquareNumerator n c| ≤
      528 * (n ^ 2 * c ^ 2) := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hc1 : 1 ≤ c := hn.trans hc
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  let b := n ^ 2 * c ^ 2
  have hnc : 0 ≤ n * c := mul_nonneg hn0 hc0
  have hnc2 : 0 ≤ n * c ^ 2 := mul_nonneg hn0 (sq_nonneg c)
  have hn2c : 0 ≤ n ^ 2 * c := mul_nonneg (sq_nonneg n) hc0
  have hn3c : 0 ≤ n ^ 3 * c := by positivity
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hn_sq : n ≤ n ^ 2 := by
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hn)]
  have hc_sq : c ≤ c ^ 2 := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  have hnc_le : n * c ≤ b := by
    dsimp only [b]
    calc
      n * c ≤ n ^ 2 * c := by gcongr
      _ ≤ n ^ 2 * c ^ 2 := by gcongr
  have hnc2_le : n * c ^ 2 ≤ b := by
    dsimp only [b]
    gcongr
  have hn2c_le : n ^ 2 * c ≤ b := by
    dsimp only [b]
    gcongr
  have hn3c_le : n ^ 3 * c ≤ b := by
    dsimp only [b]
    calc
      n ^ 3 * c = n ^ 2 * (n * c) := by ring
      _ ≤ n ^ 2 * (c * c) := by gcongr
      _ = n ^ 2 * c ^ 2 := by ring
  have hc2_le : c ^ 2 ≤ b := by
    have hn2 : 1 ≤ n ^ 2 := by nlinarith [sq_nonneg (n - 1)]
    dsimp only [b]
    calc
      c ^ 2 = 1 * c ^ 2 := by ring
      _ ≤ n ^ 2 * c ^ 2 := by gcongr
  apply abs_le.mpr
  constructor <;>
    unfold cubicTraceThreeRemainderCoeffSquareNumerator <;>
    dsimp only [b] at * <;> nlinarith

theorem cubicTraceThreeRemainderCoeffSquare_abs_le
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) :
    |cubicTraceThreeRemainderCoeffSquare n c| ≤ 600 / n ^ 3 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hcpos : 0 < c := hnpos.trans_le hc
  have hdenpos : 0 < cubicTraceThreeRemainderDenominator n c := by
    unfold cubicTraceThreeRemainderDenominator
    positivity
  have hden := cubicTraceThreeRemainderDenominator_lower_bound hn hc
  unfold cubicTraceThreeRemainderCoeffSquare
  rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
  calc
    |cubicTraceThreeRemainderCoeffSquareNumerator n c| ≤
        528 * (n ^ 2 * c ^ 2) :=
      cubicTraceThreeRemainderCoeffSquareNumerator_abs_le hn hc
    _ ≤ 600 * (n ^ 2 * c ^ 2) := by
      nlinarith [mul_nonneg (sq_nonneg n) (sq_nonneg c)]
    _ = (600 / n ^ 3) * (n ^ 5 * c ^ 2) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ (600 / n ^ 3) * cubicTraceThreeRemainderDenominator n c := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

private theorem cubicTraceThreeRemainderCoeffMixedNumerator_abs_le
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) :
    |cubicTraceThreeRemainderCoeffMixedNumerator n c| ≤
      576 * (n * c ^ 2) := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hc1 : 1 ≤ c := hn.trans hc
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have hc_sq : c ≤ c ^ 2 := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  let b := n * c ^ 2
  have hnc : 0 ≤ n * c := mul_nonneg hn0 hc0
  have hnc2 : 0 ≤ n * c ^ 2 := mul_nonneg hn0 (sq_nonneg c)
  have hn2c : 0 ≤ n ^ 2 * c := mul_nonneg (sq_nonneg n) hc0
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  have hnc_le : n * c ≤ b := by
    dsimp only [b]
    gcongr
  have hn_le : n ≤ b := by
    dsimp only [b]
    calc
      n = n * 1 := by ring
      _ ≤ n * c ^ 2 := by
        gcongr
        nlinarith [sq_nonneg (c - 1)]
  have hn2c_le : n ^ 2 * c ≤ b := by
    dsimp only [b]
    calc
      n ^ 2 * c = (n * c) * n := by ring
      _ ≤ (n * c) * c := by gcongr
      _ = n * c ^ 2 := by ring
  have hn2_le : n ^ 2 ≤ b := by
    dsimp only [b]
    calc
      n ^ 2 = n * n := by ring
      _ ≤ n * c ^ 2 := by
        gcongr
        exact hc.trans hc_sq
  have hc_le : c ≤ b := by
    dsimp only [b]
    calc
      c = 1 * c := by ring
      _ ≤ n * c := by gcongr
      _ ≤ n * c ^ 2 := by gcongr
  apply abs_le.mpr
  constructor <;>
    unfold cubicTraceThreeRemainderCoeffMixedNumerator <;>
    dsimp only [b] at * <;> nlinarith

theorem cubicTraceThreeRemainderCoeffMixed_abs_le
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) :
    |cubicTraceThreeRemainderCoeffMixed n c| ≤ 600 / n ^ 4 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hcpos : 0 < c := hnpos.trans_le hc
  have hdenpos : 0 < cubicTraceThreeRemainderDenominator n c := by
    unfold cubicTraceThreeRemainderDenominator
    positivity
  have hden := cubicTraceThreeRemainderDenominator_lower_bound hn hc
  unfold cubicTraceThreeRemainderCoeffMixed
  rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
  calc
    |cubicTraceThreeRemainderCoeffMixedNumerator n c| ≤
        576 * (n * c ^ 2) :=
      cubicTraceThreeRemainderCoeffMixedNumerator_abs_le hn hc
    _ ≤ 600 * (n * c ^ 2) := by
      nlinarith [mul_nonneg (zero_le_one.trans hn) (sq_nonneg c)]
    _ = (600 / n ^ 4) * (n ^ 5 * c ^ 2) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ (600 / n ^ 4) * cubicTraceThreeRemainderDenominator n c := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

private theorem cubicTraceThreeRemainderCoeffTwoNumerator_abs_le
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) :
    |cubicTraceThreeRemainderCoeffTwoNumerator n c| ≤
      960 * (n ^ 3 * c ^ 2) := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hc1 : 1 ≤ c := hn.trans hc
  have hc0 : 0 ≤ c := zero_le_one.trans hc1
  have hn_sq : n ≤ n ^ 2 := by
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hn)]
  have hn_cube : n ^ 2 ≤ n ^ 3 := by
    calc
      n ^ 2 = n * n := by ring
      _ ≤ n * n ^ 2 := by gcongr
      _ = n ^ 3 := by ring
  have hc_sq : c ≤ c ^ 2 := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  let b := n ^ 3 * c ^ 2
  have hnc : 0 ≤ n * c := mul_nonneg hn0 hc0
  have hnc2 : 0 ≤ n * c ^ 2 := mul_nonneg hn0 (sq_nonneg c)
  have hn2c2 : 0 ≤ n ^ 2 * c ^ 2 :=
    mul_nonneg (sq_nonneg n) (sq_nonneg c)
  have hn3c : 0 ≤ n ^ 3 * c := by positivity
  have hc0' : 0 ≤ c := hc0
  have hnc_le : n * c ≤ b := by
    dsimp only [b]
    calc
      n * c ≤ n ^ 3 * c := by gcongr; exact hn_sq.trans hn_cube
      _ ≤ n ^ 3 * c ^ 2 := by gcongr
  have hnc2_le : n * c ^ 2 ≤ b := by
    dsimp only [b]
    gcongr
    exact hn_sq.trans hn_cube
  have hn2c2_le : n ^ 2 * c ^ 2 ≤ b := by
    dsimp only [b]
    gcongr
  have hn3c_le : n ^ 3 * c ≤ b := by
    dsimp only [b]
    gcongr
  have hc_le : c ≤ b := by
    have hn3 : 1 ≤ n ^ 3 := by
      calc
        1 ≤ n := hn
        _ ≤ n ^ 2 := hn_sq
        _ ≤ n ^ 3 := hn_cube
    dsimp only [b]
    calc
      c ≤ c ^ 2 := hc_sq
      _ = 1 * c ^ 2 := by ring
      _ ≤ n ^ 3 * c ^ 2 := by gcongr
  apply abs_le.mpr
  constructor <;>
    unfold cubicTraceThreeRemainderCoeffTwoNumerator <;>
    dsimp only [b] at * <;> nlinarith

theorem cubicTraceThreeRemainderCoeffTwo_abs_le
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) :
    |cubicTraceThreeRemainderCoeffTwo n c| ≤ 1000 / n ^ 2 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hcpos : 0 < c := hnpos.trans_le hc
  have hdenpos : 0 < cubicTraceThreeRemainderDenominator n c := by
    unfold cubicTraceThreeRemainderDenominator
    positivity
  have hden := cubicTraceThreeRemainderDenominator_lower_bound hn hc
  unfold cubicTraceThreeRemainderCoeffTwo
  rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
  calc
    |cubicTraceThreeRemainderCoeffTwoNumerator n c| ≤
        960 * (n ^ 3 * c ^ 2) :=
      cubicTraceThreeRemainderCoeffTwoNumerator_abs_le hn hc
    _ ≤ 1000 * (n ^ 3 * c ^ 2) := by
      nlinarith [mul_nonneg (show 0 ≤ n ^ 3 by positivity) (sq_nonneg c)]
    _ = (1000 / n ^ 2) * (n ^ 5 * c ^ 2) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ (1000 / n ^ 2) * cubicTraceThreeRemainderDenominator n c := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

private theorem cubicTraceThreeRemainderCoeffOneNumerator_abs_le
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) :
    |cubicTraceThreeRemainderCoeffOneNumerator n c| ≤
      320 * (n ^ 4 * c ^ 2) := by
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hc0 : 0 ≤ c := hn0.trans hc
  have hn_sq : n ≤ n ^ 2 := by
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hn)]
  have hn_cube : n ^ 2 ≤ n ^ 3 := by
    calc
      n ^ 2 = n * n := by ring
      _ ≤ n * n ^ 2 := by gcongr
      _ = n ^ 3 := by ring
  have hn_four : n ^ 3 ≤ n ^ 4 := by
    calc
      n ^ 3 = n * n ^ 2 := by ring
      _ ≤ n ^ 2 * n ^ 2 := by gcongr
      _ = n ^ 4 := by ring
  let b := n ^ 4 * c ^ 2
  have hnc2 : 0 ≤ n * c ^ 2 := mul_nonneg hn0 (sq_nonneg c)
  have hn2c2 : 0 ≤ n ^ 2 * c ^ 2 :=
    mul_nonneg (sq_nonneg n) (sq_nonneg c)
  have hn3c2 : 0 ≤ n ^ 3 * c ^ 2 := by positivity
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hnc2_le : n * c ^ 2 ≤ b := by
    dsimp only [b]
    gcongr
    exact hn_sq.trans (hn_cube.trans hn_four)
  have hn2c2_le : n ^ 2 * c ^ 2 ≤ b := by
    dsimp only [b]
    exact mul_le_mul_of_nonneg_right (hn_cube.trans hn_four) (sq_nonneg c)
  have hn3c2_le : n ^ 3 * c ^ 2 ≤ b := by
    dsimp only [b]
    gcongr
  have hc2_le : c ^ 2 ≤ b := by
    have hn4 : 1 ≤ n ^ 4 := hn.trans
      (hn_sq.trans (hn_cube.trans hn_four))
    dsimp only [b]
    calc
      c ^ 2 = 1 * c ^ 2 := by ring
      _ ≤ n ^ 4 * c ^ 2 := by gcongr
  apply abs_le.mpr
  constructor <;>
    unfold cubicTraceThreeRemainderCoeffOneNumerator <;>
    dsimp only [b] at * <;> nlinarith

theorem cubicTraceThreeRemainderCoeffOne_abs_le
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) :
    |cubicTraceThreeRemainderCoeffOne n c| ≤ 400 / n := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hcpos : 0 < c := hnpos.trans_le hc
  have hdenpos : 0 < cubicTraceThreeRemainderDenominator n c := by
    unfold cubicTraceThreeRemainderDenominator
    positivity
  have hden := cubicTraceThreeRemainderDenominator_lower_bound hn hc
  unfold cubicTraceThreeRemainderCoeffOne
  rw [abs_div, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
  calc
    |cubicTraceThreeRemainderCoeffOneNumerator n c| ≤
        320 * (n ^ 4 * c ^ 2) :=
      cubicTraceThreeRemainderCoeffOneNumerator_abs_le hn hc
    _ ≤ 400 * (n ^ 4 * c ^ 2) := by
      nlinarith [mul_nonneg (show 0 ≤ n ^ 4 by positivity) (sq_nonneg c)]
    _ = (400 / n) * (n ^ 5 * c ^ 2) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ (400 / n) * cubicTraceThreeRemainderDenominator n c := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

/-! ## Raw first-trace cube from the retained centered `L^3` package -/

def derivedRawTraceOneL3Constant : ℝ :=
  denseClassicalMomentConstant + 2

def derivedRawTraceOneCubeConstant : ℝ :=
  derivedRawTraceOneL3Constant ^ 3

/-- Adding the exact mean to the centered first trace costs only two units in
the dimension-two coefficient. -/
theorem betaPrimeYTraceOne_lpNorm_three_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceOne N K) 3 (betaPrimeTraceFourLaw N K) ≤
      derivedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  let mean : ℝ := ∫ u, betaPrimeYTraceOne N K u ∂mu
  let centered : (Fin 4 → ℝ) → ℝ :=
    fun u ↦ betaPrimeYTraceOne N K u - mean
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hcentered : MemLp centered 3 mu := by
    simpa only [centered, mean, mu] using
      betaPrimeYTraceOne_centered_memLp_three_proved_allDimensions hN hgap
  have hcenteredNorm : lpNorm centered 3 mu ≤
      denseClassicalMomentConstant * (N : ℝ) := by
    simpa only [centered, mean, mu] using
      betaPrimeYTraceOne_centered_lpNorm_three_le_proved_allDimensions hN hdense
  have hmean : mean = (N : ℝ) * ((N : ℝ) + 1) := by
    simpa only [mean, mu] using
      betaPrimeYTraceOne_integral_external hN (by omega)
  have hmean0 : 0 ≤ mean := by rw [hmean]; positivity
  have hconstNorm : lpNorm (fun _ : Fin 4 → ℝ ↦ mean) 3 mu = mean := by
    rw [lpNorm_const (p := (3 : ENNReal)) (by norm_num)
      (IsProbabilityMeasure.ne_zero mu) mean]
    simp [Real.norm_eq_abs, abs_of_nonneg hmean0]
  have htri := lpNorm_add_le hcentered (p := (3 : ENNReal)) (by norm_num)
    (g := fun _ : Fin 4 → ℝ ↦ mean)
  rw [show betaPrimeYTraceOne N K =
      centered + (fun _ : Fin 4 → ℝ ↦ mean) by
    funext u
    simp [centered]]
  calc
    lpNorm (centered + (fun _ : Fin 4 → ℝ ↦ mean)) 3 mu ≤
        lpNorm centered 3 mu +
          lpNorm (fun _ : Fin 4 → ℝ ↦ mean) 3 mu := htri
    _ = lpNorm centered 3 mu + mean := by rw [hconstNorm]
    _ ≤ denseClassicalMomentConstant * (N : ℝ) +
        (N : ℝ) * ((N : ℝ) + 1) := by
      rw [hmean]
      exact add_le_add hcenteredNorm le_rfl
    _ ≤ derivedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
      have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := zero_le_one.trans hNr
      have hpow : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
        nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hNr)]
      have hD : 0 ≤ denseClassicalMomentConstant := by
        norm_num [denseClassicalMomentConstant]
      unfold derivedRawTraceOneL3Constant
      nlinarith [mul_nonneg hD (sub_nonneg.mpr hpow)]

private theorem lpNorm_mul_le_of_holder_traceThree
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p q s : ENNReal} {f g : Omega → ℝ}
    (hf : MemLp f q mu) (hg : MemLp g p mu)
    [ENNReal.HolderTriple p q s] :
    lpNorm (fun omega ↦ g omega * f omega) s mu ≤
      lpNorm g p mu * lpNorm f q mu := by
  have hprod : MemLp (fun omega ↦ g omega * f omega) s mu := hf.mul' hg
  have he : eLpNorm (fun omega ↦ g omega * f omega) s mu ≤
      eLpNorm g p mu * eLpNorm f q mu := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := p) (q := q) (r := s)
      hg.aestronglyMeasurable hf.aestronglyMeasurable
      (fun x y : ℝ ↦ x * y) 1 (by
        filter_upwards [] with omega
        simp [nnnorm_mul])
  rw [← toReal_eLpNorm hprod.aestronglyMeasurable,
    ← toReal_eLpNorm hg.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top hg.eLpNorm_ne_top hf.eLpNorm_ne_top) he

/-- Raw `(Tr Y)^3` is `L^1`, with its sharp dimensional order obtained by
Hölder from the preceding raw `L^3` estimate. -/
theorem betaPrimeYTraceOneCube_momentPackage_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u ^ 3) 1
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u ^ 3) 1
            (betaPrimeTraceFourLaw N K) ≤
          derivedRawTraceOneCubeConstant * (N : ℝ) ^ 6) := by
  let mu := betaPrimeTraceFourLaw N K
  let f := betaPrimeYTraceOne N K
  have hf : MemLp f 3 mu := by
    simpa only [f, mu] using betaPrimeYTraceOne_memLp_three_internal hN hgap
  let p32 : ENNReal := ((3 / 2 : NNReal) : ENNReal)
  letI : ENNReal.HolderTriple 3 3 p32 := by
    have h : NNReal.HolderTriple 3 3 (3 / 2) := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((3 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal)
        ((3 / 2 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  have hsq : MemLp (fun u ↦ f u * f u) p32 mu := hf.mul' hf
  have hsqNorm : lpNorm (fun u ↦ f u * f u) p32 mu ≤
      lpNorm f 3 mu * lpNorm f 3 mu :=
    lpNorm_mul_le_of_holder_traceThree hf hf
  letI : ENNReal.HolderTriple p32 3 1 := by
    have h : NNReal.HolderTriple (3 / 2) 3 1 := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((3 / 2 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal)
        ((1 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  have hcube : MemLp (fun u ↦ (f u * f u) * f u) 1 mu := hf.mul' hsq
  constructor
  · convert hcube using 1
    funext u
    simp only [f]
    ring
  · intro hdense
    have hfNorm : lpNorm f 3 mu ≤
        derivedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
      simpa only [f, mu] using
        betaPrimeYTraceOne_lpNorm_three_le_internal hN hdense
    have hbound0 : 0 ≤ derivedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
      have : 0 ≤ derivedRawTraceOneL3Constant := by
        norm_num [derivedRawTraceOneL3Constant, denseClassicalMomentConstant]
      positivity
    change lpNorm (fun u ↦ f u ^ 3) 1 mu ≤ _
    calc
      lpNorm (fun u ↦ f u ^ 3) 1 mu =
          lpNorm (fun u ↦ (f u * f u) * f u) 1 mu := by
        congr 1
        funext u
        ring
      _ ≤ lpNorm (fun u ↦ f u * f u) p32 mu * lpNorm f 3 mu :=
        lpNorm_mul_le_of_holder_traceThree hf hsq
      _ ≤ (lpNorm f 3 mu * lpNorm f 3 mu) * lpNorm f 3 mu := by
        exact mul_le_mul_of_nonneg_right hsqNorm lpNorm_nonneg
      _ ≤ ((derivedRawTraceOneL3Constant * (N : ℝ) ^ 2) *
            (derivedRawTraceOneL3Constant * (N : ℝ) ^ 2)) *
          (derivedRawTraceOneL3Constant * (N : ℝ) ^ 2) := by
        exact mul_le_mul
          (mul_le_mul hfNorm hfNorm lpNorm_nonneg hbound0)
          hfNorm lpNorm_nonneg (mul_nonneg hbound0 hbound0)
      _ = derivedRawTraceOneCubeConstant * (N : ℝ) ^ 6 := by
        unfold derivedRawTraceOneCubeConstant
        ring

/-! ## The five-monomial beta-prime remainder -/

def betaPrimeAveragedCenteredCubicTraceThreeRemainder
    (N K : ℕ) (u : Fin 4 → ℝ) : ℝ :=
  scalarAveragedCenteredCubicDensity (N : ℝ) (concreteCOEExponent N K)
    (betaPrimeYTraceOne N K u) (betaPrimeYTraceTwo N K u) 0

def derivedRawTraceThreeRemainderConstant : ℝ :=
  100 * derivedRawTraceOneCubeConstant +
    600 * derivedRawTraceProductConstant +
    600 * derivedPositiveRawTraceOneTwoConstant +
    1000 * derivedPositiveRawTraceTwoConstant +
    400 * derivedRawTraceOneConstant

theorem betaPrimeAveragedCenteredCubicTraceThreeRemainder_eq_lowerTracePolynomial
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    betaPrimeAveragedCenteredCubicTraceThreeRemainder N K =
      cubicTraceThreeRemainderCoeffCube (N : ℝ)
          (concreteCOEExponent N K) •
        (fun u ↦ betaPrimeYTraceOne N K u ^ 3) +
      cubicTraceThreeRemainderCoeffSquare (N : ℝ)
          (concreteCOEExponent N K) •
        (fun u ↦ betaPrimeYTraceOne N K u ^ 2) +
      cubicTraceThreeRemainderCoeffMixed (N : ℝ)
          (concreteCOEExponent N K) •
        (fun u ↦ betaPrimeYTraceOne N K u * betaPrimeYTraceTwo N K u) +
      cubicTraceThreeRemainderCoeffTwo (N : ℝ)
          (concreteCOEExponent N K) • betaPrimeYTraceTwo N K +
      cubicTraceThreeRemainderCoeffOne (N : ℝ)
          (concreteCOEExponent N K) • betaPrimeYTraceOne N K := by
  have hNr : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hN)
  have hc : concreteCOEExponent N K ≠ 0 := by
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  funext u
  simp only [betaPrimeAveragedCenteredCubicTraceThreeRemainder,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact scalarAveragedCenteredCubicDensity_zero_eq_lowerTracePolynomial
    hNr hc _ _

theorem betaPrimeAveragedCenteredCubicTraceThreeRemainder_memLp_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (betaPrimeAveragedCenteredCubicTraceThreeRemainder N K) 1
      (betaPrimeTraceFourLaw N K) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  let f1 := fun u ↦ betaPrimeYTraceOne N K u ^ 3
  let f2 := fun u ↦ betaPrimeYTraceOne N K u ^ 2
  let f3 := fun u ↦ betaPrimeYTraceOne N K u * betaPrimeYTraceTwo N K u
  let f4 := betaPrimeYTraceTwo N K
  let f5 := betaPrimeYTraceOne N K
  let a1 := cubicTraceThreeRemainderCoeffCube (N : ℝ)
    (concreteCOEExponent N K)
  let a2 := cubicTraceThreeRemainderCoeffSquare (N : ℝ)
    (concreteCOEExponent N K)
  let a3 := cubicTraceThreeRemainderCoeffMixed (N : ℝ)
    (concreteCOEExponent N K)
  let a4 := cubicTraceThreeRemainderCoeffTwo (N : ℝ)
    (concreteCOEExponent N K)
  let a5 := cubicTraceThreeRemainderCoeffOne (N : ℝ)
    (concreteCOEExponent N K)
  have hf1 : MemLp f1 1 mu := by
    simpa only [f1, mu] using
      (betaPrimeYTraceOneCube_momentPackage_internal hN hgap).1
  have hf2 : MemLp f2 1 mu := by
    simpa only [f2, mu] using
      betaPrimeYTraceOneSquare_memLp_one_proved_allDimensions hN hgap
  have hf3 : MemLp f3 1 mu := by
    simpa only [f3, mu] using
      (betaPrimeYTraceOneTwo_momentPackage_positive_internal hN hgap).1
  have hf4 : MemLp f4 1 mu := by
    simpa only [f4, mu] using
      betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap
  have hf5 : MemLp f5 1 mu := by
    simpa only [f5, mu] using
      betaPrimeYTraceOne_memLp_one_proved_allDimensions hN hgap
  rw [betaPrimeAveragedCenteredCubicTraceThreeRemainder_eq_lowerTracePolynomial
    hN hdense]
  change MemLp (a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4 + a5 • f5) 1 mu
  exact ((((hf1.const_smul a1).add (hf2.const_smul a2)).add
    (hf3.const_smul a3)).add (hf4.const_smul a4)).add
      (hf5.const_smul a5)

theorem betaPrimeAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeAveragedCenteredCubicTraceThreeRemainder N K) 1
        (betaPrimeTraceFourLaw N K) ≤
      derivedRawTraceThreeRemainderConstant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  let x : ℝ := N
  let c := concreteCOEExponent N K
  let f1 := fun u ↦ betaPrimeYTraceOne N K u ^ 3
  let f2 := fun u ↦ betaPrimeYTraceOne N K u ^ 2
  let f3 := fun u ↦ betaPrimeYTraceOne N K u * betaPrimeYTraceTwo N K u
  let f4 := betaPrimeYTraceTwo N K
  let f5 := betaPrimeYTraceOne N K
  let a1 := cubicTraceThreeRemainderCoeffCube x c
  let a2 := cubicTraceThreeRemainderCoeffSquare x c
  let a3 := cubicTraceThreeRemainderCoeffMixed x c
  let a4 := cubicTraceThreeRemainderCoeffTwo x c
  let a5 := cubicTraceThreeRemainderCoeffOne x c
  have hx : 1 ≤ x := by
    change (1 : ℝ) ≤ (N : ℝ)
    exact_mod_cast hN
  have hc : x ≤ c := by
    dsimp only [x, c]
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    nlinarith
  have hf1 : MemLp f1 1 mu := by
    simpa only [f1, mu] using
      (betaPrimeYTraceOneCube_momentPackage_internal hN hgap).1
  have hf2 : MemLp f2 1 mu := by
    simpa only [f2, mu] using
      betaPrimeYTraceOneSquare_memLp_one_proved_allDimensions hN hgap
  have hf3 : MemLp f3 1 mu := by
    simpa only [f3, mu] using
      (betaPrimeYTraceOneTwo_momentPackage_positive_internal hN hgap).1
  have hf4 : MemLp f4 1 mu := by
    simpa only [f4, mu] using
      betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap
  have hf5 : MemLp f5 1 mu := by
    simpa only [f5, mu] using
      betaPrimeYTraceOne_memLp_one_proved_allDimensions hN hgap
  have hf1Norm : lpNorm f1 1 mu ≤
      derivedRawTraceOneCubeConstant * x ^ 6 := by
    simpa only [f1, mu, x] using
      (betaPrimeYTraceOneCube_momentPackage_internal hN hgap).2 hdense
  have hf2Norm : lpNorm f2 1 mu ≤
      derivedRawTraceProductConstant * x ^ 4 := by
    simpa only [f2, mu, x] using
      betaPrimeYTraceOneSquare_lpNorm_one_le_proved_allDimensions hN hdense
  have hf3Norm : lpNorm f3 1 mu ≤
      derivedPositiveRawTraceOneTwoConstant * x ^ 5 := by
    simpa only [f3, mu, x] using
      (betaPrimeYTraceOneTwo_momentPackage_positive_internal hN hgap).2 hdense
  have hf4Norm : lpNorm f4 1 mu ≤
      derivedPositiveRawTraceTwoConstant * x ^ 3 := by
    simpa only [f4, mu, x] using
      betaPrimeYTraceTwo_lpNorm_one_le_positive_internal hN hdense
  have hf5Norm : lpNorm f5 1 mu ≤
      derivedRawTraceOneConstant * x ^ 2 := by
    simpa only [f5, mu, x] using
      betaPrimeYTraceOne_lpNorm_one_le_proved_allDimensions hN hdense
  have ha1 : |a1| ≤ 100 / x ^ 5 := by
    simpa only [a1] using cubicTraceThreeRemainderCoeffCube_abs_le hx hc
  have ha2 : |a2| ≤ 600 / x ^ 3 := by
    simpa only [a2] using cubicTraceThreeRemainderCoeffSquare_abs_le hx hc
  have ha3 : |a3| ≤ 600 / x ^ 4 := by
    simpa only [a3] using cubicTraceThreeRemainderCoeffMixed_abs_le hx hc
  have ha4 : |a4| ≤ 1000 / x ^ 2 := by
    simpa only [a4] using cubicTraceThreeRemainderCoeffTwo_abs_le hx hc
  have ha5 : |a5| ≤ 400 / x := by
    simpa only [a5] using cubicTraceThreeRemainderCoeffOne_abs_le hx hc
  have hC1 : 0 ≤ derivedRawTraceOneCubeConstant := by
    norm_num [derivedRawTraceOneCubeConstant, derivedRawTraceOneL3Constant,
      denseClassicalMomentConstant]
  have hC2 : 0 ≤ derivedRawTraceProductConstant := by
    norm_num [derivedRawTraceProductConstant, denseClassicalMomentConstant]
  have hC3 : 0 ≤ derivedPositiveRawTraceOneTwoConstant := by
    norm_num [derivedPositiveRawTraceOneTwoConstant,
      derivedPositiveRawTraceTwoL2Constant,
      derivedPositiveRawTraceTwoConstant, derivedRawTraceOneConstant,
      derivedRawTraceProductConstant, denseClassicalMomentConstant]
  have hC4 : 0 ≤ derivedPositiveRawTraceTwoConstant := by
    norm_num [derivedPositiveRawTraceTwoConstant,
      derivedRawTraceProductConstant, denseClassicalMomentConstant]
  have hC5 : 0 ≤ derivedRawTraceOneConstant := by
    norm_num [derivedRawTraceOneConstant, denseClassicalMomentConstant]
  have h12 : MemLp (a1 • f1 + a2 • f2) 1 mu :=
    (hf1.const_smul a1).add (hf2.const_smul a2)
  have h123 : MemLp (a1 • f1 + a2 • f2 + a3 • f3) 1 mu :=
    h12.add (hf3.const_smul a3)
  have h1234 : MemLp (a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4) 1 mu :=
    h123.add (hf4.const_smul a4)
  have htri :
      lpNorm (a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4 + a5 • f5) 1 mu ≤
        lpNorm (a1 • f1) 1 mu + lpNorm (a2 • f2) 1 mu +
          lpNorm (a3 • f3) 1 mu + lpNorm (a4 • f4) 1 mu +
            lpNorm (a5 • f5) 1 mu := by
    calc
      _ ≤ lpNorm (a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4) 1 mu +
          lpNorm (a5 • f5) 1 mu :=
        lpNorm_add_le h1234 (p := (1 : ENNReal)) (by norm_num)
      _ ≤ (lpNorm (a1 • f1 + a2 • f2 + a3 • f3) 1 mu +
            lpNorm (a4 • f4) 1 mu) + lpNorm (a5 • f5) 1 mu := by
        gcongr
        exact lpNorm_add_le h123 (p := (1 : ENNReal)) (by norm_num)
      _ ≤ ((lpNorm (a1 • f1 + a2 • f2) 1 mu + lpNorm (a3 • f3) 1 mu) +
            lpNorm (a4 • f4) 1 mu) + lpNorm (a5 • f5) 1 mu := by
        gcongr
        exact lpNorm_add_le h12 (p := (1 : ENNReal)) (by norm_num)
      _ ≤ (((lpNorm (a1 • f1) 1 mu + lpNorm (a2 • f2) 1 mu) +
            lpNorm (a3 • f3) 1 mu) + lpNorm (a4 • f4) 1 mu) +
            lpNorm (a5 • f5) 1 mu := by
        gcongr
        exact lpNorm_add_le (hf1.const_smul a1) (p := (1 : ENNReal))
          (by norm_num)
  rw [betaPrimeAveragedCenteredCubicTraceThreeRemainder_eq_lowerTracePolynomial
    hN hdense]
  change lpNorm (a1 • f1 + a2 • f2 + a3 • f3 + a4 • f4 + a5 • f5) 1 mu ≤ _
  calc
    _ ≤ lpNorm (a1 • f1) 1 mu + lpNorm (a2 • f2) 1 mu +
          lpNorm (a3 • f3) 1 mu + lpNorm (a4 • f4) 1 mu +
            lpNorm (a5 • f5) 1 mu := htri
    _ = |a1| * lpNorm f1 1 mu + |a2| * lpNorm f2 1 mu +
          |a3| * lpNorm f3 1 mu + |a4| * lpNorm f4 1 mu +
            |a5| * lpNorm f5 1 mu := by
      simp only [lpNorm_const_smul, coe_nnnorm, Real.norm_eq_abs]
    _ ≤ (100 / x ^ 5) * (derivedRawTraceOneCubeConstant * x ^ 6) +
          (600 / x ^ 3) * (derivedRawTraceProductConstant * x ^ 4) +
          (600 / x ^ 4) * (derivedPositiveRawTraceOneTwoConstant * x ^ 5) +
          (1000 / x ^ 2) * (derivedPositiveRawTraceTwoConstant * x ^ 3) +
          (400 / x) * (derivedRawTraceOneConstant * x ^ 2) := by
      have hx0 : 0 ≤ x := zero_le_one.trans hx
      exact add_le_add
        (add_le_add
          (add_le_add
            (add_le_add
              (mul_le_mul ha1 hf1Norm lpNorm_nonneg
                (by positivity))
              (mul_le_mul ha2 hf2Norm lpNorm_nonneg
                (by positivity)))
            (mul_le_mul ha3 hf3Norm lpNorm_nonneg
              (by positivity)))
          (mul_le_mul ha4 hf4Norm lpNorm_nonneg
            (by positivity)))
        (mul_le_mul ha5 hf5Norm lpNorm_nonneg
          (by positivity))
    _ = derivedRawTraceThreeRemainderConstant * x := by
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
      unfold derivedRawTraceThreeRemainderConstant
      field_simp [ne_of_gt hxpos]

/-! ## Transfer and normalization -/

theorem betaPrimeAveragedCenteredCubicTraceThreeRemainder_comp_traceVector
    (N K : ℕ) :
    betaPrimeAveragedCenteredCubicTraceThreeRemainder N K ∘
        concreteCOETracePowerVector 4 N K =
      concreteAveragedCenteredCubicTraceThreeRemainder N K := by
  funext A
  unfold betaPrimeAveragedCenteredCubicTraceThreeRemainder
    concreteAveragedCenteredCubicTraceThreeRemainder
  change scalarAveragedCenteredCubicDensity (N : ℝ)
      (concreteCOEExponent N K)
      (concreteBetaPrimeYTraceOne N K A)
      (concreteBetaPrimeYTraceTwo N K A) 0 = _
  rw [concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne,
    concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo]

theorem concreteAveragedCenteredCubicTraceThreeRemainder_memLp_one_lowerTrace_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteAveragedCenteredCubicTraceThreeRemainder N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have h2NK : 2 * N ≤ K := by omega
  have hpull := memLp_comp_concreteCOETracePowerVector hN h2NK
    (betaPrimeAveragedCenteredCubicTraceThreeRemainder_memLp_one_internal
      hN hdense)
  rw [betaPrimeAveragedCenteredCubicTraceThreeRemainder_comp_traceVector]
    at hpull
  exact hpull

theorem concreteAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteAveragedCenteredCubicTraceThreeRemainder N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      derivedRawTraceThreeRemainderConstant * (N : ℝ) := by
  have h2NK : 2 * N ≤ K := by omega
  have hmem :=
    betaPrimeAveragedCenteredCubicTraceThreeRemainder_memLp_one_internal
      hN hdense
  have hpull := lpNorm_comp_concreteCOETracePowerVector hN h2NK
    (p := (1 : ENNReal))
    hmem.aestronglyMeasurable
  rw [betaPrimeAveragedCenteredCubicTraceThreeRemainder_comp_traceVector]
    at hpull
  rw [hpull]
  exact betaPrimeAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_internal
    hN hdense

def derivedRawTraceThreeConstant : ℝ :=
  3 * derivedRawTraceThreeRemainderConstant / 4

/-- The sharp raw-third-trace package, proved from lower traces, total-mass
cancellation, and positivity.  In particular, this theorem does not use
`betaPrimeYTraceThree_momentPackage_external`. -/
theorem betaPrimeYTraceThree_momentPackage_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceThree N K) 1 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (betaPrimeYTraceThree N K) 1
            (betaPrimeTraceFourLaw N K) ≤
          derivedRawTraceThreeConstant * (N : ℝ) ^ 4) := by
  constructor
  · exact betaPrimeYTraceThree_memLp_one_positive_internal hN hgap
  · intro hdense
    have h2NK : 2 * N ≤ K := by omega
    have hconcrete := concreteCOETraceThree_lpNorm_one_le_of_remainder
      hN hdense
      (concreteAveragedCenteredCubicTraceThreeRemainder_memLp_one_lowerTrace_internal
        hN hdense)
      (concreteAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_internal
        hN hdense)
    have htransport := lpNorm_comp_concreteCOETracePowerVector hN h2NK
      (p := (1 : ENNReal))
      (betaPrimeYTraceThree_memLp_one_positive_internal hN hgap).aestronglyMeasurable
    have hfun : betaPrimeYTraceThree N K ∘
        concreteCOETracePowerVector 4 N K = concreteCOETraceThree N K := by
      funext A
      change concreteBetaPrimeYTraceThree N K A = concreteCOETraceThree N K A
      exact concreteBetaPrimeYTraceThree_eq_concreteCOETraceThree N K A
    rw [hfun] at htransport
    rw [← htransport]
    simpa only [derivedRawTraceThreeConstant] using hconcrete

theorem betaPrimeYTraceThree_memLp_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceThree N K) 1 (betaPrimeTraceFourLaw N K) :=
  (betaPrimeYTraceThree_momentPackage_internal hN hgap).1

theorem betaPrimeYTraceThree_lpNorm_one_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceThree N K) 1
        (betaPrimeTraceFourLaw N K) ≤
      derivedRawTraceThreeConstant * (N : ℝ) ^ 4 :=
  (betaPrimeYTraceThree_momentPackage_internal hN (by omega)).2 hdense

theorem concreteCOETraceThree_memLp_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCOETraceThree N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have hpull := memLp_comp_concreteCOETracePowerVector hN (by omega)
    (betaPrimeYTraceThree_memLp_one_internal hN hgap)
  have hfun : betaPrimeYTraceThree N K ∘
      concreteCOETracePowerVector 4 N K = concreteCOETraceThree N K := by
    funext A
    change concreteBetaPrimeYTraceThree N K A = concreteCOETraceThree N K A
    exact concreteBetaPrimeYTraceThree_eq_concreteCOETraceThree N K A
  rw [hfun] at hpull
  exact hpull

theorem concreteCOETraceThree_lpNorm_one_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCOETraceThree N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      derivedRawTraceThreeConstant * (N : ℝ) ^ 4 := by
  exact concreteCOETraceThree_lpNorm_one_le_of_remainder hN hdense
    (concreteAveragedCenteredCubicTraceThreeRemainder_memLp_one_lowerTrace_internal
      hN hdense)
    (concreteAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_internal
      hN hdense)

/-! ## A closed centered cubic bound using the new raw-third package -/

theorem averagedCenteredCubicTraceThreeCoefficient_abs_le
    {n c : ℝ} (hn : 1 ≤ n) (hc : n ≤ c) (hc4 : 4 ≤ c) :
    |averagedCenteredCubicTraceThreeCoefficient n c| ≤ 600 / n ^ 3 := by
  have hnpos : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hcpos : 0 < c := hnpos.trans_le hc
  have hdenpos : 0 < cubicTraceThreeRemainderDenominator n c := by
    unfold cubicTraceThreeRemainderDenominator
    positivity
  have hden := cubicTraceThreeRemainderDenominator_lower_bound hn hc
  have halpha0 : 0 ≤ averagedCenteredCubicTraceThreeCoefficient n c := by
    have hlower := averagedCenteredCubicTraceThreeCoefficient_lower_bound hn hc4
    exact (by positivity : 0 ≤ 4 / (3 * n ^ 3)).trans hlower
  have hbase0 : 0 ≤ n ^ 2 * c ^ 2 :=
    mul_nonneg (sq_nonneg n) (sq_nonneg c)
  have hn2_le : n ^ 2 ≤ n ^ 2 * c ^ 2 := by
    have hc2 : 1 ≤ c ^ 2 := by nlinarith [sq_nonneg (c - 1)]
    calc
      n ^ 2 = n ^ 2 * 1 := by ring
      _ ≤ n ^ 2 * c ^ 2 := by gcongr
  have hnc_le : n * c ≤ n ^ 2 * c ^ 2 := by
    have hn_sq : n ≤ n ^ 2 := by
      nlinarith [mul_nonneg (zero_le_one.trans hn) (sub_nonneg.mpr hn)]
    have hc_sq : c ≤ c ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ c by positivity)
        (sub_nonneg.mpr (show 1 ≤ c by linarith))]
    calc
      n * c ≤ n ^ 2 * c := by gcongr
      _ ≤ n ^ 2 * c ^ 2 := by gcongr
  have hone_le : 1 ≤ n ^ 2 * c ^ 2 := by
    have hn2 : 1 ≤ n ^ 2 := by nlinarith [sq_nonneg (n - 1)]
    have hc2 : 1 ≤ c ^ 2 := by nlinarith [sq_nonneg (c - 1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr hc2)]
  rw [abs_of_nonneg halpha0]
  unfold averagedCenteredCubicTraceThreeCoefficient
  change 16 * (n ^ 2 * (c ^ 2 - 3 * c + 4) +
      12 * n * (c - 1) + 16) /
      cubicTraceThreeRemainderDenominator n c ≤ 600 / n ^ 3
  rw [div_le_iff₀ hdenpos]
  calc
    16 * (n ^ 2 * (c ^ 2 - 3 * c + 4) +
        12 * n * (c - 1) + 16) ≤
        576 * (n ^ 2 * c ^ 2) := by nlinarith
    _ ≤ 600 * (n ^ 2 * c ^ 2) := by nlinarith
    _ = (600 / n ^ 3) * (n ^ 5 * c ^ 2) := by
      field_simp [ne_of_gt hnpos]
    _ ≤ (600 / n ^ 3) * cubicTraceThreeRemainderDenominator n c := by
      exact mul_le_mul_of_nonneg_left hden (by positivity)

theorem concreteAveragedCenteredCubicTraceThreeCoefficient_abs_le
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    |averagedCenteredCubicTraceThreeCoefficient (N : ℝ)
        (concreteCOEExponent N K)| ≤ 600 / (N : ℝ) ^ 3 := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hcN : (N : ℝ) ≤ concreteCOEExponent N K := by
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    nlinarith
  have hc4 : (4 : ℝ) ≤ concreteCOEExponent N K := by
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    nlinarith
  exact averagedCenteredCubicTraceThreeCoefficient_abs_le hNr hcN hc4

def concreteAveragedCenteredCubicNormalizationConstant : ℝ :=
  600 * derivedRawTraceThreeConstant + derivedRawTraceThreeRemainderConstant

theorem concreteAveragedCenteredCubicDensity_memLp_one_normalization_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteAveragedCenteredCubicDensity N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let alpha := averagedCenteredCubicTraceThreeCoefficient (N : ℝ)
    (concreteCOEExponent N K)
  let tThree := concreteCOETraceThree N K
  let rem := concreteAveragedCenteredCubicTraceThreeRemainder N K
  have ht : MemLp tThree 1 mu := by
    simpa only [tThree, mu] using
      concreteCOETraceThree_memLp_one_internal hN (by omega)
  have hr : MemLp rem 1 mu := by
    simpa only [rem, mu] using
      concreteAveragedCenteredCubicTraceThreeRemainder_memLp_one_lowerTrace_internal
        hN hdense
  have heq : concreteAveragedCenteredCubicDensity N K =
      alpha • tThree + rem := by
    funext A
    simp only [alpha, tThree, rem, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact concreteAveragedCenteredCubicDensity_extract_traceThree hN hdense A
  rw [heq]
  exact (ht.const_smul alpha).add hr

theorem concreteAveragedCenteredCubicDensity_lpNorm_one_le_normalization_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteAveragedCenteredCubicDensity N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      concreteAveragedCenteredCubicNormalizationConstant * (N : ℝ) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let x : ℝ := N
  let alpha := averagedCenteredCubicTraceThreeCoefficient x
    (concreteCOEExponent N K)
  let tThree := concreteCOETraceThree N K
  let rem := concreteAveragedCenteredCubicTraceThreeRemainder N K
  have hx : 1 ≤ x := by
    change (1 : ℝ) ≤ (N : ℝ)
    exact_mod_cast hN
  have ht : MemLp tThree 1 mu := by
    simpa only [tThree, mu] using
      concreteCOETraceThree_memLp_one_internal hN (by omega)
  have hr : MemLp rem 1 mu := by
    simpa only [rem, mu] using
      concreteAveragedCenteredCubicTraceThreeRemainder_memLp_one_lowerTrace_internal
        hN hdense
  have htNorm : lpNorm tThree 1 mu ≤
      derivedRawTraceThreeConstant * x ^ 4 := by
    simpa only [tThree, mu, x] using
      concreteCOETraceThree_lpNorm_one_le_internal hN hdense
  have hrNorm : lpNorm rem 1 mu ≤
      derivedRawTraceThreeRemainderConstant * x := by
    simpa only [rem, mu, x] using
      concreteAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_internal
        hN hdense
  have halpha : |alpha| ≤ 600 / x ^ 3 := by
    simpa only [alpha, x] using
      concreteAveragedCenteredCubicTraceThreeCoefficient_abs_le hN hdense
  have heq : concreteAveragedCenteredCubicDensity N K =
      alpha • tThree + rem := by
    funext A
    simp only [alpha, tThree, rem, x, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact concreteAveragedCenteredCubicDensity_extract_traceThree hN hdense A
  rw [heq]
  calc
    lpNorm (alpha • tThree + rem) 1 mu ≤
        lpNorm (alpha • tThree) 1 mu + lpNorm rem 1 mu :=
      lpNorm_add_le (ht.const_smul alpha) (p := (1 : ENNReal)) (by norm_num)
    _ = |alpha| * lpNorm tThree 1 mu + lpNorm rem 1 mu := by
      rw [lpNorm_const_smul]
      simp only [coe_nnnorm, Real.norm_eq_abs]
    _ ≤ (600 / x ^ 3) *
          (derivedRawTraceThreeConstant * x ^ 4) +
        derivedRawTraceThreeRemainderConstant * x := by
      exact add_le_add
        (mul_le_mul halpha htNorm lpNorm_nonneg (by positivity)) hrNorm
    _ = concreteAveragedCenteredCubicNormalizationConstant * x := by
      have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
      unfold concreteAveragedCenteredCubicNormalizationConstant
      field_simp [ne_of_gt hxpos]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
