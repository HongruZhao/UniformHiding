import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredCubicTraceClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MixedScalarQuadraticClosure
import Mathlib.Tactic

/-!
# The raw third-trace coefficient in the averaged centered cubic density

This file is pure scalar algebra.  It expands the three pieces in the
centered cubic polarization and isolates the coefficient of the literal
`Tr Y^3` variable.  No probability law or moment estimate occurs here.

The resulting positive coefficient is the algebraic starting point for a
possible normalization-based derivation of the raw third-trace first moment.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- `Tr S`, where `S = Y - (N+1)I`, in scalar trace coordinates. -/
def scalarCenteredTraceOne (N tOne : ℝ) : ℝ :=
  tOne - N * (N + 1)

/-- `Tr S²` in scalar trace coordinates. -/
def scalarCenteredTraceTwo (N tOne tTwo : ℝ) : ℝ :=
  tTwo - 2 * (N + 1) * tOne + N * (N + 1) ^ 2

/-- `Tr S³` in scalar trace coordinates. -/
def scalarCenteredTraceThree (N tOne tTwo tThree : ℝ) : ℝ :=
  tThree - 3 * (N + 1) * tTwo + 3 * (N + 1) ^ 2 * tOne -
    N * (N + 1) ^ 3

/-- The closed rank-one cubic density, written only in the three raw traces. -/
def scalarAveragedRankOneCubicDensity
    (N c tOne tTwo tThree : ℝ) : ℝ :=
  let sOne := scalarCenteredTraceOne N tOne
  let sTwo := scalarCenteredTraceTwo N tOne tTwo
  let sThree := scalarCenteredTraceThree N tOne tTwo tThree
  let meanS := sOne / N
  let meanSSquare := (sOne ^ 2 + sTwo) / (N * (N + 1))
  let meanSCube := (sOne ^ 3 + 3 * sOne * sTwo + 2 * sThree) /
    (N * (N + 1) * (N + 2))
  let traceZW := tOne / c + tTwo / c ^ 2
  let traceZTraceZW := tOne ^ 2 / c ^ 2 + (tOne * tTwo) / c ^ 3
  let traceZTwoW := tTwo / c ^ 2 + tThree / c ^ 3
  averagedCubicNonWExpression N c meanS meanSSquare meanSCube +
    averagedCubicWTraceExpression N c traceZW traceZTraceZW traceZTwoW

/-- The mixed scalar--quadratic density in the same raw trace coordinates. -/
def scalarMixedScalarQuadraticDensity
    (N c tOne tTwo tThree : ℝ) : ℝ :=
  let sOne := scalarCenteredTraceOne N tOne
  let quadraticDensity := 4 / (N * (N + 1)) *
    centeredQuadraticTraceBracket N c tOne tTwo
  let derivativeDensity := 4 / (N * (N + 1)) *
    centralDerivativeQuadraticTraceBracket N c tOne tTwo tThree
  (2 * sOne) * quadraticDensity - derivativeDensity

/-- The third scalar density score in raw trace coordinates. -/
def scalarCentralDensityScoreThree
    (N c tOne tTwo tThree : ℝ) : ℝ :=
  let sOne := scalarCenteredTraceOne N tOne
  8 * sOne ^ 3 - 48 * (sOne * tOne) -
    (48 / c) * (sOne * tTwo) + 32 * tOne +
    (96 / c) * tTwo + (64 / c ^ 2) * tThree

/-- The exact scalar trace polynomial represented by the averaged centered
third density. -/
def scalarAveragedCenteredCubicDensity
    (N c tOne tTwo tThree : ℝ) : ℝ :=
  scalarAveragedRankOneCubicDensity N c tOne tTwo tThree -
    (3 / N) * scalarMixedScalarQuadraticDensity N c tOne tTwo tThree -
    (1 / N ^ 3) * scalarCentralDensityScoreThree N c tOne tTwo tThree

/-- Exact coefficient of the literal raw `Tr Y³` variable. -/
def averagedCenteredCubicTraceThreeCoefficient (N c : ℝ) : ℝ :=
  16 * (N ^ 2 * (c ^ 2 - 3 * c + 4) +
      12 * N * (c - 1) + 16) /
    (N ^ 3 * (N + 1) * (N + 2) * c ^ 2)

/-- The averaged centered cubic trace polynomial is affine in `Tr Y³`,
with the displayed coefficient. -/
theorem scalarAveragedCenteredCubicDensity_extract_traceThree
    {N c : ℝ} (hN : N ≠ 0) (hNpOne : N + 1 ≠ 0)
    (hNpTwo : N + 2 ≠ 0) (hc : c ≠ 0)
    (tOne tTwo tThree : ℝ) :
    scalarAveragedCenteredCubicDensity N c tOne tTwo tThree =
      averagedCenteredCubicTraceThreeCoefficient N c * tThree +
        scalarAveragedCenteredCubicDensity N c tOne tTwo 0 := by
  simp only [scalarAveragedCenteredCubicDensity,
    scalarAveragedRankOneCubicDensity, scalarMixedScalarQuadraticDensity,
    scalarCentralDensityScoreThree, scalarCenteredTraceOne,
    scalarCenteredTraceTwo, scalarCenteredTraceThree,
    averagedCenteredCubicTraceThreeCoefficient,
    averagedCubicNonWExpression, averagedCubicWTraceExpression,
    cubicTraceCoefficientThree, cubicTraceCoefficientTwo,
    cubicTraceCoefficientOne, cubicTraceCoefficientZero,
    centeredQuadraticTraceBracket, centralDerivativeQuadraticTraceBracket,
    centralTraceOneDerivative, centralTraceTwoDerivative,
    quadraticTraceCoeffTwo, quadraticTraceCoeffSquare,
    quadraticTraceCoeffOne]
  field_simp [hN, hNpOne, hNpTwo, hc]
  ring

/-- In the dense scalar range the raw-third-trace coefficient has the
dimension-sharp lower bound `4 / (3 N³)`. -/
theorem averagedCenteredCubicTraceThreeCoefficient_lower_bound
    {N c : ℝ} (hN : 1 ≤ N) (hc : 4 ≤ c) :
    4 / (3 * N ^ 3) ≤ averagedCenteredCubicTraceThreeCoefficient N c := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hcpos : 0 < c := lt_of_lt_of_le (by norm_num) hc
  have hNpOne : 0 < N + 1 := by linarith
  have hNpTwo : 0 < N + 2 := by linarith
  have hpoly : c ^ 2 / 2 ≤ c ^ 2 - 3 * c + 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr (by linarith : 2 ≤ c))
      (sub_nonneg.mpr hc)]
  have hrest : 0 ≤ 12 * N * (c - 1) + 16 := by
    have : 0 ≤ c - 1 := by linarith
    positivity
  have hnum : N ^ 2 * c ^ 2 / 2 ≤
      N ^ 2 * (c ^ 2 - 3 * c + 4) + 12 * N * (c - 1) + 16 := by
    have hsquare : 0 ≤ N ^ 2 := sq_nonneg N
    have := mul_le_mul_of_nonneg_left hpoly hsquare
    nlinarith
  have hdenpos : 0 < N ^ 3 * (N + 1) * (N + 2) * c ^ 2 := by positivity
  have hfirst :
      8 / (N * (N + 1) * (N + 2)) ≤
        averagedCenteredCubicTraceThreeCoefficient N c := by
    unfold averagedCenteredCubicTraceThreeCoefficient
    rw [div_le_div_iff₀ (by positivity : 0 < N * (N + 1) * (N + 2))
      hdenpos]
    have hc2 : 0 < c ^ 2 := sq_pos_of_pos hcpos
    have hscaled := mul_le_mul_of_nonneg_left hnum (by norm_num : (0 : ℝ) ≤ 16)
    field_simp [ne_of_gt hNpos, ne_of_gt hcpos]
    nlinarith
  calc
    4 / (3 * N ^ 3) ≤ 8 / (N * (N + 1) * (N + 2)) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 3 * N ^ 3)
        (by positivity : 0 < N * (N + 1) * (N + 2))]
      nlinarith [mul_nonneg (sub_nonneg.mpr hN) (sq_nonneg N)]
    _ ≤ averagedCenteredCubicTraceThreeCoefficient N c := hfirst

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
