import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10_ExactTraceRecurrenceAlgebra
import Mathlib.Tactic

/-!
# Exact raw fourth-source algebra for H12

The H8/H10 ten-moment solver already determines the two uncentered Wick
polynomials needed by H12.  This foundations-only module records their exact
rational forms and proves the dense-regime integer ceiling `1218`.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

set_option maxHeartbeats 7200000
set_option maxRecDepth 100000

/-- Raw fourth moment of the first Gaussian-source trace, expressed through
the five degree-four denominator moments. -/
def h12TraceOneRawFourthRecurrenceMoment
    (n x4 x2y y2 xz q : ℝ) : ℝ :=
  (n + 1) ^ 4 * x4 +
    12 * (n + 1) ^ 3 * x2y +
    12 * (n + 1) ^ 2 * y2 +
    32 * (n + 1) ^ 2 * xz +
    48 * (n + 1) * q

/-- Raw square moment of the second Gaussian-source trace. -/
def h12TraceTwoRawSquareRecurrenceMoment
    (n x4 x2y y2 xz q : ℝ) : ℝ :=
  (n + 1) ^ 2 * x4 +
    (2 * (n + 1) ^ 3 + 2 * (n + 1) ^ 2 + 8 * (n + 1)) * x2y +
    ((n + 1) ^ 4 + 2 * (n + 1) ^ 3 +
      5 * (n + 1) ^ 2 + 4 * (n + 1)) * y2 +
    16 * (n + 1) * (n + 2) * xz +
    (8 * (n + 1) ^ 3 + 20 * (n + 1) ^ 2 + 20 * (n + 1)) * q

def h12TraceOneRawMeanRecurrenceMoment (n x2 y : ℝ) : ℝ :=
  (n + 1) ^ 2 * x2 + 2 * (n + 1) * y

def h12TraceTwoRawMeanRecurrenceMoment (n x2 y : ℝ) : ℝ :=
  (n + 1) * (n + 2) * y + (n + 1) * x2

/-- Numerator of the exact first raw mean over the degree-two denominator. -/
def h12TraceOneRawMeanNumerator (n c : ℝ) : ℝ :=
  (n + 1) ^ 2 * (c * ((c - 1) * n ^ 2 + 2 * n)) +
    2 * (n + 1) * (c * n * (c + n))

/-- Numerator of the exact second raw mean over the degree-two denominator. -/
def h12TraceTwoRawMeanNumerator (n c : ℝ) : ℝ :=
  (n + 1) * (n + 2) * (c * n * (c + n)) +
    (n + 1) * (c * ((c - 1) * n ^ 2 + 2 * n))

/-- Quotient left after cancelling the square of the degree-two denominator
from the common degree-four denominator. -/
def h12RawMeanDenominatorQuotient (c : ℝ) : ℝ :=
  (c + 3) * (c + 2) * (c - 1) * (c - 4) * (c - 6)

/-- Exact numerator of the first raw fourth source moment. -/
def h12TraceOneRawFourthNumerator (n c : ℝ) : ℝ :=
  h8ExactVarianceNumerator n c +
    h12RawMeanDenominatorQuotient c *
      h12TraceOneRawMeanNumerator n c ^ 2

/-- Exact numerator of the second raw square source moment. -/
def h12TraceTwoRawSquareNumerator (n c : ℝ) : ℝ :=
  h10ExactVarianceNumerator n c +
    h12RawMeanDenominatorQuotient c *
      h12TraceTwoRawMeanNumerator n c ^ 2

theorem h12TraceOneRawMeanRecurrenceMoment_eq_exact
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceOneRawMeanRecurrenceMoment n x2 y =
      h12TraceOneRawMeanNumerator n c /
        h8H10DegreeTwoDenominator c := by
  obtain ⟨hc, h2, h3, h4⟩ :=
    h8H10_traceRecurrence_denominators_ne_zero_of_dense hn hdense
  obtain ⟨hx2, hy, _⟩ :=
    h8H10ExactTraceRecurrenceSystem_solver h hc h2 h3 h4
  rw [hx2, hy]
  unfold h12TraceOneRawMeanRecurrenceMoment
    h12TraceOneRawMeanNumerator h8H10SolvedX2 h8H10SolvedY
  field_simp [h2]

theorem h12TraceTwoRawMeanRecurrenceMoment_eq_exact
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceTwoRawMeanRecurrenceMoment n x2 y =
      h12TraceTwoRawMeanNumerator n c /
        h8H10DegreeTwoDenominator c := by
  obtain ⟨hc, h2, h3, h4⟩ :=
    h8H10_traceRecurrence_denominators_ne_zero_of_dense hn hdense
  obtain ⟨hx2, hy, _⟩ :=
    h8H10ExactTraceRecurrenceSystem_solver h hc h2 h3 h4
  rw [hx2, hy]
  unfold h12TraceTwoRawMeanRecurrenceMoment
    h12TraceTwoRawMeanNumerator h8H10SolvedX2 h8H10SolvedY
  field_simp [h2]

theorem h12TraceOneRawFourthRecurrenceMoment_eq_exact
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceOneRawFourthRecurrenceMoment n x4 x2y y2 xz q =
      h12TraceOneRawFourthNumerator n c /
        h8H10CommonVarianceDenominator c := by
  obtain ⟨hc, h2, h3, h4⟩ :=
    h8H10_traceRecurrence_denominators_ne_zero_of_dense hn hdense
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hn hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  have hvar := h8_exact_variance_identity_of_traceRecurrences_dense h hn hdense
  have hmean := h12TraceOneRawMeanRecurrenceMoment_eq_exact h hn hdense
  calc
    h12TraceOneRawFourthRecurrenceMoment n x4 x2y y2 xz q =
        h8TraceRecurrenceVariance n x2 y x4 x2y y2 xz q +
          h12TraceOneRawMeanRecurrenceMoment n x2 y ^ 2 := by
      unfold h12TraceOneRawFourthRecurrenceMoment
        h8TraceRecurrenceVariance h12TraceOneRawMeanRecurrenceMoment
      ring
    _ = h8ExactVarianceNumerator n c /
          h8H10CommonVarianceDenominator c +
        (h12TraceOneRawMeanNumerator n c /
          h8H10DegreeTwoDenominator c) ^ 2 := by rw [hvar, hmean]
    _ = h12TraceOneRawFourthNumerator n c /
          h8H10CommonVarianceDenominator c := by
      unfold h12TraceOneRawFourthNumerator
      field_simp [h2, ne_of_gt hdenPos]
      unfold h12RawMeanDenominatorQuotient h8H10CommonVarianceDenominator
        h8H10DegreeTwoDenominator
      ring

theorem h12TraceTwoRawSquareRecurrenceMoment_eq_exact
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceTwoRawSquareRecurrenceMoment n x4 x2y y2 xz q =
      h12TraceTwoRawSquareNumerator n c /
        h8H10CommonVarianceDenominator c := by
  obtain ⟨hc, h2, h3, h4⟩ :=
    h8H10_traceRecurrence_denominators_ne_zero_of_dense hn hdense
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hn hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  have hvar := h10_exact_variance_identity_of_traceRecurrences_dense h hn hdense
  have hmean := h12TraceTwoRawMeanRecurrenceMoment_eq_exact h hn hdense
  calc
    h12TraceTwoRawSquareRecurrenceMoment n x4 x2y y2 xz q =
        h10TraceRecurrenceVariance n x2 y x4 x2y y2 xz q +
          h12TraceTwoRawMeanRecurrenceMoment n x2 y ^ 2 := by
      unfold h12TraceTwoRawSquareRecurrenceMoment
        h10TraceRecurrenceVariance h12TraceTwoRawMeanRecurrenceMoment
      ring
    _ = h10ExactVarianceNumerator n c /
          h8H10CommonVarianceDenominator c +
        (h12TraceTwoRawMeanNumerator n c /
          h8H10DegreeTwoDenominator c) ^ 2 := by rw [hvar, hmean]
    _ = h12TraceTwoRawSquareNumerator n c /
          h8H10CommonVarianceDenominator c := by
      unfold h12TraceTwoRawSquareNumerator
      field_simp [h2, ne_of_gt hdenPos]
      unfold h12RawMeanDenominatorQuotient h8H10CommonVarianceDenominator
        h8H10DegreeTwoDenominator
      ring

/-- The exact raw first-source numerator is below the integer ceiling `1218`.
After `n=1+x`, `c=13(1+x)+y`, the cleared difference has only nonnegative
coefficients. -/
theorem h12TraceOneRawFourthNumerator_le_1218_dense
    {n c : ℝ} (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceOneRawFourthNumerator n c ≤
      1218 * n ^ 8 * h8H10CommonVarianceDenominator c := by
  let x := n - 1
  let y := c - 13 * n
  have hx : 0 ≤ x := by dsimp only [x]; linarith
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hnRep : n = x + 1 := by dsimp only [x]; ring
  have hcRep : c = y + 13 * (x + 1) := by dsimp only [x, y]; ring
  have hcert : 0 ≤
      1218 * n ^ 8 * h8H10CommonVarianceDenominator c -
        h12TraceOneRawFourthNumerator n c := by
    rw [hnRep, hcRep]
    unfold h12TraceOneRawFourthNumerator h12TraceOneRawMeanNumerator
      h12RawMeanDenominatorQuotient h8ExactVarianceNumerator
      h8H10CommonVarianceDenominator
    ring_nf
    positivity
  linarith

/-- The exact raw second-source numerator obeys the same integer ceiling. -/
theorem h12TraceTwoRawSquareNumerator_le_1218_dense
    {n c : ℝ} (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceTwoRawSquareNumerator n c ≤
      1218 * n ^ 6 * h8H10CommonVarianceDenominator c := by
  let x := n - 1
  let y := c - 13 * n
  have hx : 0 ≤ x := by dsimp only [x]; linarith
  have hy : 0 ≤ y := by dsimp only [y]; linarith
  have hnRep : n = x + 1 := by dsimp only [x]; ring
  have hcRep : c = y + 13 * (x + 1) := by dsimp only [x, y]; ring
  have hcert : 0 ≤
      1218 * n ^ 6 * h8H10CommonVarianceDenominator c -
        h12TraceTwoRawSquareNumerator n c := by
    rw [hnRep, hcRep]
    unfold h12TraceTwoRawSquareNumerator h12TraceTwoRawMeanNumerator
      h12RawMeanDenominatorQuotient h10ExactVarianceNumerator
      h8H10CommonVarianceDenominator
    ring_nf
    positivity
  linarith

/-! ## Dimension-at-least-two refinements

The projective part of H12 vanishes in dimension one.  Starting at dimension
two, the same exact rational functions have much smaller integer ceilings.
Writing `n = 2 + e` and `c = 13 * (2 + e) + d` turns each cleared difference
below into a polynomial with nonnegative coefficients.
-/

/-- Optimal coefficient-positive integer ceiling for the first raw fourth
source moment when `n >= 2`. -/
theorem h12TraceOneRawFourthNumerator_le_34_dense
    {n c : ℝ} (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceOneRawFourthNumerator n c ≤
      34 * n ^ 8 * h8H10CommonVarianceDenominator c := by
  let e : ℝ := n - 2
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnRep : n = 2 + e := by dsimp only [e]; ring
  have hcRep : c = 13 * (2 + e) + d := by dsimp only [e, d]; ring
  rw [hnRep, hcRep]
  unfold h12TraceOneRawFourthNumerator h12TraceOneRawMeanNumerator
    h12RawMeanDenominatorQuotient h8ExactVarianceNumerator
    h8H10CommonVarianceDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- Exact degree-two first raw mean ceiling used by the sharpened H8/H13
packages. -/
theorem h12TraceOneRawMeanNumerator_le_4_dense
    {n c : ℝ} (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceOneRawMeanNumerator n c ≤
      4 * n ^ 4 * h8H10DegreeTwoDenominator c := by
  let e : ℝ := n - 2
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnRep : n = 2 + e := by dsimp only [e]; ring
  have hcRep : c = 13 * (2 + e) + d := by dsimp only [e, d]; ring
  rw [hnRep, hcRep]
  unfold h12TraceOneRawMeanNumerator h8H10DegreeTwoDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- Exact degree-two second raw mean ceiling used by the sharpened H10/H14
packages. -/
theorem h12TraceTwoRawMeanNumerator_le_5_dense
    {n c : ℝ} (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceTwoRawMeanNumerator n c ≤
      5 * n ^ 3 * h8H10DegreeTwoDenominator c := by
  let e : ℝ := n - 2
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnRep : n = 2 + e := by dsimp only [e]; ring
  have hcRep : c = 13 * (2 + e) + d := by dsimp only [e, d]; ring
  rw [hnRep, hcRep]
  unfold h12TraceTwoRawMeanNumerator h8H10DegreeTwoDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- Optimal coefficient-positive integer ceiling for the second raw square
source moment when `n >= 2`. -/
theorem h12TraceTwoRawSquareNumerator_le_88_dense
    {n c : ℝ} (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceTwoRawSquareNumerator n c ≤
      88 * n ^ 6 * h8H10CommonVarianceDenominator c := by
  let e : ℝ := n - 2
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnRep : n = 2 + e := by dsimp only [e]; ring
  have hcRep : c = 13 * (2 + e) + d := by dsimp only [e, d]; ring
  rw [hnRep, hcRep]
  unfold h12TraceTwoRawSquareNumerator h12TraceTwoRawMeanNumerator
    h12RawMeanDenominatorQuotient h10ExactVarianceNumerator
    h8H10CommonVarianceDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- The projective factor `(n-1)^2/n^2` lowers the raw second-trace square
constant from `88` to `22`.  The statement is kept at numerator level so it
can be reused without any probabilistic input. -/
theorem h12TraceTwoRawSquareNumerator_projective_le_22_dense
    {n c : ℝ} (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    (n - 1) ^ 2 * h12TraceTwoRawSquareNumerator n c ≤
      22 * n ^ 8 * h8H10CommonVarianceDenominator c := by
  let e : ℝ := n - 2
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnRep : n = 2 + e := by dsimp only [e]; ring
  have hcRep : c = 13 * (2 + e) + d := by dsimp only [e, d]; ring
  rw [hnRep, hcRep]
  unfold h12TraceTwoRawSquareNumerator h12TraceTwoRawMeanNumerator
    h12RawMeanDenominatorQuotient h10ExactVarianceNumerator
    h8H10CommonVarianceDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- Direct integer optimization of the complete H12 coefficient.  Keeping
the fixed-sphere factor `144` inside the exact polynomial certificate lowers
`144 * 22 = 3168` to `3151`. -/
theorem h12TraceTwoRawSquareNumerator_projective_144_le_3151_dense
    {n c : ℝ} (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    144 * (n - 1) ^ 2 * h12TraceTwoRawSquareNumerator n c ≤
      3151 * n ^ 8 * h8H10CommonVarianceDenominator c := by
  let e : ℝ := n - 2
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnRep : n = 2 + e := by dsimp only [e]; ring
  have hcRep : c = 13 * (2 + e) + d := by dsimp only [e, d]; ring
  rw [hnRep, hcRep]
  unfold h12TraceTwoRawSquareNumerator h12TraceTwoRawMeanNumerator
    h12RawMeanDenominatorQuotient h10ExactVarianceNumerator
    h8H10CommonVarianceDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

theorem h12TraceOneRawFourthRecurrenceMoment_le_1218_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceOneRawFourthRecurrenceMoment n x4 x2y y2 xz q ≤
      1218 * n ^ 8 := by
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hn hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  rw [h12TraceOneRawFourthRecurrenceMoment_eq_exact h hn hdense]
  exact (div_le_iff₀ hdenPos).2
    (h12TraceOneRawFourthNumerator_le_1218_dense hn hdense)

theorem h12TraceTwoRawSquareRecurrenceMoment_le_1218_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceTwoRawSquareRecurrenceMoment n x4 x2y y2 xz q ≤
      1218 * n ^ 6 := by
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hn hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  rw [h12TraceTwoRawSquareRecurrenceMoment_eq_exact h hn hdense]
  exact (div_le_iff₀ hdenPos).2
    (h12TraceTwoRawSquareNumerator_le_1218_dense hn hdense)

theorem h12TraceOneRawFourthRecurrenceMoment_le_34_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceOneRawFourthRecurrenceMoment n x4 x2y y2 xz q ≤
      34 * n ^ 8 := by
  have hnOne : 1 ≤ n := by linarith
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hnOne hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  rw [h12TraceOneRawFourthRecurrenceMoment_eq_exact h hnOne hdense]
  exact (div_le_iff₀ hdenPos).2
    (h12TraceOneRawFourthNumerator_le_34_dense hn hdense)

theorem h12TraceOneRawMeanRecurrenceMoment_le_4_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceOneRawMeanRecurrenceMoment n x2 y ≤ 4 * n ^ 4 := by
  have hnOne : 1 ≤ n := by linarith
  have hc : 26 ≤ c := by nlinarith
  have hdenPos : 0 < h8H10DegreeTwoDenominator c := by
    unfold h8H10DegreeTwoDenominator
    exact mul_pos (by linarith) (by linarith)
  rw [h12TraceOneRawMeanRecurrenceMoment_eq_exact h hnOne hdense]
  exact (div_le_iff₀ hdenPos).2
    (h12TraceOneRawMeanNumerator_le_4_dense hn hdense)

theorem h12TraceTwoRawMeanRecurrenceMoment_le_5_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceTwoRawMeanRecurrenceMoment n x2 y ≤ 5 * n ^ 3 := by
  have hnOne : 1 ≤ n := by linarith
  have hc : 26 ≤ c := by nlinarith
  have hdenPos : 0 < h8H10DegreeTwoDenominator c := by
    unfold h8H10DegreeTwoDenominator
    exact mul_pos (by linarith) (by linarith)
  rw [h12TraceTwoRawMeanRecurrenceMoment_eq_exact h hnOne hdense]
  exact (div_le_iff₀ hdenPos).2
    (h12TraceTwoRawMeanNumerator_le_5_dense hn hdense)

theorem h12TraceTwoRawSquareRecurrenceMoment_le_88_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceTwoRawSquareRecurrenceMoment n x4 x2y y2 xz q ≤
      88 * n ^ 6 := by
  have hnOne : 1 ≤ n := by linarith
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hnOne hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  rw [h12TraceTwoRawSquareRecurrenceMoment_eq_exact h hnOne hdense]
  exact (div_le_iff₀ hdenPos).2
    (h12TraceTwoRawSquareNumerator_le_88_dense hn hdense)

/-- Exact recurrence form of the `22` projective second-trace estimate. -/
theorem h12TraceTwoRawSquareRecurrenceMoment_projective_le_22_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    ((n - 1) / n) ^ 2 *
        h12TraceTwoRawSquareRecurrenceMoment n x4 x2y y2 xz q ≤
      22 * n ^ 6 := by
  have hnOne : 1 ≤ n := by linarith
  have hnPos : 0 < n := by linarith
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hnOne hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  rw [h12TraceTwoRawSquareRecurrenceMoment_eq_exact h hnOne hdense]
  calc
    ((n - 1) / n) ^ 2 *
          (h12TraceTwoRawSquareNumerator n c /
            h8H10CommonVarianceDenominator c) =
        ((n - 1) ^ 2 * h12TraceTwoRawSquareNumerator n c) /
          (n ^ 2 * h8H10CommonVarianceDenominator c) := by
            field_simp [ne_of_gt hnPos, ne_of_gt hdenPos]
    _ ≤ (22 * n ^ 8 * h8H10CommonVarianceDenominator c) /
          (n ^ 2 * h8H10CommonVarianceDenominator c) := by
      exact div_le_div_of_nonneg_right
        (h12TraceTwoRawSquareNumerator_projective_le_22_dense hn hdense)
        (by positivity)
    _ = 22 * n ^ 6 := by
      field_simp [ne_of_gt hnPos, ne_of_gt hdenPos]

/-- Complete recurrence-level H12 coefficient `3151`. -/
theorem h12TraceTwoRawSquareRecurrenceMoment_projective_144_le_3151_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    144 * ((n - 1) / n) ^ 2 *
        h12TraceTwoRawSquareRecurrenceMoment n x4 x2y y2 xz q ≤
      3151 * n ^ 6 := by
  have hnOne : 1 ≤ n := by linarith
  have hnPos : 0 < n := by linarith
  have hdenLower := h8H10_commonVarianceDenominator_lower_dense hnOne hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c / 2) 9) hdenLower
  rw [h12TraceTwoRawSquareRecurrenceMoment_eq_exact h hnOne hdense]
  calc
    144 * ((n - 1) / n) ^ 2 *
          (h12TraceTwoRawSquareNumerator n c /
            h8H10CommonVarianceDenominator c) =
        (144 * (n - 1) ^ 2 * h12TraceTwoRawSquareNumerator n c) /
          (n ^ 2 * h8H10CommonVarianceDenominator c) := by
            field_simp [ne_of_gt hnPos, ne_of_gt hdenPos]
    _ ≤ (3151 * n ^ 8 * h8H10CommonVarianceDenominator c) /
          (n ^ 2 * h8H10CommonVarianceDenominator c) := by
      exact div_le_div_of_nonneg_right
        (h12TraceTwoRawSquareNumerator_projective_144_le_3151_dense
          hn hdense)
        (by positivity)
    _ = 3151 * n ^ 6 := by
      field_simp [ne_of_gt hnPos, ne_of_gt hdenPos]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
