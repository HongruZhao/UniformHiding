import Mathlib.Tactic

/-!
# Exact scalar algebra for the H8/H10 trace recurrences

This file is deliberately foundations-only.  It records the ten scalar
recurrences obtained after setting `E[Tr D] = n`, solves them over `ℝ`, and
computes the two centered fourth-Wick variances exactly.  There is no matrix,
probability, or scientific interface in this module.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

set_option maxHeartbeats 3600000
set_option maxRecDepth 100000

noncomputable section

/-- The ten scalar inverse-Wishart trace recurrences, with `E[Tr D] = n`
already substituted.  The variables respectively denote
`E[x²], E[y], E[x³], E[xy], E[z], E[x⁴], E[x²y], E[y²], E[xz], E[q]`.
-/
structure H8H10ExactTraceRecurrenceSystem
    (n c x2 y x3 xy z x4 x2y y2 xz q : ℝ) : Prop where
  traceOne_sq : c * x2 = c * n * n + 2 * y
  traceTwo : (c - 1) * y = c * n + x2
  traceOne_cube : c * x3 = c * n * x2 + 4 * xy
  traceOne_traceTwo : c * xy = c * n * y + 4 * z
  traceThree : (c - 2) * z = c * y + 2 * xy
  traceOne_fourth : c * x4 = c * n * x3 + 6 * x2y
  traceOne_sq_traceTwo : c * x2y = c * n * xy + 2 * y2 + 4 * xz
  traceTwo_sq : (c - 1) * y2 = c * xy + x2y + 4 * q
  traceOne_traceThree : c * xz = c * n * z + 6 * q
  traceFour : (c - 3) * q = c * z + 2 * xz + y2

/-! ## Canonical rational solution -/

def h8H10DegreeTwoDenominator (c : ℝ) : ℝ :=
  (c - 2) * (c + 1)

def h8H10DegreeThreeDenominator (c : ℝ) : ℝ :=
  (c - 4) * (c + 2)

def h8H10DegreeFourDenominator (c : ℝ) : ℝ :=
  c * (c - 1) * (c - 6) * (c + 3)

def h8H10SolvedX2 (n c : ℝ) : ℝ :=
  c * ((c - 1) * n ^ 2 + 2 * n) / h8H10DegreeTwoDenominator c

def h8H10SolvedY (n c : ℝ) : ℝ :=
  c * n * (c + n) / h8H10DegreeTwoDenominator c

def h8H10SolvedXY (n c : ℝ) : ℝ :=
  c * ((c - 2) * n + 4) * h8H10SolvedY n c /
    h8H10DegreeThreeDenominator c

def h8H10SolvedZ (n c : ℝ) : ℝ :=
  c * (h8H10SolvedXY n c - n * h8H10SolvedY n c) / 4

def h8H10SolvedX3 (n c : ℝ) : ℝ :=
  n * h8H10SolvedX2 n c + 4 * h8H10SolvedXY n c / c

/-- The degree-four determinant numerator after eliminating
`E[x²y], E[y²], E[xz]` from recurrences 7--10. -/
def h8H10SolvedQNumerator (n c : ℝ) : ℝ :=
  c ^ 2 * (h8H10DegreeTwoDenominator c + 2 * (c - 1) * n) *
      h8H10SolvedZ n c +
    c ^ 2 * (n + c) * h8H10SolvedXY n c

def h8H10SolvedQ (n c : ℝ) : ℝ :=
  h8H10SolvedQNumerator n c / h8H10DegreeFourDenominator c

def h8H10SolvedXZ (n c : ℝ) : ℝ :=
  n * h8H10SolvedZ n c + 6 * h8H10SolvedQ n c / c

def h8H10SolvedY2 (n c : ℝ) : ℝ :=
  (c - 3) * h8H10SolvedQ n c - 2 * h8H10SolvedXZ n c -
    c * h8H10SolvedZ n c

def h8H10SolvedX2Y (n c : ℝ) : ℝ :=
  (c - 1) * h8H10SolvedY2 n c - 4 * h8H10SolvedQ n c -
    c * h8H10SolvedXY n c

def h8H10SolvedX4 (n c : ℝ) : ℝ :=
  n * h8H10SolvedX3 n c + 6 * h8H10SolvedX2Y n c / c

/-! ## The two centered fourth-Wick variances -/

def h8TraceRecurrenceVariance
    (n x2 y x4 x2y y2 xz q : ℝ) : ℝ :=
  (n + 1) ^ 4 * x4 +
      12 * (n + 1) ^ 3 * x2y +
      12 * (n + 1) ^ 2 * y2 +
      32 * (n + 1) ^ 2 * xz +
      48 * (n + 1) * q -
    ((n + 1) ^ 2 * x2 + 2 * (n + 1) * y) ^ 2

def h10TraceRecurrenceVariance
    (n x2 y x4 x2y y2 xz q : ℝ) : ℝ :=
  (n + 1) ^ 2 * x4 +
      (2 * (n + 1) ^ 3 + 2 * (n + 1) ^ 2 + 8 * (n + 1)) * x2y +
      ((n + 1) ^ 4 + 2 * (n + 1) ^ 3 + 5 * (n + 1) ^ 2 +
        4 * (n + 1)) * y2 +
      16 * (n + 1) * (n + 2) * xz +
      (8 * (n + 1) ^ 3 + 20 * (n + 1) ^ 2 + 20 * (n + 1)) * q -
    ((n + 1) * (n + 2) * y + (n + 1) * x2) ^ 2

/-- Common reduced denominator of both exact centered variances. -/
def h8H10CommonVarianceDenominator (c : ℝ) : ℝ :=
  (c + 3) * (c + 2) * (c + 1) ^ 2 * (c - 1) * (c - 2) ^ 2 *
    (c - 4) * (c - 6)

/-- Expanded numerator of the exact H8 centered variance. -/
def h8ExactVarianceNumerator (n c : ℝ) : ℝ :=
  c ^ 9 * (8*n^6 + 24*n^5 + 64*n^4 + 88*n^3 + 88*n^2 + 48*n) +
  c ^ 8 * (16*n^7 + 128*n^5 + 224*n^4 + 560*n^3 + 672*n^2 + 192*n) +
  c ^ 7 * (8*n^8 - 80*n^7 + 32*n^6 - 496*n^5 + 152*n^4 +
    1120*n^3 + 256*n^2 - 96*n) +
  c ^ 6 * (-56*n^8 + 16*n^7 - 1008*n^6 - 608*n^5 - 632*n^4 -
    3696*n^3 - 3552*n^2 - 960*n) +
  c ^ 5 * (48*n^8 - 208*n^7 + 424*n^6 - 296*n^5 - 6208*n^4 -
    8408*n^3 - 3704*n^2 - 528*n) +
  c ^ 4 * (168*n^8 + 352*n^7 + 784*n^6 - 2304*n^5 - 3800*n^4 +
    928*n^3 + 2592*n^2 + 768*n) +
  c ^ 3 * (-360*n^8 + 96*n^7 - 432*n^6 + 288*n^5 + 5976*n^4 +
    7872*n^3 + 3648*n^2 + 576*n) +
  c ^ 2 * (144*n^8 - 576*n^7 - 864*n^6 + 2304*n^5 + 4752*n^4 +
    2880*n^3 + 576*n^2)

/-- Expanded numerator of the exact H10 centered variance. -/
def h10ExactVarianceNumerator (n c : ℝ) : ℝ :=
  c ^ 9 * (36*n^4 + 112*n^3 + 124*n^2 + 48*n) +
  c ^ 8 * (144*n^5 + 392*n^4 + 560*n^3 + 504*n^2 + 192*n) +
  c ^ 7 * (216*n^6 + 416*n^5 + 468*n^4 + 128*n^3 - 236*n^2 - 96*n) +
  c ^ 6 * (144*n^7 + 16*n^6 - 840*n^5 - 2720*n^4 - 3592*n^3 -
    2544*n^2 - 960*n) +
  c ^ 5 * (36*n^8 - 208*n^7 - 1584*n^6 - 4248*n^5 - 5676*n^4 -
    4456*n^3 - 2216*n^2 - 528*n) +
  c ^ 4 * (-88*n^8 - 832*n^7 - 1904*n^6 - 1888*n^5 + 104*n^4 +
    1696*n^3 + 1632*n^2 + 768*n) +
  c ^ 3 * (-120*n^8 + 96*n^7 + 1200*n^6 + 3552*n^5 + 5256*n^4 +
    4608*n^3 + 2496*n^2 + 576*n) +
  c ^ 2 * (144*n^8 + 576*n^7 + 1440*n^6 + 2304*n^5 + 2448*n^4 +
    1728*n^3 + 576*n^2)

/-! ## Exact solution and variance identities -/

theorem h8H10ExactTraceRecurrenceSystem_solver
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hc : c ≠ 0)
    (h2 : h8H10DegreeTwoDenominator c ≠ 0)
    (h3 : h8H10DegreeThreeDenominator c ≠ 0)
    (h4 : h8H10DegreeFourDenominator c ≠ 0) :
    x2 = h8H10SolvedX2 n c ∧
    y = h8H10SolvedY n c ∧
    x3 = h8H10SolvedX3 n c ∧
    xy = h8H10SolvedXY n c ∧
    z = h8H10SolvedZ n c ∧
    x4 = h8H10SolvedX4 n c ∧
    x2y = h8H10SolvedX2Y n c ∧
    y2 = h8H10SolvedY2 n c ∧
    xz = h8H10SolvedXZ n c ∧
    q = h8H10SolvedQ n c := by
  have hx2 : x2 = h8H10SolvedX2 n c := by
    rw [h8H10SolvedX2, eq_div_iff h2]
    unfold h8H10DegreeTwoDenominator
    linear_combination (c - 1) * h.traceOne_sq + 2 * h.traceTwo
  have hy : y = h8H10SolvedY n c := by
    rw [h8H10SolvedY, eq_div_iff h2]
    unfold h8H10DegreeTwoDenominator
    linear_combination h.traceOne_sq + c * h.traceTwo
  have hxy : xy = h8H10SolvedXY n c := by
    rw [h8H10SolvedXY, eq_div_iff h3, ← hy]
    unfold h8H10DegreeThreeDenominator
    linear_combination
      (c - 2) * h.traceOne_traceTwo + 4 * h.traceThree
  have hz : z = h8H10SolvedZ n c := by
    rw [h8H10SolvedZ, ← hxy, ← hy]
    nlinarith [h.traceOne_traceTwo]
  have hx3 : x3 = h8H10SolvedX3 n c := by
    rw [h8H10SolvedX3, ← hx2, ← hxy]
    field_simp [hc]
    nlinarith [h.traceOne_cube]
  have hqDen :
      h8H10DegreeFourDenominator c * q =
        c ^ 2 * (h8H10DegreeTwoDenominator c + 2 * (c - 1) * n) * z +
          c ^ 2 * (n + c) * xy := by
    unfold h8H10DegreeTwoDenominator h8H10DegreeFourDenominator
    linear_combination
      c * h.traceOne_sq_traceTwo +
      c ^ 2 * h.traceTwo_sq +
      c * ((c - 2) * (c + 1)) * h.traceFour +
      2 * c * (c - 1) * h.traceOne_traceThree
  have hq : q = h8H10SolvedQ n c := by
    rw [h8H10SolvedQ, eq_div_iff h4, h8H10SolvedQNumerator, ← hz, ← hxy]
    simpa [mul_comm] using hqDen
  have hxz : xz = h8H10SolvedXZ n c := by
    rw [h8H10SolvedXZ, ← hz, ← hq]
    field_simp [hc]
    nlinarith [h.traceOne_traceThree]
  have hy2 : y2 = h8H10SolvedY2 n c := by
    rw [h8H10SolvedY2, ← hq, ← hxz, ← hz]
    nlinarith [h.traceFour]
  have hx2y : x2y = h8H10SolvedX2Y n c := by
    rw [h8H10SolvedX2Y, ← hy2, ← hq, ← hxy]
    nlinarith [h.traceTwo_sq]
  have hx4 : x4 = h8H10SolvedX4 n c := by
    rw [h8H10SolvedX4, ← hx3, ← hx2y]
    field_simp [hc]
    nlinarith [h.traceOne_fourth]
  exact ⟨hx2, hy, hx3, hxy, hz, hx4, hx2y, hy2, hxz, hq⟩

private theorem h8H10CommonVarianceDenominator_ne_zero
    {c : ℝ}
    (h2 : h8H10DegreeTwoDenominator c ≠ 0)
    (h3 : h8H10DegreeThreeDenominator c ≠ 0)
    (h4 : h8H10DegreeFourDenominator c ≠ 0) :
    h8H10CommonVarianceDenominator c ≠ 0 := by
  have hprod :
      h8H10CommonVarianceDenominator c * c =
        h8H10DegreeTwoDenominator c ^ 2 *
          h8H10DegreeThreeDenominator c * h8H10DegreeFourDenominator c := by
    unfold h8H10CommonVarianceDenominator h8H10DegreeTwoDenominator
      h8H10DegreeThreeDenominator h8H10DegreeFourDenominator
    ring
  intro hzero
  have hrhs :
      h8H10DegreeTwoDenominator c ^ 2 *
          h8H10DegreeThreeDenominator c * h8H10DegreeFourDenominator c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 h2) h3) h4
  apply hrhs
  rw [← hprod, hzero]
  simp

private theorem h8H10IndividualDenominatorFactors_ne_zero
    {c : ℝ}
    (h2 : h8H10DegreeTwoDenominator c ≠ 0)
    (h3 : h8H10DegreeThreeDenominator c ≠ 0)
    (h4 : h8H10DegreeFourDenominator c ≠ 0) :
    c - 2 ≠ 0 ∧ c + 1 ≠ 0 ∧
      c - 4 ≠ 0 ∧ c + 2 ≠ 0 ∧
      c ≠ 0 ∧ c - 1 ≠ 0 ∧ c - 6 ≠ 0 ∧ c + 3 ≠ 0 := by
  have h2' : (c - 2) * (c + 1) ≠ 0 := by
    simpa [h8H10DegreeTwoDenominator] using h2
  have h3' : (c - 4) * (c + 2) ≠ 0 := by
    simpa [h8H10DegreeThreeDenominator] using h3
  have h4' : c * (c - 1) * (c - 6) * (c + 3) ≠ 0 := by
    simpa [h8H10DegreeFourDenominator] using h4
  obtain ⟨hc2, hcp1⟩ := mul_ne_zero_iff.mp h2'
  obtain ⟨hc4, hcp2⟩ := mul_ne_zero_iff.mp h3'
  obtain ⟨hleft, hcp3⟩ := mul_ne_zero_iff.mp h4'
  obtain ⟨hleft, hc6⟩ := mul_ne_zero_iff.mp hleft
  obtain ⟨hc, hc1⟩ := mul_ne_zero_iff.mp hleft
  exact ⟨hc2, hcp1, hc4, hcp2, hc, hc1, hc6, hcp3⟩

/-- Exact rational identity for the H8 centered fourth-Wick variance. -/
theorem h8_exact_variance_identity_of_traceRecurrences
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hc : c ≠ 0)
    (h2 : h8H10DegreeTwoDenominator c ≠ 0)
    (h3 : h8H10DegreeThreeDenominator c ≠ 0)
    (h4 : h8H10DegreeFourDenominator c ≠ 0) :
    h8TraceRecurrenceVariance n x2 y x4 x2y y2 xz q =
      h8ExactVarianceNumerator n c / h8H10CommonVarianceDenominator c := by
  obtain ⟨hx2, hy, _, _, _, hx4, hx2y, hy2, hxz, hq⟩ :=
    h8H10ExactTraceRecurrenceSystem_solver h hc h2 h3 h4
  rw [hx2, hy, hx4, hx2y, hy2, hxz, hq]
  have hden := h8H10CommonVarianceDenominator_ne_zero h2 h3 h4
  obtain ⟨hc2, hcp1, hc4, hcp2, hc', hc1, hc6, hcp3⟩ :=
    h8H10IndividualDenominatorFactors_ne_zero h2 h3 h4
  simp only [h8TraceRecurrenceVariance, h8ExactVarianceNumerator,
    h8H10CommonVarianceDenominator, h8H10SolvedX2, h8H10SolvedY,
    h8H10SolvedX4, h8H10SolvedX2Y, h8H10SolvedY2, h8H10SolvedXZ,
    h8H10SolvedQ, h8H10SolvedQNumerator, h8H10SolvedX3, h8H10SolvedXY,
    h8H10SolvedZ, h8H10DegreeTwoDenominator, h8H10DegreeThreeDenominator,
    h8H10DegreeFourDenominator] at hden ⊢
  field_simp [hc, hc', hc2, hcp1, hc4, hcp2, hc1, hc6, hcp3, h2, h3, h4,
    hden]
  ring

/-- Exact rational identity for the H10 centered fourth-Wick variance. -/
theorem h10_exact_variance_identity_of_traceRecurrences
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hc : c ≠ 0)
    (h2 : h8H10DegreeTwoDenominator c ≠ 0)
    (h3 : h8H10DegreeThreeDenominator c ≠ 0)
    (h4 : h8H10DegreeFourDenominator c ≠ 0) :
    h10TraceRecurrenceVariance n x2 y x4 x2y y2 xz q =
      h10ExactVarianceNumerator n c / h8H10CommonVarianceDenominator c := by
  obtain ⟨hx2, hy, _, _, _, hx4, hx2y, hy2, hxz, hq⟩ :=
    h8H10ExactTraceRecurrenceSystem_solver h hc h2 h3 h4
  rw [hx2, hy, hx4, hx2y, hy2, hxz, hq]
  have hden := h8H10CommonVarianceDenominator_ne_zero h2 h3 h4
  obtain ⟨hc2, hcp1, hc4, hcp2, hc', hc1, hc6, hcp3⟩ :=
    h8H10IndividualDenominatorFactors_ne_zero h2 h3 h4
  simp only [h10TraceRecurrenceVariance, h10ExactVarianceNumerator,
    h8H10CommonVarianceDenominator, h8H10SolvedX2, h8H10SolvedY,
    h8H10SolvedX4, h8H10SolvedX2Y, h8H10SolvedY2, h8H10SolvedXZ,
    h8H10SolvedQ, h8H10SolvedQNumerator, h8H10SolvedX3, h8H10SolvedXY,
    h8H10SolvedZ, h8H10DegreeTwoDenominator, h8H10DegreeThreeDenominator,
    h8H10DegreeFourDenominator] at hden ⊢
  field_simp [hc, hc', hc2, hcp1, hc4, hcp2, hc1, hc6, hcp3, h2, h3, h4,
    hden]
  ring

/-! ## Dense-regime adapters for the nonzero hypotheses -/

theorem h8H10_traceRecurrence_denominators_ne_zero_of_dense
    {n c : ℝ} (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    c ≠ 0 ∧
      h8H10DegreeTwoDenominator c ≠ 0 ∧
      h8H10DegreeThreeDenominator c ≠ 0 ∧
      h8H10DegreeFourDenominator c ≠ 0 := by
  have hc13 : 13 ≤ c := by nlinarith
  constructor
  · nlinarith
  constructor
  · unfold h8H10DegreeTwoDenominator
    exact mul_ne_zero (by nlinarith) (by nlinarith)
  constructor
  · unfold h8H10DegreeThreeDenominator
    exact mul_ne_zero (by nlinarith) (by nlinarith)
  · unfold h8H10DegreeFourDenominator
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by nlinarith) (by nlinarith))
      (by nlinarith)) (by nlinarith)

theorem h8_exact_variance_identity_of_traceRecurrences_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h8TraceRecurrenceVariance n x2 y x4 x2y y2 xz q =
      h8ExactVarianceNumerator n c / h8H10CommonVarianceDenominator c := by
  obtain ⟨hc, h2, h3, h4⟩ :=
    h8H10_traceRecurrence_denominators_ne_zero_of_dense hn hdense
  exact h8_exact_variance_identity_of_traceRecurrences h hc h2 h3 h4

theorem h10_exact_variance_identity_of_traceRecurrences_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h10TraceRecurrenceVariance n x2 y x4 x2y y2 xz q =
      h10ExactVarianceNumerator n c / h8H10CommonVarianceDenominator c := by
  obtain ⟨hc, h2, h3, h4⟩ :=
    h8H10_traceRecurrence_denominators_ne_zero_of_dense hn hdense
  exact h10_exact_variance_identity_of_traceRecurrences h hc h2 h3 h4

/-! ## Dense rational bounds -/

/-- Every monomial occurring in the H8/H10 numerators is dominated by the
endpoint monomial after using `1 ≤ n ≤ c`. -/
theorem h8H10_dense_monomial_le
    {n c : ℝ} {a b target : ℕ}
    (hn : 1 ≤ n) (hnc : n ≤ c)
    (hb : b ≤ 9) (hdeg : a + b ≤ target + 9) :
    n ^ a * c ^ b ≤ n ^ target * c ^ 9 := by
  have hn0 : 0 ≤ n := by linarith
  have hc1 : 1 ≤ c := hn.trans hnc
  have hc0 : 0 ≤ c := by linarith
  by_cases hat : a ≤ target
  · exact mul_le_mul
      (pow_le_pow_right₀ hn hat)
      (pow_le_pow_right₀ hc1 hb)
      (pow_nonneg hc0 b) (pow_nonneg hn0 target)
  · have hta : target < a := Nat.lt_of_not_ge hat
    have ha : a = target + (a - target) := by omega
    have hrest : a - target + b ≤ 9 := by omega
    have hbase : n ^ (a - target) ≤ c ^ (a - target) :=
      pow_le_pow_left₀ hn0 hnc (a - target)
    calc
      n ^ a * c ^ b =
          n ^ (target + (a - target)) * c ^ b := by
        exact congrArg (fun k : ℝ => k * c ^ b)
          (congrArg (fun e : ℕ => n ^ e) ha)
      _ = n ^ target * (n ^ (a - target) * c ^ b) := by
        rw [pow_add]
        ring
      _ ≤ n ^ target * (c ^ (a - target) * c ^ b) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hbase (pow_nonneg hc0 b))
          (pow_nonneg hn0 target)
      _ = n ^ target * c ^ (a - target + b) := by rw [pow_add]
      _ ≤ n ^ target * c ^ 9 := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hc1 hrest) (pow_nonneg hn0 target)

private theorem h8_numerator_group_bounds
    {n c : ℝ} (hn : 1 ≤ n) (hnc : n ≤ c) :
    h8ExactVarianceNumerator n c ≤ 38872 * n ^ 6 * c ^ 9 := by
  have hn0 : 0 ≤ n := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hp12 : n ^ 1 ≤ n ^ 2 := pow_le_pow_right₀ hn (by omega)
  have hp23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn (by omega)
  have hp34 : n ^ 3 ≤ n ^ 4 := pow_le_pow_right₀ hn (by omega)
  have hp45 : n ^ 4 ≤ n ^ 5 := pow_le_pow_right₀ hn (by omega)
  have hp56 : n ^ 5 ≤ n ^ 6 := pow_le_pow_right₀ hn (by omega)
  have hp67 : n ^ 6 ≤ n ^ 7 := pow_le_pow_right₀ hn (by omega)
  have hp78 : n ^ 7 ≤ n ^ 8 := pow_le_pow_right₀ hn (by omega)
  have hn1 : 0 ≤ n ^ 1 := pow_nonneg hn0 1
  have hn2 : 0 ≤ n ^ 2 := pow_nonneg hn0 2
  have hn3 : 0 ≤ n ^ 3 := pow_nonneg hn0 3
  have hn4 : 0 ≤ n ^ 4 := pow_nonneg hn0 4
  have hn5 : 0 ≤ n ^ 5 := pow_nonneg hn0 5
  have hn6 : 0 ≤ n ^ 6 := pow_nonneg hn0 6
  have hn7 : 0 ≤ n ^ 7 := pow_nonneg hn0 7
  have hn8 : 0 ≤ n ^ 8 := pow_nonneg hn0 8
  have hg9 :
      8*n^6 + 24*n^5 + 64*n^4 + 88*n^3 + 88*n^2 + 48*n ≤
        320 * n^6 := by nlinarith
  have hg8 :
      16*n^7 + 128*n^5 + 224*n^4 + 560*n^3 + 672*n^2 + 192*n ≤
        1792 * n^7 := by nlinarith
  have hg7 :
      8*n^8 - 80*n^7 + 32*n^6 - 496*n^5 + 152*n^4 +
          1120*n^3 + 256*n^2 - 96*n ≤ 1568 * n^8 := by nlinarith
  have hg6 :
      -56*n^8 + 16*n^7 - 1008*n^6 - 608*n^5 - 632*n^4 -
          3696*n^3 - 3552*n^2 - 960*n ≤ 16 * n^7 := by nlinarith
  have hg5 :
      48*n^8 - 208*n^7 + 424*n^6 - 296*n^5 - 6208*n^4 -
          8408*n^3 - 3704*n^2 - 528*n ≤ 472 * n^8 := by nlinarith
  have hg4 :
      168*n^8 + 352*n^7 + 784*n^6 - 2304*n^5 - 3800*n^4 +
          928*n^3 + 2592*n^2 + 768*n ≤ 5592 * n^8 := by nlinarith
  have hg3 :
      -360*n^8 + 96*n^7 - 432*n^6 + 288*n^5 + 5976*n^4 +
          7872*n^3 + 3648*n^2 + 576*n ≤ 18456 * n^7 := by nlinarith
  have hg2 :
      144*n^8 - 576*n^7 - 864*n^6 + 2304*n^5 + 4752*n^4 +
          2880*n^3 + 576*n^2 ≤ 10656 * n^8 := by nlinarith
  have ht9 : c^9 *
      (8*n^6 + 24*n^5 + 64*n^4 + 88*n^3 + 88*n^2 + 48*n) ≤
        320 * (n^6 * c^9) := by
    calc
      _ ≤ c^9 * (320*n^6) := mul_le_mul_of_nonneg_left hg9 (pow_nonneg hc0 9)
      _ = 320 * (n^6*c^9) := by ring
  have ht8 : c^8 *
      (16*n^7 + 128*n^5 + 224*n^4 + 560*n^3 + 672*n^2 + 192*n) ≤
        1792 * (n^6 * c^9) := by
    calc
      _ ≤ c^8 * (1792*n^7) := mul_le_mul_of_nonneg_left hg8 (pow_nonneg hc0 8)
      _ = 1792 * (n^7*c^8) := by ring
      _ ≤ 1792 * (n^6*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht7 : c^7 *
      (8*n^8 - 80*n^7 + 32*n^6 - 496*n^5 + 152*n^4 +
        1120*n^3 + 256*n^2 - 96*n) ≤ 1568 * (n^6*c^9) := by
    calc
      _ ≤ c^7 * (1568*n^8) := mul_le_mul_of_nonneg_left hg7 (pow_nonneg hc0 7)
      _ = 1568 * (n^8*c^7) := by ring
      _ ≤ 1568 * (n^6*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht6 : c^6 *
      (-56*n^8 + 16*n^7 - 1008*n^6 - 608*n^5 - 632*n^4 -
        3696*n^3 - 3552*n^2 - 960*n) ≤ 16 * (n^6*c^9) := by
    calc
      _ ≤ c^6 * (16*n^7) := mul_le_mul_of_nonneg_left hg6 (pow_nonneg hc0 6)
      _ = 16 * (n^7*c^6) := by ring
      _ ≤ 16 * (n^6*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht5 : c^5 *
      (48*n^8 - 208*n^7 + 424*n^6 - 296*n^5 - 6208*n^4 -
        8408*n^3 - 3704*n^2 - 528*n) ≤ 472 * (n^6*c^9) := by
    calc
      _ ≤ c^5 * (472*n^8) := mul_le_mul_of_nonneg_left hg5 (pow_nonneg hc0 5)
      _ = 472 * (n^8*c^5) := by ring
      _ ≤ 472 * (n^6*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht4 : c^4 *
      (168*n^8 + 352*n^7 + 784*n^6 - 2304*n^5 - 3800*n^4 +
        928*n^3 + 2592*n^2 + 768*n) ≤ 5592 * (n^6*c^9) := by
    calc
      _ ≤ c^4 * (5592*n^8) := mul_le_mul_of_nonneg_left hg4 (pow_nonneg hc0 4)
      _ = 5592 * (n^8*c^4) := by ring
      _ ≤ 5592 * (n^6*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht3 : c^3 *
      (-360*n^8 + 96*n^7 - 432*n^6 + 288*n^5 + 5976*n^4 +
        7872*n^3 + 3648*n^2 + 576*n) ≤ 18456 * (n^6*c^9) := by
    calc
      _ ≤ c^3 * (18456*n^7) := mul_le_mul_of_nonneg_left hg3 (pow_nonneg hc0 3)
      _ = 18456 * (n^7*c^3) := by ring
      _ ≤ 18456 * (n^6*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht2 : c^2 *
      (144*n^8 - 576*n^7 - 864*n^6 + 2304*n^5 + 4752*n^4 +
        2880*n^3 + 576*n^2) ≤ 10656 * (n^6*c^9) := by
    calc
      _ ≤ c^2 * (10656*n^8) := mul_le_mul_of_nonneg_left hg2 (pow_nonneg hc0 2)
      _ = 10656 * (n^8*c^2) := by ring
      _ ≤ 10656 * (n^6*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  unfold h8ExactVarianceNumerator
  nlinarith [ht9, ht8, ht7, ht6, ht5, ht4, ht3, ht2]

private theorem h10_numerator_group_bounds
    {n c : ℝ} (hn : 1 ≤ n) (hnc : n ≤ c) :
    h10ExactVarianceNumerator n c ≤ 34736 * n ^ 4 * c ^ 9 := by
  have hn0 : 0 ≤ n := by linarith
  have hc0 : 0 ≤ c := by linarith
  have hp12 : n ^ 1 ≤ n ^ 2 := pow_le_pow_right₀ hn (by omega)
  have hp23 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn (by omega)
  have hp34 : n ^ 3 ≤ n ^ 4 := pow_le_pow_right₀ hn (by omega)
  have hp45 : n ^ 4 ≤ n ^ 5 := pow_le_pow_right₀ hn (by omega)
  have hp56 : n ^ 5 ≤ n ^ 6 := pow_le_pow_right₀ hn (by omega)
  have hp67 : n ^ 6 ≤ n ^ 7 := pow_le_pow_right₀ hn (by omega)
  have hp78 : n ^ 7 ≤ n ^ 8 := pow_le_pow_right₀ hn (by omega)
  have hn1 : 0 ≤ n ^ 1 := pow_nonneg hn0 1
  have hn2 : 0 ≤ n ^ 2 := pow_nonneg hn0 2
  have hn3 : 0 ≤ n ^ 3 := pow_nonneg hn0 3
  have hn4 : 0 ≤ n ^ 4 := pow_nonneg hn0 4
  have hn5 : 0 ≤ n ^ 5 := pow_nonneg hn0 5
  have hn6 : 0 ≤ n ^ 6 := pow_nonneg hn0 6
  have hn7 : 0 ≤ n ^ 7 := pow_nonneg hn0 7
  have hn8 : 0 ≤ n ^ 8 := pow_nonneg hn0 8
  have hg9 : 36*n^4 + 112*n^3 + 124*n^2 + 48*n ≤ 320*n^4 := by nlinarith
  have hg8 : 144*n^5 + 392*n^4 + 560*n^3 + 504*n^2 + 192*n ≤
      1792*n^5 := by nlinarith
  have hg7 : 216*n^6 + 416*n^5 + 468*n^4 + 128*n^3 - 236*n^2 - 96*n ≤
      1228*n^6 := by nlinarith
  have hg6 : 144*n^7 + 16*n^6 - 840*n^5 - 2720*n^4 - 3592*n^3 -
      2544*n^2 - 960*n ≤ 160*n^7 := by nlinarith
  have hg5 : 36*n^8 - 208*n^7 - 1584*n^6 - 4248*n^5 - 5676*n^4 -
      4456*n^3 - 2216*n^2 - 528*n ≤ 36*n^8 := by nlinarith
  have hg4 : -88*n^8 - 832*n^7 - 1904*n^6 - 1888*n^5 + 104*n^4 +
      1696*n^3 + 1632*n^2 + 768*n ≤ 4200*n^4 := by nlinarith
  have hg3 : -120*n^8 + 96*n^7 + 1200*n^6 + 3552*n^5 + 5256*n^4 +
      4608*n^3 + 2496*n^2 + 576*n ≤ 17784*n^7 := by nlinarith
  have hg2 : 144*n^8 + 576*n^7 + 1440*n^6 + 2304*n^5 + 2448*n^4 +
      1728*n^3 + 576*n^2 ≤ 9216*n^8 := by nlinarith
  have ht9 : c^9*(36*n^4 + 112*n^3 + 124*n^2 + 48*n) ≤
      320*(n^4*c^9) := by
    calc
      _ ≤ c^9*(320*n^4) := mul_le_mul_of_nonneg_left hg9 (pow_nonneg hc0 9)
      _ = 320*(n^4*c^9) := by ring
  have ht8 : c^8*(144*n^5 + 392*n^4 + 560*n^3 + 504*n^2 + 192*n) ≤
      1792*(n^4*c^9) := by
    calc
      _ ≤ c^8*(1792*n^5) := mul_le_mul_of_nonneg_left hg8 (pow_nonneg hc0 8)
      _ = 1792*(n^5*c^8) := by ring
      _ ≤ 1792*(n^4*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht7 : c^7*(216*n^6 + 416*n^5 + 468*n^4 + 128*n^3 - 236*n^2 - 96*n) ≤
      1228*(n^4*c^9) := by
    calc
      _ ≤ c^7*(1228*n^6) := mul_le_mul_of_nonneg_left hg7 (pow_nonneg hc0 7)
      _ = 1228*(n^6*c^7) := by ring
      _ ≤ 1228*(n^4*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht6 : c^6*(144*n^7 + 16*n^6 - 840*n^5 - 2720*n^4 - 3592*n^3 -
      2544*n^2 - 960*n) ≤ 160*(n^4*c^9) := by
    calc
      _ ≤ c^6*(160*n^7) := mul_le_mul_of_nonneg_left hg6 (pow_nonneg hc0 6)
      _ = 160*(n^7*c^6) := by ring
      _ ≤ 160*(n^4*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht5 : c^5*(36*n^8 - 208*n^7 - 1584*n^6 - 4248*n^5 - 5676*n^4 -
      4456*n^3 - 2216*n^2 - 528*n) ≤ 36*(n^4*c^9) := by
    calc
      _ ≤ c^5*(36*n^8) := mul_le_mul_of_nonneg_left hg5 (pow_nonneg hc0 5)
      _ = 36*(n^8*c^5) := by ring
      _ ≤ 36*(n^4*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht4 : c^4*(-88*n^8 - 832*n^7 - 1904*n^6 - 1888*n^5 + 104*n^4 +
      1696*n^3 + 1632*n^2 + 768*n) ≤ 4200*(n^4*c^9) := by
    calc
      _ ≤ c^4*(4200*n^4) := mul_le_mul_of_nonneg_left hg4 (pow_nonneg hc0 4)
      _ = 4200*(n^4*c^4) := by ring
      _ ≤ 4200*(n^4*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht3 : c^3*(-120*n^8 + 96*n^7 + 1200*n^6 + 3552*n^5 + 5256*n^4 +
      4608*n^3 + 2496*n^2 + 576*n) ≤ 17784*(n^4*c^9) := by
    calc
      _ ≤ c^3*(17784*n^7) := mul_le_mul_of_nonneg_left hg3 (pow_nonneg hc0 3)
      _ = 17784*(n^7*c^3) := by ring
      _ ≤ 17784*(n^4*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  have ht2 : c^2*(144*n^8 + 576*n^7 + 1440*n^6 + 2304*n^5 + 2448*n^4 +
      1728*n^3 + 576*n^2) ≤ 9216*(n^4*c^9) := by
    calc
      _ ≤ c^2*(9216*n^8) := mul_le_mul_of_nonneg_left hg2 (pow_nonneg hc0 2)
      _ = 9216*(n^8*c^2) := by ring
      _ ≤ 9216*(n^4*c^9) := mul_le_mul_of_nonneg_left
        (h8H10_dense_monomial_le hn hnc (by omega) (by omega)) (by norm_num)
  unfold h10ExactVarianceNumerator
  nlinarith [ht9, ht8, ht7, ht6, ht5, ht4, ht3, ht2]

/-- The factored common denominator dominates `(c/2)^9` throughout the dense
range. -/
theorem h8H10_commonVarianceDenominator_lower_dense
    {n c : ℝ} (hn : 1 ≤ n) (hdense : 13*n ≤ c) :
    (c / 2) ^ 9 ≤ h8H10CommonVarianceDenominator c := by
  have hc13 : 13 ≤ c := by nlinarith
  have hcp3 : 0 ≤ c + 3 := by nlinarith
  have hcp2 : 0 ≤ c + 2 := by nlinarith
  have hcp1 : 0 ≤ c + 1 := by nlinarith
  have hcm1 : 0 ≤ c - 1 := by nlinarith
  have hcm2 : 0 ≤ c - 2 := by nlinarith
  have hcm4 : 0 ≤ c - 4 := by nlinarith
  have hcm6 : 0 ≤ c - 6 := by nlinarith
  calc
    (c/2)^9 =
        (c/2)*(c/2)*(c/2)*(c/2)*(c/2)*(c/2)*(c/2)*(c/2)*(c/2) := by ring
    _ ≤ (c+3)*(c+2)*(c+1)*(c+1)*(c-1)*(c-2)*(c-2)*(c-4)*(c-6) := by
      gcongr <;> nlinarith
    _ = h8H10CommonVarianceDenominator c := by
      unfold h8H10CommonVarianceDenominator
      ring

/-- Dense H8 scalar variance bound, already far below the endpoint constant. -/
theorem h8_traceRecurrenceVariance_le_twoPow26_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13*n ≤ c) :
    h8TraceRecurrenceVariance n x2 y x4 x2y y2 xz q ≤ 2^26 * n^6 := by
  have hnc : n ≤ c := by nlinarith
  have hn6 : 0 ≤ n^6 := pow_nonneg (by linarith) 6
  have hlow := h8H10_commonVarianceDenominator_lower_dense hn hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c/2) 9) hlow
  have hc9 : c^9 ≤ 512 * h8H10CommonVarianceDenominator c := by
    calc
      c^9 = 512 * (c/2)^9 := by ring
      _ ≤ 512 * h8H10CommonVarianceDenominator c := by gcongr
  rw [h8_exact_variance_identity_of_traceRecurrences_dense h hn hdense]
  apply (div_le_iff₀ hdenPos).2
  calc
    h8ExactVarianceNumerator n c ≤ 38872*n^6*c^9 :=
      h8_numerator_group_bounds hn hnc
    _ ≤ 38872*n^6*(512*h8H10CommonVarianceDenominator c) := by gcongr
    _ = (38872*512)*(n^6*h8H10CommonVarianceDenominator c) := by ring
    _ ≤ 2^26*(n^6*h8H10CommonVarianceDenominator c) := by
      apply mul_le_mul_of_nonneg_right (by norm_num)
      exact mul_nonneg hn6 hdenPos.le
    _ = 2^26*n^6*h8H10CommonVarianceDenominator c := by ring

/-- Dense H10 scalar variance bound, already far below the endpoint constant. -/
theorem h10_traceRecurrenceVariance_le_twoPow26_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13*n ≤ c) :
    h10TraceRecurrenceVariance n x2 y x4 x2y y2 xz q ≤ 2^26 * n^4 := by
  have hnc : n ≤ c := by nlinarith
  have hn4 : 0 ≤ n^4 := pow_nonneg (by linarith) 4
  have hlow := h8H10_commonVarianceDenominator_lower_dense hn hdense
  have hdenPos : 0 < h8H10CommonVarianceDenominator c :=
    lt_of_lt_of_le (pow_pos (by nlinarith : 0 < c/2) 9) hlow
  have hc9 : c^9 ≤ 512 * h8H10CommonVarianceDenominator c := by
    calc
      c^9 = 512 * (c/2)^9 := by ring
      _ ≤ 512 * h8H10CommonVarianceDenominator c := by gcongr
  rw [h10_exact_variance_identity_of_traceRecurrences_dense h hn hdense]
  apply (div_le_iff₀ hdenPos).2
  calc
    h10ExactVarianceNumerator n c ≤ 34736*n^4*c^9 :=
      h10_numerator_group_bounds hn hnc
    _ ≤ 34736*n^4*(512*h8H10CommonVarianceDenominator c) := by gcongr
    _ = (34736*512)*(n^4*h8H10CommonVarianceDenominator c) := by ring
    _ ≤ 2^26*(n^4*h8H10CommonVarianceDenominator c) := by
      apply mul_le_mul_of_nonneg_right (by norm_num)
      exact mul_nonneg hn4 hdenPos.le
    _ = 2^26*n^4*h8H10CommonVarianceDenominator c := by ring

/-- Literal squared-constant shape required by the H8 endpoint. -/
theorem h8_traceRecurrenceVariance_le_twoPow40_sq_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13*n ≤ c) :
    h8TraceRecurrenceVariance n x2 y x4 x2y y2 xz q ≤ (2^40*n^3)^2 := by
  calc
    _ ≤ 2^26*n^6 := h8_traceRecurrenceVariance_le_twoPow26_dense h hn hdense
    _ ≤ 2^80*n^6 := by gcongr <;> norm_num
    _ = (2^40*n^3)^2 := by ring

/-- Literal squared-constant shape required by the H10 endpoint. -/
theorem h10_traceRecurrenceVariance_le_twoPow40_sq_dense
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 1 ≤ n) (hdense : 13*n ≤ c) :
    h10TraceRecurrenceVariance n x2 y x4 x2y y2 xz q ≤ (2^40*n^2)^2 := by
  calc
    _ ≤ 2^26*n^4 := h10_traceRecurrenceVariance_le_twoPow26_dense h hn hdense
    _ ≤ 2^80*n^4 := by gcongr <;> norm_num
    _ = (2^40*n^2)^2 := by ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
