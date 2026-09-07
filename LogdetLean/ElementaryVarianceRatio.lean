import LogdetLean.ElementaryNormalization
import Mathlib.Tactic

/-!
# Exact-to-elementary null variance ratio

This module proves the variance half of Lemma 5.6 / equation (5.29) in
arXiv:2608.00565v1, uniformly over every strict-gap sequence.  It is kept
downstream of `ElementaryNormalization.lean` so the old-paper CLT module can
import the finished bridge without creating an import cycle.
-/

namespace LogdetLean

open Filter Real Set
open scoped Topology

noncomputable section

/-- Exact algebraic decomposition of the gap between the elementary
variance and the harmonic leading sum. -/
theorem elementaryNullVarianceReal_sub_nullVLeading_eq
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    elementaryNullVarianceReal (m : ℝ) (p : ℝ) - nullVLeading m p =
      1 / ((m - p : ℕ) : ℝ) - 1 / (m : ℝ) +
        2 * (harmonicSecondOrderError m -
          harmonicSecondOrderError (m - p)) := by
  let d : ℕ := m - p
  have hp : 2 ≤ p := h.1
  have hpm : p ≤ m := h.2
  have hmpos : 0 < m := by omega
  have hdpos : 0 < d := by dsimp [d]; omega
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
  have hgapcast : (p : ℝ) = (m : ℝ) - (d : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub hpm]
    ring
  have hev := elementaryNullVarianceReal_gap_rewrite
    (m := (m : ℝ)) (p := (p : ℝ)) (d := (d : ℝ))
    hmR hdR hgapcast
  have hv := nullVLeading_eq_harmonic_sub h
  have hmEq : m - 1 + 1 = m := by omega
  have hharmSucc : (harmonic (m - 1) : ℝ) =
      (harmonic m : ℝ) - 1 / (m : ℝ) := by
    have hs := congrArg (fun q : ℚ ↦ (q : ℝ)) (harmonic_succ (m - 1))
    rw [hmEq] at hs
    norm_num only [Rat.cast_add, Rat.cast_inv, Rat.cast_natCast] at hs
    rw [one_div]
    linarith
  have hharM : (harmonic m : ℝ) =
      Real.log (m : ℝ) + Real.eulerMascheroniConstant +
        1 / (2 * (m : ℝ)) - harmonicSecondOrderError m := by
    unfold harmonicSecondOrderError
    ring
  have hharD : (harmonic d : ℝ) =
      Real.log (d : ℝ) + Real.eulerMascheroniConstant +
        1 / (2 * (d : ℝ)) - harmonicSecondOrderError d := by
    unfold harmonicSecondOrderError
    ring
  have hgaplog : gapLogReal (m : ℝ) (d : ℝ) =
      Real.log (m : ℝ) - Real.log (d : ℝ) := by
    unfold gapLogReal
    rw [Real.log_div hmR.ne' hdR.ne']
  rw [hev, hv, hharmSucc, hharM, hharD, hgaplog]
  dsimp [d]
  ring

/-- The elementary variance is above the harmonic leading sum, with a
dilute-safe cancellation bound. -/
theorem elementaryNullVarianceReal_sub_nullVLeading_bounds
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    0 ≤ elementaryNullVarianceReal (m : ℝ) (p : ℝ) - nullVLeading m p ∧
      elementaryNullVarianceReal (m : ℝ) (p : ℝ) - nullVLeading m p ≤
        1 / ((m - p : ℕ) : ℝ) - 1 / (m : ℝ) := by
  let d : ℕ := m - p
  have hmpos : 0 < m := by omega
  have hdpos : 0 < d := by dsimp [d]; omega
  have hdm : d ≤ m := by dsimp [d]; omega
  have hEq := elementaryNullVarianceReal_sub_nullVLeading_eq h hstrict
  have hantiQ : Antitone harmonicSecondOrderError :=
    antitone_nat_of_succ_le fun n ↦ by
      by_cases hn : n = 0
      · subst n
        have hq1 := harmonicSecondOrderError_nonneg (show 0 < 1 by omega)
        unfold harmonicSecondOrderError
        norm_num at hq1 ⊢
      · simpa [Nat.succ_eq_add_one] using
          harmonicSecondOrderError_antitone_step (Nat.pos_of_ne_zero hn)
  have hQ : harmonicSecondOrderError m ≤ harmonicSecondOrderError d :=
    hantiQ hdm
  constructor
  · rw [hEq]
    have heuler : Real.eulerMascheroniSeq' m ≤
        Real.eulerMascheroniSeq' d :=
      Real.strictAnti_eulerMascheroniSeq'.antitone hdm
    have hmne : m ≠ 0 := hmpos.ne'
    have hdne : d ≠ 0 := hdpos.ne'
    simp only [Real.eulerMascheroniSeq', if_neg hmne, if_neg hdne] at heuler
    have hharM : (harmonic m : ℝ) =
        Real.log (m : ℝ) + Real.eulerMascheroniConstant +
          1 / (2 * (m : ℝ)) - harmonicSecondOrderError m := by
      unfold harmonicSecondOrderError
      ring
    have hharD : (harmonic d : ℝ) =
        Real.log (d : ℝ) + Real.eulerMascheroniConstant +
          1 / (2 * (d : ℝ)) - harmonicSecondOrderError d := by
      unfold harmonicSecondOrderError
      ring
    rw [hharM, hharD] at heuler
    dsimp [d] at heuler hQ
    have hmhalf : 1 / (2 * (m : ℝ)) = (1 / 2 : ℝ) * (1 / (m : ℝ)) := by
      field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hmne]
    have hdhalf : 1 / (2 * ((m - p : ℕ) : ℝ)) =
        (1 / 2 : ℝ) * (1 / ((m - p : ℕ) : ℝ)) := by
      have hdp : m - p ≠ 0 := by omega
      field_simp [show ((m - p : ℕ) : ℝ) ≠ 0 by exact_mod_cast hdp]
    rw [hmhalf, hdhalf] at heuler
    linarith
  · rw [hEq]
    linarith

/-- A uniform positive lower bound for the elementary variance.  Written
with `d=m-p`, it is `2 p^2 / (m (m+d))`. -/
theorem elementaryNullVarianceReal_ge_gap_ratio_sq
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    2 * (p : ℝ) ^ 2 /
        ((m : ℝ) * ((m : ℝ) + ((m - p : ℕ) : ℝ))) ≤
      elementaryNullVarianceReal (m : ℝ) (p : ℝ) := by
  let d : ℕ := m - p
  let x : ℝ := (p : ℝ) / (d : ℝ)
  have hpN : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) h.1
  have hmN : 0 < m := hpN.trans_le h.2
  have hdN : 0 < d := by dsimp [d]; omega
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmN
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hdN
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hmp : m = p + d := by dsimp [d]; omega
  have hmpR : (m : ℝ) = (p : ℝ) + (d : ℝ) := by
    exact_mod_cast hmp
  have hgapcast : (p : ℝ) = (m : ℝ) - (d : ℝ) := by
    rw [hmpR]
    ring
  have hev := elementaryNullVarianceReal_gap_rewrite
    (m := (m : ℝ)) (p := (p : ℝ)) (d := (d : ℝ))
    hmR hdR hgapcast
  have hgaplog : gapLogReal (m : ℝ) (d : ℝ) = Real.log (1 + x) := by
    unfold gapLogReal
    congr 1
    dsimp [x]
    rw [hmpR]
    field_simp [hdR.ne']
    ring
  have hratio : (p : ℝ) / (m : ℝ) = x / (1 + x) := by
    dsimp [x]
    rw [hmpR]
    field_simp [hdR.ne', hpR.ne']
    ring
  have hlog := Real.le_log_one_add_of_nonneg hx
  have hden1 : 0 < x + 1 := by linarith
  have hden2 : 0 < x + 2 := by linarith
  have halg :
      2 * x / (x + 2) - x / (x + 1) =
        x ^ 2 / ((x + 1) * (x + 2)) := by
    field_simp [hden1.ne', hden2.ne']
    ring
  have hcore : x ^ 2 / ((x + 1) * (x + 2)) ≤
      Real.log (1 + x) - x / (1 + x) := by
    have hsub := sub_le_sub_right hlog (x / (x + 1))
    rw [halg] at hsub
    simpa [add_comm] using hsub
  calc
    2 * (p : ℝ) ^ 2 /
        ((m : ℝ) * ((m : ℝ) + ((m - p : ℕ) : ℝ))) =
        2 * (x ^ 2 / ((x + 1) * (x + 2))) := by
      dsimp [x, d]
      rw [Nat.cast_sub h.2]
      field_simp [hmR.ne', hpR.ne',
        show (m : ℝ) - (p : ℝ) ≠ 0 by linarith]
      ring
    _ ≤ 2 * (Real.log (1 + x) - x / (1 + x)) := by linarith
    _ = elementaryNullVarianceReal (m : ℝ) (p : ℝ) := by
      rw [hev, hgaplog, hratio]

/-- Positivity of the elementary null variance throughout the strict-gap
range. -/
theorem elementaryNullVarianceReal_pos_nat
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    0 < elementaryNullVarianceReal (m : ℝ) (p : ℝ) := by
  have hpN : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) h.1
  have hmN : 0 < m := hpN.trans_le h.2
  have hdN : 0 < m - p := by omega
  have hlower := elementaryNullVarianceReal_ge_gap_ratio_sq h hstrict
  have hpos : 0 < 2 * (p : ℝ) ^ 2 /
      ((m : ℝ) * ((m : ℝ) + ((m - p : ℕ) : ℝ))) := by
    positivity
  exact hpos.trans_le hlower

/-- Coarse growing-gap comparison between the exact and elementary
variances. -/
theorem abs_nullVSeries_sub_elementaryNullVarianceReal_growingGap_le
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    |nullVSeries m p - elementaryNullVarianceReal (m : ℝ) (p : ℝ)| ≤
      5 / ((m - p : ℕ) : ℝ) +
        4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
  have hd : 1 ≤ m - p := by omega
  have hVL := abs_nullVSeries_sub_nullVLeading_growingGap_le h hd
  have hLE := elementaryNullVarianceReal_sub_nullVLeading_bounds h hstrict
  have hDpos : 0 < (((m - p : ℕ) : ℝ)) := by positivity
  calc
    |nullVSeries m p - elementaryNullVarianceReal (m : ℝ) (p : ℝ)| =
        |(nullVSeries m p - nullVLeading m p) -
          (elementaryNullVarianceReal (m : ℝ) (p : ℝ) -
            nullVLeading m p)| := by ring_nf
    _ ≤ |nullVSeries m p - nullVLeading m p| +
        |elementaryNullVarianceReal (m : ℝ) (p : ℝ) -
          nullVLeading m p| := abs_sub _ _
    _ = |nullVSeries m p - nullVLeading m p| +
        (elementaryNullVarianceReal (m : ℝ) (p : ℝ) -
          nullVLeading m p) := by rw [abs_of_nonneg hLE.1]
    _ ≤ (4 / ((m - p : ℕ) : ℝ) +
          4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2) +
        (1 / ((m - p : ℕ) : ℝ) - 1 / (m : ℝ)) :=
      add_le_add hVL hLE.2
    _ ≤ 5 / ((m - p : ℕ) : ℝ) +
        4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 := by
      have hmnonneg : 0 ≤ 1 / (m : ℝ) := by positivity
      calc
        (4 / ((m - p : ℕ) : ℝ) +
              4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2) +
            (1 / ((m - p : ℕ) : ℝ) - 1 / (m : ℝ)) =
            (5 / ((m - p : ℕ) : ℝ) +
              4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2) -
                1 / (m : ℝ) := by ring
        _ ≤ 5 / ((m - p : ℕ) : ℝ) +
              4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 :=
          sub_le_self _ hmnonneg

/-- Dilute-safe endpoint comparison between the exact and elementary
variances. -/
theorem abs_nullVSeries_sub_elementaryNullVarianceReal_endpoint_le
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m) :
    |nullVSeries m p - elementaryNullVarianceReal (m : ℝ) (p : ℝ)| ≤
      4 * ((p : ℝ) - 1) / (((m - p + 1 : ℕ) : ℝ) ^ 2) +
        4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 +
        (1 / ((m - p : ℕ) : ℝ) - 1 / (m : ℝ)) := by
  have hVL := abs_nullVSeries_sub_nullVLeading_endpoint_le h
  have hLE := elementaryNullVarianceReal_sub_nullVLeading_bounds h hstrict
  calc
    |nullVSeries m p - elementaryNullVarianceReal (m : ℝ) (p : ℝ)| =
        |(nullVSeries m p - nullVLeading m p) -
          (elementaryNullVarianceReal (m : ℝ) (p : ℝ) -
            nullVLeading m p)| := by ring_nf
    _ ≤ |nullVSeries m p - nullVLeading m p| +
        |elementaryNullVarianceReal (m : ℝ) (p : ℝ) -
          nullVLeading m p| := abs_sub _ _
    _ = |nullVSeries m p - nullVLeading m p| +
        (elementaryNullVarianceReal (m : ℝ) (p : ℝ) -
          nullVLeading m p) := by rw [abs_of_nonneg hLE.1]
    _ ≤ _ := add_le_add hVL hLE.2

/-- In the near-hard-edge region, the elementary variance is at least
`log p - 2`. -/
theorem log_sub_two_le_elementaryNullVarianceReal_of_gap_le_sqrt
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (hgap : (((m - p : ℕ) : ℝ)) ≤ Real.sqrt (p : ℝ)) :
    Real.log (p : ℝ) - 2 ≤
      elementaryNullVarianceReal (m : ℝ) (p : ℝ) := by
  let d : ℕ := m - p
  have hpN : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) h.1
  have hmN : 0 < m := hpN.trans_le h.2
  have hdN : 0 < d := by dsimp [d]; omega
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmN
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hdN
  have hsqrt : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hgap' : (d : ℝ) ≤ Real.sqrt (p : ℝ) := by simpa [d] using hgap
  have hdsqrt : (d : ℝ) * Real.sqrt (p : ℝ) ≤ (p : ℝ) := by
    calc
      (d : ℝ) * Real.sqrt (p : ℝ) ≤
          Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) := by gcongr
      _ = (p : ℝ) := Real.mul_self_sqrt hpR.le
  have hsqrtDiv : Real.sqrt (p : ℝ) ≤ (p : ℝ) / (d : ℝ) :=
    (le_div_iff₀ hdR).2 (by simpa [mul_comm] using hdsqrt)
  have hpDivM : (p : ℝ) / (m : ℝ) ≤ 1 :=
    (div_le_one hmR).2 (by exact_mod_cast h.2)
  have hpDivD_le_mDivD : (p : ℝ) / (d : ℝ) ≤
      (m : ℝ) / (d : ℝ) := by gcongr
  have hlogSqrt : Real.log (Real.sqrt (p : ℝ)) =
      Real.log (p : ℝ) / 2 := Real.log_sqrt hpR.le
  have hlogPD : Real.log (Real.sqrt (p : ℝ)) ≤
      Real.log ((p : ℝ) / (d : ℝ)) :=
    Real.log_le_log hsqrt hsqrtDiv
  have hpDivDpos : 0 < (p : ℝ) / (d : ℝ) := by positivity
  have hlogMD : Real.log ((p : ℝ) / (d : ℝ)) ≤
      Real.log ((m : ℝ) / (d : ℝ)) :=
    Real.log_le_log hpDivDpos hpDivD_le_mDivD
  have hmEq : (p : ℝ) = (m : ℝ) - (d : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub h.2]
    ring
  have hev := elementaryNullVarianceReal_gap_rewrite
    (m := (m : ℝ)) (p := (p : ℝ)) (d := (d : ℝ))
    hmR hdR hmEq
  unfold gapLogReal at hev
  rw [hev, hlogSqrt] at *
  linarith

/-- Endpoint error simplified in the very dilute half `p ≤ m-p`. -/
theorem abs_nullVSeries_sub_elementaryNullVarianceReal_le_nine_p_div_gap_sq
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (hpGap : p ≤ m - p) :
    |nullVSeries m p - elementaryNullVarianceReal (m : ℝ) (p : ℝ)| ≤
      9 * (p : ℝ) / (((m - p : ℕ) : ℝ) ^ 2) := by
  let d : ℕ := m - p
  have hpN : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) h.1
  have hmN : 0 < m := hpN.trans_le h.2
  have hdN : 0 < d := by dsimp [d]; omega
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmN
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hdN
  have hpD : (p : ℝ) ≤ (d : ℝ) := by exact_mod_cast hpGap
  have hdM : (d : ℝ) ≤ (m : ℝ) := by
    dsimp [d]
    exact_mod_cast Nat.sub_le m p
  have hpPred : (p : ℝ) - 1 ≤ (p : ℝ) := by linarith
  have h1 : 4 * ((p : ℝ) - 1) / ((d : ℝ) + 1) ^ 2 ≤
      4 * (p : ℝ) / (d : ℝ) ^ 2 := by gcongr <;> nlinarith
  have h2 : 4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤
      4 * (p : ℝ) / (d : ℝ) ^ 2 := by gcongr <;> nlinarith
  have hmEq : (m : ℝ) = (p : ℝ) + (d : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub h.2]
    ring
  have h3eq : 1 / (d : ℝ) - 1 / (m : ℝ) =
      (p : ℝ) / ((d : ℝ) * (m : ℝ)) := by
    field_simp [hdR.ne', hmR.ne']
    linarith
  have h3 : 1 / (d : ℝ) - 1 / (m : ℝ) ≤
      (p : ℝ) / (d : ℝ) ^ 2 := by
    rw [h3eq]
    have hden : (d : ℝ) ^ 2 ≤ (d : ℝ) * (m : ℝ) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hdM hdR.le
    gcongr
  have hbase := abs_nullVSeries_sub_elementaryNullVarianceReal_endpoint_le
    h hstrict
  dsimp [d] at h1 h2 h3 ⊢
  calc
    |nullVSeries m p - elementaryNullVarianceReal (m : ℝ) (p : ℝ)| ≤
        4 * ((p : ℝ) - 1) /
            (((m - p + 1 : ℕ) : ℝ) ^ 2) +
          4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 +
          (1 / ((m - p : ℕ) : ℝ) - 1 / (m : ℝ)) := hbase
    _ ≤ 4 * (p : ℝ) / (((m - p : ℕ) : ℝ) ^ 2) +
          4 * (p : ℝ) / (((m - p : ℕ) : ℝ) ^ 2) +
          (p : ℝ) / (((m - p : ℕ) : ℝ) ^ 2) := by
      have h1' : 4 * ((p : ℝ) - 1) /
          (((m - p + 1 : ℕ) : ℝ) ^ 2) ≤
          4 * (p : ℝ) / (((m - p : ℕ) : ℝ) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one] using h1
      exact add_le_add (add_le_add h1' h2) h3
    _ = 9 * (p : ℝ) / (((m - p : ℕ) : ℝ) ^ 2) := by ring

/-- Growing-gap error simplified in the complementary half `m-p ≤ p`. -/
theorem abs_nullVSeries_sub_elementaryNullVarianceReal_le_five_div_gap_add_four_div_p
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (hGapP : m - p ≤ p) :
    |nullVSeries m p - elementaryNullVarianceReal (m : ℝ) (p : ℝ)| ≤
      5 / ((m - p : ℕ) : ℝ) + 4 / (p : ℝ) := by
  have hpN : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) h.1
  have hmN : 0 < m := hpN.trans_le h.2
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmN
  have hpM : (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast h.2
  have hpPred : (p : ℝ) - 1 ≤ (p : ℝ) := by linarith
  have hterm : 4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤
      4 / (p : ℝ) := by
    have : ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤ 1 / (p : ℝ) := by
      calc
        ((p : ℝ) - 1) / (m : ℝ) ^ 2 ≤
            (p : ℝ) / (m : ℝ) ^ 2 := by gcongr
        _ ≤ (p : ℝ) / (p : ℝ) ^ 2 := by gcongr
        _ = 1 / (p : ℝ) := by
          field_simp [hpR.ne']
    calc
      4 * ((p : ℝ) - 1) / (m : ℝ) ^ 2 =
          4 * (((p : ℝ) - 1) / (m : ℝ) ^ 2) := by ring
      _ ≤ 4 * (1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left this (by norm_num)
      _ = 4 / (p : ℝ) := by ring
  exact (abs_nullVSeries_sub_elementaryNullVarianceReal_growingGap_le
    h hstrict).trans (add_le_add le_rfl hterm)

/-- Simplified lower bound in the dilute half `p ≤ m-p`. -/
theorem p_sq_div_three_gap_sq_le_elementaryNullVarianceReal
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (hpGap : p ≤ m - p) :
    (p : ℝ) ^ 2 / (3 * (((m - p : ℕ) : ℝ) ^ 2)) ≤
      elementaryNullVarianceReal (m : ℝ) (p : ℝ) := by
  let d : ℕ := m - p
  have hpN : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) h.1
  have hmN : 0 < m := hpN.trans_le h.2
  have hdN : 0 < d := by dsimp [d]; omega
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmN
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hdN
  have hpD : (p : ℝ) ≤ (d : ℝ) := by exact_mod_cast hpGap
  have hmEq : (m : ℝ) = (p : ℝ) + (d : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub h.2]
    ring
  have hmTwoD : (m : ℝ) ≤ 2 * (d : ℝ) := by linarith
  have hmDThreeD : (m : ℝ) + (d : ℝ) ≤ 3 * (d : ℝ) := by
    linarith
  have hden : (m : ℝ) * ((m : ℝ) + (d : ℝ)) ≤
      6 * (d : ℝ) ^ 2 := by nlinarith
  have hbase := elementaryNullVarianceReal_ge_gap_ratio_sq h hstrict
  have hcompare : (p : ℝ) ^ 2 / (3 * (d : ℝ) ^ 2) ≤
      2 * (p : ℝ) ^ 2 /
        ((m : ℝ) * ((m : ℝ) + (d : ℝ))) := by
    rw [le_div_iff₀ (by positivity :
      0 < (m : ℝ) * ((m : ℝ) + (d : ℝ)))]
    calc
      (p : ℝ) ^ 2 / (3 * (d : ℝ) ^ 2) *
          ((m : ℝ) * ((m : ℝ) + (d : ℝ))) ≤
          (p : ℝ) ^ 2 / (3 * (d : ℝ) ^ 2) *
            (6 * (d : ℝ) ^ 2) := by gcongr
      _ = 2 * (p : ℝ) ^ 2 := by
        field_simp [hdR.ne']
        norm_num
  dsimp [d] at hcompare
  exact hcompare.trans hbase

/-- Uniform positive lower bound in the complementary half `m-p ≤ p`. -/
theorem one_third_le_elementaryNullVarianceReal_of_gap_le_p
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (hGapP : m - p ≤ p) :
    (1 / 3 : ℝ) ≤ elementaryNullVarianceReal (m : ℝ) (p : ℝ) := by
  let d : ℕ := m - p
  have hpN : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) h.1
  have hmN : 0 < m := hpN.trans_le h.2
  have hdN : 0 < d := by dsimp [d]; omega
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hmN
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hdN
  have hdP : (d : ℝ) ≤ (p : ℝ) := by exact_mod_cast hGapP
  have hmEq : (m : ℝ) = (p : ℝ) + (d : ℝ) := by
    dsimp [d]
    rw [Nat.cast_sub h.2]
    ring
  have hmTwoP : (m : ℝ) ≤ 2 * (p : ℝ) := by linarith
  have hmDThreeP : (m : ℝ) + (d : ℝ) ≤ 3 * (p : ℝ) := by
    linarith
  have hden : (m : ℝ) * ((m : ℝ) + (d : ℝ)) ≤
      6 * (p : ℝ) ^ 2 := by nlinarith
  have hbase := elementaryNullVarianceReal_ge_gap_ratio_sq h hstrict
  have hcompare : (1 / 3 : ℝ) ≤
      2 * (p : ℝ) ^ 2 /
        ((m : ℝ) * ((m : ℝ) + (d : ℝ))) := by
    rw [le_div_iff₀ (by positivity :
      0 < (m : ℝ) * ((m : ℝ) + (d : ℝ)))]
    nlinarith
  dsimp [d] at hcompare
  exact hcompare.trans hbase

/-- A single finite relative-error envelope, uniform over all strict gaps.
The three summands correspond respectively to the dilute, middle-gap, and
near-hard-edge cases. -/
theorem abs_nullVSeries_div_elementaryNullVarianceReal_sub_one_le
    {m p : ℕ} (h : Admissible m p) (hstrict : p < m)
    (hlog : 2 < Real.log (p : ℝ)) :
    |nullVSeries m p /
          elementaryNullVarianceReal (m : ℝ) (p : ℝ) - 1| ≤
      39 / (p : ℝ) + 15 / Real.sqrt (p : ℝ) +
        9 / (Real.log (p : ℝ) - 2) := by
  let d : ℕ := m - p
  let E : ℝ := elementaryNullVarianceReal (m : ℝ) (p : ℝ)
  have hpN : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) h.1
  have hdN : 0 < d := by dsimp [d]; omega
  have hpR : 0 < (p : ℝ) := Nat.cast_pos.mpr hpN
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hdN
  have hsqrt : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.2 hpR
  have hlogden : 0 < Real.log (p : ℝ) - 2 := sub_pos.mpr hlog
  have hE : 0 < E := elementaryNullVarianceReal_pos_nat h hstrict
  have hid :
      |nullVSeries m p / E - 1| = |nullVSeries m p - E| / E := by
    have hfrac : nullVSeries m p / E - 1 =
        (nullVSeries m p - E) / E := by
      field_simp [hE.ne']
    rw [hfrac, abs_div, abs_of_pos hE]
  by_cases hpGap : p ≤ d
  · have hErr :=
      abs_nullVSeries_sub_elementaryNullVarianceReal_le_nine_p_div_gap_sq
        h hstrict (by simpa [d] using hpGap)
    have hLow := p_sq_div_three_gap_sq_le_elementaryNullVarianceReal
      h hstrict (by simpa [d] using hpGap)
    have h27 : |nullVSeries m p / E - 1| ≤ 27 / (p : ℝ) := by
      rw [hid, div_le_iff₀ hE]
      calc
        |nullVSeries m p - E| ≤
            9 * (p : ℝ) / (d : ℝ) ^ 2 := by
          simpa [E, d] using hErr
        _ = (27 / (p : ℝ)) *
            ((p : ℝ) ^ 2 / (3 * (d : ℝ) ^ 2)) := by
          field_simp [hpR.ne', hdR.ne']
          ring
        _ ≤ (27 / (p : ℝ)) * E := by
          apply mul_le_mul_of_nonneg_left
          · simpa [E, d] using hLow
          · positivity
    calc
      |nullVSeries m p / E - 1| ≤ 27 / (p : ℝ) := h27
      _ ≤ 39 / (p : ℝ) := by gcongr <;> norm_num
      _ ≤ 39 / (p : ℝ) + 15 / Real.sqrt (p : ℝ) :=
        le_add_of_nonneg_right (by positivity)
      _ ≤ 39 / (p : ℝ) + 15 / Real.sqrt (p : ℝ) +
          9 / (Real.log (p : ℝ) - 2) :=
        le_add_of_nonneg_right (by positivity)
  · have hGapP : d ≤ p := by omega
    have hErr :=
      abs_nullVSeries_sub_elementaryNullVarianceReal_le_five_div_gap_add_four_div_p
        h hstrict (by simpa [d] using hGapP)
    by_cases hsqrtGap : Real.sqrt (p : ℝ) < (d : ℝ)
    · have hInv : 1 / (d : ℝ) ≤ 1 / Real.sqrt (p : ℝ) := by
        exact one_div_le_one_div_of_le hsqrt hsqrtGap.le
      have hErr' : |nullVSeries m p - E| ≤
          5 / Real.sqrt (p : ℝ) + 4 / (p : ℝ) := by
        have hfive : 5 / (d : ℝ) ≤
            5 / Real.sqrt (p : ℝ) := by
          calc
            5 / (d : ℝ) = 5 * (1 / (d : ℝ)) := by ring
            _ ≤ 5 * (1 / Real.sqrt (p : ℝ)) := by gcongr
            _ = 5 / Real.sqrt (p : ℝ) := by ring
        have hErrBase : |nullVSeries m p - E| ≤
            5 / (d : ℝ) + 4 / (p : ℝ) := by
          simpa [E, d] using hErr
        exact hErrBase.trans (add_le_add hfive le_rfl)
      have hLow := one_third_le_elementaryNullVarianceReal_of_gap_le_p
        h hstrict (by simpa [d] using hGapP)
      have hmid : |nullVSeries m p / E - 1| ≤
          15 / Real.sqrt (p : ℝ) + 12 / (p : ℝ) := by
        rw [hid, div_le_iff₀ hE]
        calc
          |nullVSeries m p - E| ≤
              5 / Real.sqrt (p : ℝ) + 4 / (p : ℝ) := hErr'
          _ = (15 / Real.sqrt (p : ℝ) + 12 / (p : ℝ)) *
              (1 / 3 : ℝ) := by ring
          _ ≤ (15 / Real.sqrt (p : ℝ) + 12 / (p : ℝ)) * E := by
            apply mul_le_mul_of_nonneg_left
            · simpa [E] using hLow
            · positivity
      calc
        |nullVSeries m p / E - 1| ≤
            15 / Real.sqrt (p : ℝ) + 12 / (p : ℝ) := hmid
        _ ≤ 15 / Real.sqrt (p : ℝ) + 39 / (p : ℝ) := by
          gcongr <;> norm_num
        _ = 39 / (p : ℝ) + 15 / Real.sqrt (p : ℝ) := by ring
        _ ≤ 39 / (p : ℝ) + 15 / Real.sqrt (p : ℝ) +
            9 / (Real.log (p : ℝ) - 2) :=
          le_add_of_nonneg_right (by positivity)
    · have hgapSqrt : (d : ℝ) ≤ Real.sqrt (p : ℝ) :=
        le_of_not_gt hsqrtGap
      have hErr9 : |nullVSeries m p - E| ≤ 9 := by
        have hdOne : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdN
        have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h.1
        have hfive : 5 / (d : ℝ) ≤ 5 := by
          rw [div_le_iff₀ hdR]
          nlinarith
        have hfour : 4 / (p : ℝ) ≤ 2 := by
          rw [div_le_iff₀ hpR]
          nlinarith
        have hErrBase : |nullVSeries m p - E| ≤
            5 / (d : ℝ) + 4 / (p : ℝ) := by
          simpa [E, d] using hErr
        have hErr7 : |nullVSeries m p - E| ≤ 7 :=
          hErrBase.trans (by linarith)
        linarith
      have hLow := log_sub_two_le_elementaryNullVarianceReal_of_gap_le_sqrt
        h hstrict (by simpa [d] using hgapSqrt)
      have hhard : |nullVSeries m p / E - 1| ≤
          9 / (Real.log (p : ℝ) - 2) := by
        rw [hid, div_le_iff₀ hE]
        calc
          |nullVSeries m p - E| ≤ 9 := hErr9
          _ = (9 / (Real.log (p : ℝ) - 2)) *
              (Real.log (p : ℝ) - 2) := by
            field_simp [hlogden.ne']
          _ ≤ (9 / (Real.log (p : ℝ) - 2)) * E := by
            apply mul_le_mul_of_nonneg_left
            · simpa [E] using hLow
            · positivity
      calc
        |nullVSeries m p / E - 1| ≤
            9 / (Real.log (p : ℝ) - 2) := hhard
        _ ≤ (39 / (p : ℝ) + 15 / Real.sqrt (p : ℝ)) +
            9 / (Real.log (p : ℝ) - 2) :=
          le_add_of_nonneg_left (by positivity)

/-- Explicit dimension-only envelope for the exact-to-elementary variance
ratio. -/
def elementaryVarianceRelativeErrorEnvelope (p : ℕ) : ℝ :=
  39 / (p : ℝ) + 15 / Real.sqrt (p : ℝ) +
    9 / (Real.log (p : ℝ) - 2)

/-- The explicit uniform variance-ratio envelope tends to zero. -/
theorem tendsto_elementaryVarianceRelativeErrorEnvelope_zero :
    Tendsto elementaryVarianceRelativeErrorEnvelope atTop (nhds 0) := by
  have hcast : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun p : ℕ ↦ Real.sqrt (p : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hlog : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hlogsub : Tendsto (fun p : ℕ ↦ Real.log (p : ℝ) - 2)
      atTop atTop := by
    simpa [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-2 : ℝ) hlog
  have h1 : Tendsto (fun p : ℕ ↦ 39 / (p : ℝ)) atTop (nhds 0) :=
    hcast.const_div_atTop 39
  have h2 : Tendsto (fun p : ℕ ↦ 15 / Real.sqrt (p : ℝ))
      atTop (nhds 0) := hsqrt.const_div_atTop 15
  have h3 : Tendsto (fun p : ℕ ↦ 9 / (Real.log (p : ℝ) - 2))
      atTop (nhds 0) := hlogsub.const_div_atTop 9
  unfold elementaryVarianceRelativeErrorEnvelope
  simpa using (h1.add h2).add h3

/-- Lemma 5.6, variance half: along every eventually admissible strict-gap
triangular array with `p -> infinity`, the exact trigamma variance divided by
the elementary variance tends to one. -/
theorem tendsto_nullVSeries_div_elementaryNullVarianceReal
    (mseq pseq : ℕ → ℕ)
    (hp : Tendsto pseq atTop atTop)
    (hadm : ∀ᶠ n in atTop, Admissible (mseq n) (pseq n))
    (hstrict : ∀ᶠ n in atTop, pseq n < mseq n) :
    Tendsto (fun n ↦
      nullVSeries (mseq n) (pseq n) /
        elementaryNullVarianceReal (mseq n : ℝ) (pseq n : ℝ))
      atTop (nhds 1) := by
  have hlog : Tendsto (fun n ↦ Real.log (pseq n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hp)
  have hlogEventually : ∀ᶠ n in atTop, 2 < Real.log (pseq n : ℝ) :=
    (tendsto_atTop.1 hlog 3).mono fun n hn ↦ by linarith
  have henv := tendsto_elementaryVarianceRelativeErrorEnvelope_zero.comp hp
  have habs : Tendsto (fun n ↦
      |nullVSeries (mseq n) (pseq n) /
          elementaryNullVarianceReal (mseq n : ℝ) (pseq n : ℝ) - 1|)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Filter.Eventually.of_forall fun _ ↦ abs_nonneg _
    · filter_upwards [hadm, hstrict, hlogEventually] with n hn hs hl
      exact abs_nullVSeries_div_elementaryNullVarianceReal_sub_one_le hn hs hl
    · exact henv
  have hsub : Tendsto (fun n ↦
      nullVSeries (mseq n) (pseq n) /
          elementaryNullVarianceReal (mseq n : ℝ) (pseq n : ℝ) - 1)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    simpa [Function.comp_def] using habs
  have hsum : Tendsto (fun n ↦
      1 + (nullVSeries (mseq n) (pseq n) /
          elementaryNullVarianceReal (mseq n : ℝ) (pseq n : ℝ) - 1))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hsub :
      Tendsto (fun n ↦ (1 : ℝ) +
        (nullVSeries (mseq n) (pseq n) /
          elementaryNullVarianceReal (mseq n : ℝ) (pseq n : ℝ) - 1))
        atTop (nhds (1 + 0)))
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun n ↦ by ring

end

end LogdetLean
