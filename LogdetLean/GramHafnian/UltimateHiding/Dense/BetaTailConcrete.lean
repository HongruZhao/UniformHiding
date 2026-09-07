import LogdetLean.GramHafnian.UltimateHiding.Dense.TailSeries
import LogdetLean.GramHafnian.RankTwoOuterBeta
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Concrete beta exceptional events

This file connects the scalar beta law used by the one-column kernel to the
bad logarithmic event.  It proves the support and event algebra for the
literal `betaMeasure`, evaluates the deleted-radius moment as a rising-factorial
ratio, and closes the Markov bound and infinite telescope with explicit
constants.
-/

open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open LogdetLean.GramHafnian

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

/-- The deleted squared radius `1-q` as a concrete pushforward of the beta
variable `q`. -/
def oneColumnDeletedRadiusLaw (m N : ℕ) : Measure ℝ :=
  Measure.map (fun q : ℝ ↦ 1 - q) (oneColumnBetaLaw m N)

theorem oneColumnDeletedRadiusLaw_isProbability
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    IsProbabilityMeasure (oneColumnDeletedRadiusLaw m N) := by
  let _ : IsProbabilityMeasure (oneColumnBetaLaw m N) :=
    oneColumnBetaLaw_isProbability hN hNm
  unfold oneColumnDeletedRadiusLaw
  exact Measure.isProbabilityMeasure_map (by fun_prop :
    AEMeasurable (fun q : ℝ ↦ 1 - q) (oneColumnBetaLaw m N))

theorem betaMeasure_Iic_zero (α β : ℝ) :
    betaMeasure α β (Iic 0) = 0 := by
  rw [betaMeasure, MeasureTheory.withDensity_apply _ measurableSet_Iic]
  exact setLIntegral_eq_zero measurableSet_Iic
    (fun q hq ↦ betaPDF_eq_zero_of_nonpos hq)

theorem betaMeasure_Ici_one (α β : ℝ) :
    betaMeasure α β (Ici 1) = 0 := by
  rw [betaMeasure, MeasureTheory.withDensity_apply _ measurableSet_Ici]
  exact setLIntegral_eq_zero measurableSet_Ici
    (fun q hq ↦ betaPDF_eq_zero_of_one_le hq)

/-- The complement of the open unit interval is null for the literal beta
law. -/
theorem oneColumnBetaLaw_compl_Ioo_eq_zero (m N : ℕ) :
    oneColumnBetaLaw m N ((Ioo 0 1)ᶜ) = 0 := by
  have heq : (Ioo (0 : ℝ) 1)ᶜ = Iic 0 ∪ Ici 1 := by
    ext q
    simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt, mem_union,
      mem_Iic, mem_Ici]
  rw [heq]
  apply le_antisymm
  · calc
      oneColumnBetaLaw m N (Iic 0 ∪ Ici 1)
          ≤ oneColumnBetaLaw m N (Iic 0) +
              oneColumnBetaLaw m N (Ici 1) := measure_union_le _ _
      _ = 0 := by
        simp [oneColumnBetaLaw, betaMeasure_Iic_zero,
          betaMeasure_Ici_one]
  · exact bot_le

/-- The concrete beta law is concentrated on the open unit interval. -/
theorem oneColumnBetaLaw_Ioo_eq_one
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    oneColumnBetaLaw m N (Ioo 0 1) = 1 := by
  let _ : IsProbabilityMeasure (oneColumnBetaLaw m N) :=
    oneColumnBetaLaw_isProbability hN hNm
  have hcompl := oneColumnBetaLaw_compl_Ioo_eq_zero m N
  rw [measure_of_measure_compl_eq_zero hcompl]
  exact measure_univ

/-- The literal logarithmic bad event in the proof note. -/
def oneColumnLogBadEvent (N : ℕ) (c0 : ℝ) : Set ℝ :=
  {q | |oneColumnRankOneLog q| > c0 / (N : ℝ)}

/-- The corresponding deleted-radius threshold. -/
def oneColumnDeletedRadiusThreshold (N : ℕ) (c0 : ℝ) : ℝ :=
  1 - Real.exp (-2 * c0 / (N : ℝ))

theorem measurableSet_oneColumnLogBadEvent (N : ℕ) (c0 : ℝ) :
    MeasurableSet (oneColumnLogBadEvent N c0) := by
  unfold oneColumnLogBadEvent oneColumnRankOneLog
  exact measurableSet_lt (by fun_prop) (by fun_prop)

/-- On the beta support `0 < q < 1`, the logarithmic bad event is exactly a
large deleted-radius event. -/
theorem mem_oneColumnLogBadEvent_iff
    {N : ℕ} (hN : 1 ≤ N) {c0 q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    q ∈ oneColumnLogBadEvent N c0 ↔
      oneColumnDeletedRadiusThreshold N c0 < 1 - q := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hlog : Real.log q < 0 := Real.log_neg hq0 hq1
  have hbnonpos : oneColumnRankOneLog q ≤ 0 := by
    unfold oneColumnRankOneLog
    nlinarith
  rw [oneColumnLogBadEvent, Set.mem_ofPred_eq, abs_of_nonpos hbnonpos,
    oneColumnRankOneLog, oneColumnDeletedRadiusThreshold]
  constructor
  · intro h
    have hloglt : Real.log q < -2 * c0 / (N : ℝ) := by
      norm_num [div_eq_mul_inv] at h ⊢
      nlinarith
    have hexp := Real.exp_lt_exp.mpr hloglt
    rw [Real.exp_log hq0] at hexp
    linarith
  · intro h
    have hqexp : q < Real.exp (-2 * c0 / (N : ℝ)) := by linarith
    have hloglt : Real.log q < -2 * c0 / (N : ℝ) :=
      Real.exp_lt_exp.mp (by simpa [Real.exp_log hq0] using hqexp)
    norm_num [div_eq_mul_inv] at hloglt ⊢
    nlinarith

/-- The beta probability of the logarithmic exceptional event is exactly the
upper-tail probability of the concrete deleted-radius pushforward. -/
theorem oneColumnLogBadProbability_eq_deletedRadius
    {m N : ℕ} (hN : 1 ≤ N) (_hNm : N ≤ m) (c0 : ℝ) :
    oneColumnBetaLaw m N (oneColumnLogBadEvent N c0) =
      oneColumnDeletedRadiusLaw m N
        (Ioi (oneColumnDeletedRadiusThreshold N c0)) := by
  let μ := oneColumnBetaLaw m N
  let support : Set ℝ := Ioo 0 1
  let radiusEvent : Set ℝ :=
    (fun q : ℝ ↦ 1 - q) ⁻¹' Ioi (oneColumnDeletedRadiusThreshold N c0)
  have hnull : μ supportᶜ = 0 := by
    exact oneColumnBetaLaw_compl_Ioo_eq_zero m N
  have hset : oneColumnLogBadEvent N c0 ∩ support =
      radiusEvent ∩ support := by
    ext q
    constructor
    · intro hq
      exact ⟨(mem_oneColumnLogBadEvent_iff hN hq.2.1 hq.2.2).mp hq.1,
        hq.2⟩
    · intro hq
      exact ⟨(mem_oneColumnLogBadEvent_iff hN hq.2.1 hq.2.2).mpr hq.1,
        hq.2⟩
  calc
    oneColumnBetaLaw m N (oneColumnLogBadEvent N c0) =
        μ (oneColumnLogBadEvent N c0 ∩ support) := by
          symm
          exact measure_inter_conull hnull
    _ = μ (radiusEvent ∩ support) := congrArg μ hset
    _ = μ radiusEvent := measure_inter_conull hnull
    _ = oneColumnDeletedRadiusLaw m N
        (Ioi (oneColumnDeletedRadiusThreshold N c0)) := by
          rw [oneColumnDeletedRadiusLaw,
            Measure.map_apply (by fun_prop : Measurable fun q : ℝ ↦ 1 - q)
              measurableSet_Ioi]

/-- Raw `p`th moment of the concrete deleted radius, in the extended
nonnegative reals used by Markov's inequality. -/
def oneColumnDeletedRadiusMoment (m N p : ℕ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ, ENNReal.ofReal (x ^ p) ∂(oneColumnDeletedRadiusLaw m N)

/-- Multiplying a beta density by a natural power of the complementary
coordinate shifts its right shape parameter. -/
theorem betaPDF_mul_one_sub_pow
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (p : ℕ) (x : ℝ) :
    betaPDF α β x * ENNReal.ofReal ((1 - x) ^ p) =
      ENNReal.ofReal (beta α (β + p) / beta α β) *
        betaPDF α (β + p) x := by
  have hβp : 0 < β + (p : ℝ) := by positivity
  by_cases hx : 0 < x ∧ x < 1
  · rw [betaPDF_of_pos_lt_one hx.1 hx.2,
      betaPDF_of_pos_lt_one hx.1 hx.2]
    have hbase : 0 < 1 - x := sub_pos.mpr hx.2
    have hpdf : 0 ≤ (1 / beta α β) * x ^ (α - 1) *
        (1 - x) ^ (β - 1) := by
      exact mul_nonneg
        (mul_nonneg (one_div_nonneg.mpr (beta_pos hα hβ).le)
          (Real.rpow_nonneg hx.1.le _))
        (Real.rpow_nonneg hbase.le _)
    have hpow : 0 ≤ (1 - x) ^ p := pow_nonneg hbase.le p
    have hratio : 0 ≤ beta α (β + p) / beta α β :=
      div_nonneg (beta_pos hα hβp).le (beta_pos hα hβ).le
    have hpdfp : 0 ≤ (1 / beta α (β + p)) * x ^ (α - 1) *
        (1 - x) ^ (β + p - 1) := by
      exact mul_nonneg
        (mul_nonneg (one_div_nonneg.mpr (beta_pos hα hβp).le)
          (Real.rpow_nonneg hx.1.le _))
        (Real.rpow_nonneg hbase.le _)
    rw [← ENNReal.ofReal_mul hpdf, ← ENNReal.ofReal_mul hratio]
    apply congrArg ENNReal.ofReal
    have hpowadd : (1 - x) ^ (β + p - 1) =
        (1 - x) ^ (β - 1) * (1 - x) ^ p := by
      rw [show β + (p : ℝ) - 1 = (β - 1) + (p : ℝ) by ring,
        Real.rpow_add hbase, Real.rpow_natCast]
    rw [hpowadd]
    field_simp [ne_of_gt (beta_pos hα hβ), ne_of_gt (beta_pos hα hβp)]
  · have hxp : ¬ (0 < x ∧ x < 1) := hx
    rw [betaPDF_eq, betaPDF_eq, if_neg hxp, if_neg hxp]
    simp

/-- Exact natural complementary-coordinate moment of a beta law. -/
theorem lintegral_one_sub_pow_betaMeasure
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (p : ℕ) :
    (∫⁻ x : ℝ, ENNReal.ofReal ((1 - x) ^ p) ∂betaMeasure α β) =
      ENNReal.ofReal (beta α (β + p) / beta α β) := by
  have hpdf : Measurable (betaPDF α β) :=
    (measurable_betaPDFReal α β).ennreal_ofReal
  have hpdfp : Measurable (betaPDF α (β + p)) :=
    (measurable_betaPDFReal α (β + p)).ennreal_ofReal
  calc
    (∫⁻ x : ℝ, ENNReal.ofReal ((1 - x) ^ p) ∂betaMeasure α β) =
        ∫⁻ x : ℝ, betaPDF α β x * ENNReal.ofReal ((1 - x) ^ p) := by
          exact lintegral_withDensity_eq_lintegral_mul volume hpdf (by fun_prop)
    _ = ∫⁻ x : ℝ, ENNReal.ofReal (beta α (β + p) / beta α β) *
          betaPDF α (β + p) x :=
      lintegral_congr fun x ↦ betaPDF_mul_one_sub_pow hα hβ p x
    _ = ENNReal.ofReal (beta α (β + p) / beta α β) := by
      rw [lintegral_const_mul _ hpdfp,
        lintegral_betaPDF_eq_one hα (by positivity)]
      simp

/-- Shifting the right beta shape by a natural number gives the corresponding
rising-factorial ratio.  This is the complementary-coordinate form of
`integral_pow_betaMeasure_eq_rising_ratio`. -/
theorem beta_shift_right_div_eq_rising_ratio
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (j : ℕ) :
    beta a (b + j) / beta a b = rising b j / rising (a + b) j := by
  unfold beta
  rw [gamma_add_nat_eq_rising_mul b j hb]
  have hab : 0 < a + b := add_pos ha hb
  rw [show a + (b + (j : ℝ)) = (a + b) + j by ring,
    gamma_add_nat_eq_rising_mul (a + b) j hab]
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hGb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hGab : Real.Gamma (a + b) ≠ 0 :=
    (Real.Gamma_pos_of_pos hab).ne'
  have hrb : rising b j ≠ 0 := ne_of_gt (rising_pos hb j)
  have hrab : rising (a + b) j ≠ 0 := ne_of_gt (rising_pos hab j)
  field_simp [hGa, hGb, hGab, hrb, hrab]

/-- The deleted-radius moment as an exact beta-function quotient. -/
theorem oneColumnDeletedRadiusMoment_eq_betaRatio
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) (p : ℕ) :
    oneColumnDeletedRadiusMoment m N p =
      ENNReal.ofReal
        (beta (oneColumnBetaShapeLeft m N)
            (oneColumnBetaShapeRight N + p) /
          beta (oneColumnBetaShapeLeft m N)
            (oneColumnBetaShapeRight N)) := by
  rw [oneColumnDeletedRadiusMoment, oneColumnDeletedRadiusLaw,
    lintegral_map (by fun_prop) (by fun_prop)]
  exact lintegral_one_sub_pow_betaMeasure
    (oneColumnBetaShapeLeft_pos hNm)
    (oneColumnBetaShapeRight_pos hN) p

/-- The same moment in rising-factorial form. -/
theorem oneColumnDeletedRadiusMoment_eq_risingRatio
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) (p : ℕ) :
    oneColumnDeletedRadiusMoment m N p =
      ENNReal.ofReal
        (rising (oneColumnBetaShapeRight N) p /
          rising (oneColumnBetaShapeLeft m N +
            oneColumnBetaShapeRight N) p) := by
  rw [oneColumnDeletedRadiusMoment_eq_betaRatio hN hNm p,
    beta_shift_right_div_eq_rising_ratio
      (oneColumnBetaShapeLeft_pos hNm)
      (oneColumnBetaShapeRight_pos hN)]

theorem oneColumnBetaShape_sum (m N : ℕ) :
    oneColumnBetaShapeLeft m N + oneColumnBetaShapeRight N =
      (m : ℝ) + 1 := by
  simp [oneColumnBetaShapeLeft, oneColumnBetaShapeRight]
  ring

/-- Literal natural-parameter form: the deleted radius has the natural beta
moment `(N)_p/(m+1)_p`. -/
theorem oneColumnDeletedRadiusMoment_eq_naturalRisingRatio
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) (p : ℕ) :
    oneColumnDeletedRadiusMoment m N p =
      ENNReal.ofReal
        (rising (N : ℝ) p / rising ((m : ℝ) + 1) p) := by
  rw [oneColumnDeletedRadiusMoment_eq_risingRatio hN hNm p]
  simp only [oneColumnBetaShapeRight]
  rw [show oneColumnBetaShapeLeft m N + (N : ℝ) = (m : ℝ) + 1 by
    simpa [oneColumnBetaShapeRight] using oneColumnBetaShape_sum m N]

/-- Uniform finite-product bound for every exponent up to `N+2`. -/
theorem oneColumn_rising_ratio_le
    {m N j : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (hj : j ≤ N + 2) :
    rising (N : ℝ) j / rising ((m : ℝ) + 1) j ≤
      (3 * (N : ℝ) / (m : ℝ)) ^ j := by
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < N) hNm)
  induction j with
  | zero => simp
  | succ j ih =>
      have hj' : j ≤ N + 2 := by omega
      have ih' := ih hj'
      rw [rising_succ, rising_succ, pow_succ]
      have hden0 : rising ((m : ℝ) + 1) j ≠ 0 :=
        ne_of_gt (rising_pos (by positivity) j)
      have hnewden : (m : ℝ) + 1 + j ≠ 0 := by positivity
      have hratio :
          rising (N : ℝ) j * ((N : ℝ) + j) /
              (rising ((m : ℝ) + 1) j * ((m : ℝ) + 1 + j)) =
            (rising (N : ℝ) j / rising ((m : ℝ) + 1) j) *
              (((N : ℝ) + j) / ((m : ℝ) + 1 + j)) := by
        field_simp [hden0, hnewden]
      rw [hratio]
      have hfactor : ((N : ℝ) + j) / ((m : ℝ) + 1 + j) ≤
          3 * (N : ℝ) / (m : ℝ) := by
        have hnum : (N : ℝ) + j ≤ 3 * (N : ℝ) := by
          have hjN : j ≤ N + 1 := by omega
          exact_mod_cast (by omega : N + j ≤ 3 * N)
        have hden : (m : ℝ) ≤ (m : ℝ) + 1 + j := by
          have hjR : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
          linarith
        calc
          ((N : ℝ) + j) / ((m : ℝ) + 1 + j) ≤
              (3 * (N : ℝ)) / ((m : ℝ) + 1 + j) := by
                gcongr
          _ ≤ (3 * (N : ℝ)) / (m : ℝ) := by
                exact div_le_div_of_nonneg_left (by positivity) hmR hden
      exact mul_le_mul ih' hfactor
        (div_nonneg (by positivity) (by positivity))
        (pow_nonneg (by positivity) j)

/-- The exact `(N+2)` moment is bounded by `(3N/m)^(N+2)`. -/
theorem oneColumnDeletedRadiusMoment_N_add_two_le
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    oneColumnDeletedRadiusMoment m N (N + 2) ≤
      ENNReal.ofReal ((3 * (N : ℝ) / (m : ℝ)) ^ (N + 2)) := by
  rw [oneColumnDeletedRadiusMoment_eq_naturalRisingRatio hN hNm]
  exact ENNReal.ofReal_le_ofReal
    (oneColumn_rising_ratio_le hN hNm (by rfl))

/-- Markov's inequality for the literal deleted-radius law, with no moment
formula assumed. -/
theorem oneColumnDeletedRadius_markov
    (m N p : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ENNReal.ofReal (ε ^ p) *
        oneColumnDeletedRadiusLaw m N (Ioi ε) ≤
      oneColumnDeletedRadiusMoment m N p := by
  let f : ℝ → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (x ^ p)
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hsubset : Ioi ε ⊆ {x | ENNReal.ofReal (ε ^ p) ≤ f x} := by
    intro x hx
    have hp : ε ^ p ≤ x ^ p := pow_le_pow_left₀ hε hx.le p
    exact ENNReal.ofReal_le_ofReal hp
  calc
    ENNReal.ofReal (ε ^ p) * oneColumnDeletedRadiusLaw m N (Ioi ε)
        ≤ ENNReal.ofReal (ε ^ p) *
            oneColumnDeletedRadiusLaw m N
              {x | ENNReal.ofReal (ε ^ p) ≤ f x} :=
          by
            simpa [mul_comm] using
              mul_le_mul_left (measure_mono hsubset) (ENNReal.ofReal (ε ^ p))
    _ ≤ ∫⁻ x, f x ∂(oneColumnDeletedRadiusLaw m N) :=
      mul_meas_ge_le_lintegral hf (ENNReal.ofReal (ε ^ p))
    _ = oneColumnDeletedRadiusMoment m N p := rfl

theorem oneColumnDeletedRadiusThreshold_pos
    {N : ℕ} (hN : 1 ≤ N) {c0 : ℝ} (hc0 : 0 < c0) :
    0 < oneColumnDeletedRadiusThreshold N c0 := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hexponent : -2 * c0 / (N : ℝ) < 0 :=
    div_neg_of_neg_of_pos (by nlinarith) hNR
  unfold oneColumnDeletedRadiusThreshold
  have hexp : Real.exp (-2 * c0 / (N : ℝ)) < 1 := by
    simpa using Real.exp_lt_one_iff.mpr hexponent
  linarith

/-- At the fixed cutoff `c0=1`, the deleted-radius threshold is at least
`1/(2N)`.  The estimate includes `N=1`. -/
theorem oneColumnDeletedRadiusThreshold_one_lower
    {N : ℕ} (hN : 1 ≤ N) :
    1 / (2 * (N : ℝ)) ≤ oneColumnDeletedRadiusThreshold N 1 := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  let x : ℝ := 2 / (N : ℝ)
  have hx : 0 < x := div_pos (by norm_num) hNR
  have hexp : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hinv : 1 / Real.exp x ≤ 1 / (1 + x) :=
    one_div_le_one_div_of_le (by linarith) hexp
  have hneg : Real.exp (-x) ≤ 1 / (1 + x) := by
    simpa [Real.exp_neg] using hinv
  have hfrac : 1 / (2 * (N : ℝ)) ≤ x / (1 + x) := by
    dsimp [x]
    have h2N : 0 < 2 * (N : ℝ) := by positivity
    have hNp2 : 0 < (N : ℝ) + 2 := by positivity
    have hN1R : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    field_simp
    nlinarith
  unfold oneColumnDeletedRadiusThreshold
  have harg : -2 * (1 : ℝ) / (N : ℝ) = -x := by
    dsimp [x]
    ring
  rw [harg]
  have hidentity : x / (1 + x) = 1 - 1 / (1 + x) := by
    field_simp
    ring
  rw [hidentity] at hfrac
  linarith

/-- The exact Markov reduction for the beta logarithmic bad event. -/
theorem oneColumnLogBad_markov_moment
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) {c0 : ℝ} (hc0 : 0 < c0) :
    ENNReal.ofReal
        (oneColumnDeletedRadiusThreshold N c0 ^ (N + 2)) *
        oneColumnBetaLaw m N (oneColumnLogBadEvent N c0) ≤
      oneColumnDeletedRadiusMoment m N (N + 2) := by
  rw [oneColumnLogBadProbability_eq_deletedRadius hN hNm c0]
  exact oneColumnDeletedRadius_markov m N (N + 2)
    (oneColumnDeletedRadiusThreshold_pos hN hc0).le

/-- Literal real-valued probability of the one-column logarithmic bad event. -/
def oneColumnLogBadProbability (m N : ℕ) (c0 : ℝ) : ℝ :=
  (oneColumnBetaLaw m N).real (oneColumnLogBadEvent N c0)

theorem oneColumnLogBadProbability_nonneg (m N : ℕ) (c0 : ℝ) :
    0 ≤ oneColumnLogBadProbability m N c0 := by
  exact measureReal_nonneg

/-- Fully explicit beta bad-tail estimate at cutoff `c0=1`.  The constant
`6` comes from the exact beta moment, the bound
`(N)_{N+2}/(m+1)_{N+2} <= (3N/m)^(N+2)`, and the threshold
`1-exp(-2/N) >= 1/(2N)`. -/
theorem oneColumnLogBadProbability_le_six
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    oneColumnLogBadProbability m N 1 ≤
      (6 * (N : ℝ) ^ 2 / (m : ℝ)) ^ (N + 2) := by
  let T := oneColumnDeletedRadiusThreshold N 1
  let R := (6 * (N : ℝ) ^ 2 / (m : ℝ)) ^ (N + 2)
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < N) hNm)
  have hTpos : 0 < T := oneColumnDeletedRadiusThreshold_pos hN (by norm_num)
  have hTlower : 1 / (2 * (N : ℝ)) ≤ T :=
    oneColumnDeletedRadiusThreshold_one_lower hN
  have hRnonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hbase : 3 * (N : ℝ) / (m : ℝ) ≤
      T * (6 * (N : ℝ) ^ 2 / (m : ℝ)) := by
    calc
      3 * (N : ℝ) / (m : ℝ) =
          (1 / (2 * (N : ℝ))) *
            (6 * (N : ℝ) ^ 2 / (m : ℝ)) := by
              have hNR : (N : ℝ) ≠ 0 := by positivity
              have hmR : (m : ℝ) ≠ 0 := ne_of_gt hmpos
              field_simp [hNR, hmR]
              ring
      _ ≤ T * (6 * (N : ℝ) ^ 2 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hTlower (by positivity)
  have hpowers : (3 * (N : ℝ) / (m : ℝ)) ^ (N + 2) ≤
      T ^ (N + 2) * R := by
    have hpow := pow_le_pow_left₀ (by positivity) hbase (N + 2)
    simpa [R, mul_pow] using hpow
  have hmarkov := oneColumnLogBad_markov_moment hN hNm
    (c0 := (1 : ℝ)) (by norm_num)
  have hmoment := oneColumnDeletedRadiusMoment_N_add_two_le hN hNm
  have hchain :
      ENNReal.ofReal (T ^ (N + 2)) *
          oneColumnBetaLaw m N (oneColumnLogBadEvent N 1) ≤
        ENNReal.ofReal (T ^ (N + 2)) * ENNReal.ofReal R := by
    calc
      ENNReal.ofReal (T ^ (N + 2)) *
          oneColumnBetaLaw m N (oneColumnLogBadEvent N 1) ≤
          oneColumnDeletedRadiusMoment m N (N + 2) := by
            simpa [T] using hmarkov
      _ ≤ ENNReal.ofReal ((3 * (N : ℝ) / (m : ℝ)) ^ (N + 2)) :=
        hmoment
      _ ≤ ENNReal.ofReal (T ^ (N + 2) * R) :=
        ENNReal.ofReal_le_ofReal hpowers
      _ = ENNReal.ofReal (T ^ (N + 2)) * ENNReal.ofReal R := by
        rw [ENNReal.ofReal_mul (pow_nonneg hTpos.le (N + 2))]
  have hfac0 : ENNReal.ofReal (T ^ (N + 2)) ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    positivity
  have hfacTop : ENNReal.ofReal (T ^ (N + 2)) ≠ ∞ := ENNReal.ofReal_ne_top
  have hevent : oneColumnBetaLaw m N (oneColumnLogBadEvent N 1) ≤
      ENNReal.ofReal R := by
    apply (ENNReal.mul_le_mul_iff_left hfac0 hfacTop).mp
    simpa [mul_comm] using hchain
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hevent
  simpa [oneColumnLogBadProbability, Measure.real, R, hRnonneg] using hreal

/-- Abstract pointwise beta-tail input consumed by the telescope.  The literal
beta law satisfies this proposition with `A=6` and `c0=1`, as proved below. -/
def OneColumnBetaTailBoundAt
    (A c0 : ℝ) (N M : ℕ) : Prop :=
  ∀ j : ℕ,
    oneColumnLogBadProbability (M + j) N c0 ≤
      denseBadTailTerm A N M j

/-- The pointwise beta-tail interface is discharged internally, with explicit
constant `A=6` and cutoff `c0=1`. -/
theorem oneColumnBetaTailBoundAt_six
    {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    OneColumnBetaTailBoundAt 6 1 N M := by
  intro j
  have hNMj : N ≤ M + j := hNM.trans (Nat.le_add_right M j)
  simpa [denseBadTailTerm] using
    (oneColumnLogBadProbability_le_six hN hNMj)

/-- Pointwise exceptional-event budget in exactly the reciprocal-product
normalization of the dense telescope.  Thus the bad event can be absorbed
into the same one-column coefficient as the smooth score contribution,
rather than being left as a separate summable remainder. -/
theorem oneColumnLogBadProbability_le_telescopingRate_concrete
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m)
    (hthreshold : 24 * (N : ℝ) ^ 2 ≤ (m : ℝ)) :
    oneColumnLogBadProbability m N 1 ≤
      denseTelescopingRate 72 N m := by
  have hm : 1 ≤ m := hN.trans hNm
  have hprob := oneColumnLogBadProbability_le_six hN hNm
  have htail := denseBadTailTerm_zero_le_telescopingRate
    (A := (6 : ℝ)) (by norm_num) hN hm (by
      norm_num at hthreshold ⊢
      exact hthreshold)
  exact hprob.trans <| by
    norm_num at htail ⊢
    simpa [denseBadTailTerm] using htail

/-- Finite summation for the actual beta bad-event probabilities. -/
theorem sum_oneColumnLogBadProbability_le
    {A c0 : ℝ} (hA : 0 ≤ A) {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hthreshold : 4 * A * (N : ℝ) ^ 2 ≤ (M : ℝ))
    (hbeta : OneColumnBetaTailBoundAt A c0 N M) (L : ℕ) :
    (∑ j ∈ Finset.range L,
      oneColumnLogBadProbability (M + j) N c0) ≤
      2 * A ^ 2 * (N : ℝ) ^ 2 / (M : ℝ) := by
  calc
    (∑ j ∈ Finset.range L,
        oneColumnLogBadProbability (M + j) N c0)
        ≤ ∑ j ∈ Finset.range L, denseBadTailTerm A N M j := by
          exact Finset.sum_le_sum fun j _ ↦ hbeta j
    _ ≤ 2 * A ^ 2 * (N : ℝ) ^ 2 / (M : ℝ) :=
      sum_denseBadTailTerm_le hA hN hM hthreshold L

/-- Infinite beta bad-event telescope with explicit constants.  Once the
pointwise beta moment estimate is supplied, no further analytic summation
interface remains. -/
theorem tsum_oneColumnLogBadProbability_le
    {A c0 : ℝ} (hA : 0 ≤ A) {N M : ℕ}
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hthreshold : 4 * A * (N : ℝ) ^ 2 ≤ (M : ℝ))
    (hbeta : OneColumnBetaTailBoundAt A c0 N M) :
    (∑' j : ℕ, oneColumnLogBadProbability (M + j) N c0) ≤
      2 * A ^ 2 * (N : ℝ) ^ 2 / (M : ℝ) := by
  apply Real.tsum_le_of_sum_range_le
  · exact fun j ↦ oneColumnLogBadProbability_nonneg (M + j) N c0
  · exact fun L ↦
      sum_oneColumnLogBadProbability_le hA hN hM hthreshold hbeta L

/-- Fully concrete infinite beta bad-event telescope.  Under
`M >= 24 N^2`, no beta-tail hypothesis remains, and the explicit result is
`72 N^2 / M`. -/
theorem tsum_oneColumnLogBadProbability_le_concrete
    {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    (hthreshold : 24 * (N : ℝ) ^ 2 ≤ (M : ℝ)) :
    (∑' j : ℕ, oneColumnLogBadProbability (M + j) N 1) ≤
      72 * (N : ℝ) ^ 2 / (M : ℝ) := by
  have hNreal : (N : ℝ) ≤ (M : ℝ) := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [sq_nonneg ((N : ℝ) - 1)]
  have hNM : N ≤ M := by exact_mod_cast hNreal
  have h := tsum_oneColumnLogBadProbability_le
    (A := (6 : ℝ)) (c0 := (1 : ℝ)) (by norm_num) hN hM
    (by norm_num at hthreshold ⊢; exact hthreshold)
    (oneColumnBetaTailBoundAt_six hN hNM)
  norm_num at h ⊢
  exact h

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
