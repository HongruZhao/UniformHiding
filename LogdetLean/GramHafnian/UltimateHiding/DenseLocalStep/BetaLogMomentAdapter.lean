import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.OneStepBridge
import LogdetLean.GramHafnian.UltimateHiding.Dense.BetaLogMomentsInternal
import Mathlib.Tactic

/-!
# Concrete beta-log moments at the squared hiding scale

This file turns the internally verified beta Mellin and polygamma identities
into the four concrete moment bounds consumed by `OneStepBridge`.
-/

open MeasureTheory Finset

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open _root_.LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Quadratic remainder for `log (1+x)` on the nonnegative half line.  This
elementary copy keeps the hiding package independent of the anticoncentration
coefficient module, where the same inequality was historically located. -/
theorem abs_log_one_add_sub_self_le_half_sq_local
    {x : ℝ} (hx : 0 ≤ x) :
    |Real.log (1 + x) - x| ≤ x ^ 2 / 2 := by
  have hpos : 0 < 1 + x := by linarith
  have hupp : Real.log (1 + x) ≤ x := by
    simpa using Real.log_le_sub_one_of_pos hpos
  have hlow := Real.le_log_one_add_of_nonneg hx
  have hden : 0 < x + 2 := by linarith
  have hgap : x - 2 * x / (x + 2) = x ^ 2 / (x + 2) := by
    field_simp [hden.ne']
    ring
  have hgapLe : x ^ 2 / (x + 2) ≤ x ^ 2 / 2 := by
    exact div_le_div_of_nonneg_left (sq_nonneg x) (by norm_num) (by linarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hupp)]
  rw [neg_sub]
  linarith

/-- On the integer ambient range, replacing `m^2` by `m(m+1)` costs at most
a factor two. -/
theorem one_div_sq_le_two_div_mul_succ
    {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / (m : ℝ) ^ 2 ≤
      2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmsR : 0 < (((m + 1 : ℕ) : ℝ)) := by positivity
  apply (div_le_div_iff₀ (sq_pos_of_pos hmR) (mul_pos hmR hmsR)).2
  push_cast
  nlinarith

/-- The deterministic scalar logarithm is nonnegative. -/
theorem oneColumnScalarLog_nonneg {m : ℕ} (hm : 1 ≤ m) :
    0 ≤ oneColumnScalarLog m := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have harg : (1 : ℝ) ≤ 1 + 1 / (m : ℝ) := by
    nlinarith [one_div_pos.mpr hmR]
  unfold oneColumnScalarLog
  exact mul_nonneg (by norm_num) (Real.log_nonneg harg)

/-- The deterministic scalar logarithm is at most `1/(2m)`. -/
theorem oneColumnScalarLog_le_half_inv {m : ℕ} (hm : 1 ≤ m) :
    oneColumnScalarLog m ≤ 1 / (2 * (m : ℝ)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  unfold oneColumnScalarLog
  have hpos : 0 < 1 + 1 / (m : ℝ) := by positivity
  have hlog : Real.log (1 + 1 / (m : ℝ)) ≤ 1 / (m : ℝ) := by
    simpa using Real.log_le_sub_one_of_pos hpos
  calc
    (1 / 2 : ℝ) * Real.log (1 + 1 / (m : ℝ)) ≤
        (1 / 2 : ℝ) * (1 / (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by norm_num)
    _ = 1 / (2 * (m : ℝ)) := by field_simp [hmR.ne']

/-- A reciprocal in the harmonic window differs from `1/m` by at most
`2N/m²` when `2N <= m`. -/
theorem oneColumn_reciprocal_window_sub_le
    {m N j : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m)
    (hj : j ∈ Finset.range N) :
    (1 : ℝ) / ((m + 1 - N + j : ℕ) : ℝ) - 1 / (m : ℝ) ≤
      2 * (N : ℝ) / (m : ℝ) ^ 2 := by
  have hjN : j < N := Finset.mem_range.mp hj
  let d : ℕ := m + 1 - N + j
  have hmNat : 1 ≤ m := by omega
  have hdNat : 1 ≤ d := by
    dsimp only [d]
    omega
  have hdmNat : d ≤ m := by
    dsimp only [d]
    omega
  have hgapNat : m - d ≤ N := by omega
  have hm : 0 < (m : ℝ) := by exact_mod_cast hmNat
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hdm : (d : ℝ) ≤ (m : ℝ) := by exact_mod_cast hdmNat
  have hgap : (m : ℝ) - (d : ℝ) ≤ (N : ℝ) := by
    rw [← Nat.cast_sub hdmNat]
    exact_mod_cast hgapNat
  have hm2d : (m : ℝ) ≤ 2 * (d : ℝ) := by
    simpa only [d] using oneColumn_harmonic_denominator_half hN h2Nm hj
  have hcore : ((m : ℝ) - (d : ℝ)) * (m : ℝ) ≤
      2 * (N : ℝ) * (d : ℝ) := by
    calc
      ((m : ℝ) - (d : ℝ)) * (m : ℝ) ≤
          (N : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hgap hm.le
      _ ≤ (N : ℝ) * (2 * (d : ℝ)) :=
        mul_le_mul_of_nonneg_left hm2d (Nat.cast_nonneg N)
      _ = 2 * (N : ℝ) * (d : ℝ) := by ring
  have hcross := mul_le_mul_of_nonneg_right hcore hm.le
  change (1 : ℝ) / (d : ℝ) - 1 / (m : ℝ) ≤
    2 * (N : ℝ) / (m : ℝ) ^ 2
  rw [show (1 : ℝ) / (d : ℝ) - 1 / (m : ℝ) =
      ((m : ℝ) - (d : ℝ)) / ((m : ℝ) * (d : ℝ)) by
        field_simp [hm.ne', hd.ne']]
  apply (div_le_div_iff₀ (mul_pos hm hd) (sq_pos_of_pos hm)).2
  nlinarith

/-- The harmonic average differs from `1/m` by at most `2N/m²`. -/
theorem oneColumnLogHarmonic_average_sub_le
    {m N : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) :
    oneColumnLogHarmonic m N 1 / (N : ℝ) - 1 / (m : ℝ) ≤
      2 * (N : ℝ) / (m : ℝ) ^ 2 := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsum : oneColumnLogHarmonic m N 1 -
      (N : ℝ) * (1 / (m : ℝ)) ≤
        (N : ℝ) * (2 * (N : ℝ) / (m : ℝ) ^ 2) := by
    unfold oneColumnLogHarmonic
    calc
      (∑ j ∈ Finset.range N,
          (1 : ℝ) / (((m + 1 - N + j : ℕ) : ℝ) ^ 1)) -
          (N : ℝ) * (1 / (m : ℝ)) =
        ∑ j ∈ Finset.range N,
          ((1 : ℝ) / ((m + 1 - N + j : ℕ) : ℝ) -
            1 / (m : ℝ)) := by
              simp only [pow_one, Finset.sum_sub_distrib]
              simp
      _ ≤ ∑ _j ∈ Finset.range N,
          2 * (N : ℝ) / (m : ℝ) ^ 2 := by
            exact Finset.sum_le_sum fun j hj ↦
              oneColumn_reciprocal_window_sub_le hN h2Nm hj
      _ = (N : ℝ) * (2 * (N : ℝ) / (m : ℝ) ^ 2) := by simp
  calc
    oneColumnLogHarmonic m N 1 / (N : ℝ) - 1 / (m : ℝ) =
        (oneColumnLogHarmonic m N 1 -
          (N : ℝ) * (1 / (m : ℝ))) / (N : ℝ) := by
            field_simp [hNR.ne']
    _ ≤ ((N : ℝ) * (2 * (N : ℝ) / (m : ℝ) ^ 2)) /
        (N : ℝ) := div_le_div_of_nonneg_right hsum hNR.le
    _ = 2 * (N : ℝ) / (m : ℝ) ^ 2 := by
      field_simp [hNR.ne']

/-- The harmonic average is at least `1/m`. -/
theorem oneColumnLogHarmonic_average_sub_nonneg
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    0 ≤ oneColumnLogHarmonic m N 1 / (N : ℝ) - 1 / (m : ℝ) := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmNat : 1 ≤ m := hN.trans hNm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmNat
  have hterm : ∀ j ∈ Finset.range N,
      1 / (m : ℝ) ≤
        (1 : ℝ) / ((m + 1 - N + j : ℕ) : ℝ) := by
    intro j hj
    have hjN : j < N := Finset.mem_range.mp hj
    have hdNat : 1 ≤ m + 1 - N + j := by omega
    have hdmNat : m + 1 - N + j ≤ m := by omega
    have hdR : 0 < ((m + 1 - N + j : ℕ) : ℝ) := by
      exact_mod_cast hdNat
    exact one_div_le_one_div_of_le hdR (by exact_mod_cast hdmNat)
  have hsum : (N : ℝ) * (1 / (m : ℝ)) ≤
      oneColumnLogHarmonic m N 1 := by
    unfold oneColumnLogHarmonic
    calc
      (N : ℝ) * (1 / (m : ℝ)) =
          ∑ _j ∈ Finset.range N, 1 / (m : ℝ) := by simp
      _ ≤ ∑ j ∈ Finset.range N,
          (1 : ℝ) / (((m + 1 - N + j : ℕ) : ℝ) ^ 1) := by
            simpa only [pow_one] using Finset.sum_le_sum hterm
  have hdiv := div_le_div_of_nonneg_right hsum hNR.le
  field_simp [hNR.ne'] at hdiv ⊢
  nlinarith

/-- Exact signed mean of the centered scalar logarithm. -/
theorem integral_oneColumnCenteredScalarLog_eq
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    (∫ q, oneColumnCenteredScalarLog m N q ∂(oneColumnBetaLaw m N)) =
      oneColumnScalarLog m - oneColumnLogHarmonic m N 1 / (2 * (N : ℝ)) := by
  letI : IsProbabilityMeasure (oneColumnBetaLaw m N) :=
    oneColumnBetaLaw_isProbability hN hNm
  rcases beta_log_moments_internal hN hNm with
    ⟨hb, _hbTwo, _hbThree, hbMean, _hbSecond, _hbThird⟩
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  unfold oneColumnCenteredScalarLog
  rw [integral_add (integrable_const _) (hb.div_const _), integral_const,
    integral_div, hbMean]
  simp
  field_simp [hN0]
  ring

/-- Concrete signed-mean estimate at the reciprocal-product scale.  This is
where the cancellation between the ambient scalar normalization and the mean
rank-one logarithm is retained. -/
theorem abs_integral_oneColumnCenteredScalarLog_le_concrete
    {m N : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) :
    |∫ q, oneColumnCenteredScalarLog m N q
        ∂(oneColumnBetaLaw m N)| ≤
      4 * (N : ℝ) / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
  have hNm : N ≤ m := by omega
  have hmNat : 1 ≤ m := hN.trans hNm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmNat
  have hNRone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : 0 ≤ (1 : ℝ) / (m : ℝ) := (one_div_nonneg.mpr hmR.le)
  have hlogrem :
      |Real.log (1 + 1 / (m : ℝ)) - 1 / (m : ℝ)| ≤
        ((1 : ℝ) / (m : ℝ)) ^ 2 / 2 :=
    abs_log_one_add_sub_self_le_half_sq_local hx
  have havg0 := oneColumnLogHarmonic_average_sub_nonneg hN hNm
  have havgLe := oneColumnLogHarmonic_average_sub_le hN h2Nm
  have habsAvg :
      |(1 : ℝ) / (m : ℝ) -
          oneColumnLogHarmonic m N 1 / (N : ℝ)| ≤
        2 * (N : ℝ) / (m : ℝ) ^ 2 := by
    rw [abs_of_nonpos]
    · linarith
    · linarith
  have habsLogAvg :
      |Real.log (1 + 1 / (m : ℝ)) -
          oneColumnLogHarmonic m N 1 / (N : ℝ)| ≤
        ((1 : ℝ) / (m : ℝ)) ^ 2 / 2 +
          2 * (N : ℝ) / (m : ℝ) ^ 2 := by
    calc
      |Real.log (1 + 1 / (m : ℝ)) -
          oneColumnLogHarmonic m N 1 / (N : ℝ)| =
          |(Real.log (1 + 1 / (m : ℝ)) - 1 / (m : ℝ)) +
            (1 / (m : ℝ) -
              oneColumnLogHarmonic m N 1 / (N : ℝ))| := by ring_nf
      _ ≤ |Real.log (1 + 1 / (m : ℝ)) - 1 / (m : ℝ)| +
          |1 / (m : ℝ) - oneColumnLogHarmonic m N 1 / (N : ℝ)| :=
        abs_add_le _ _
      _ ≤ ((1 : ℝ) / (m : ℝ)) ^ 2 / 2 +
          2 * (N : ℝ) / (m : ℝ) ^ 2 := add_le_add hlogrem habsAvg
  have hmeanEq :
      (∫ q, oneColumnCenteredScalarLog m N q ∂(oneColumnBetaLaw m N)) =
        (1 / 2 : ℝ) *
          (Real.log (1 + 1 / (m : ℝ)) -
            oneColumnLogHarmonic m N 1 / (N : ℝ)) := by
    rw [integral_oneColumnCenteredScalarLog_eq hN hNm]
    unfold oneColumnScalarLog
    ring
  have hcoarse :
      |∫ q, oneColumnCenteredScalarLog m N q
          ∂(oneColumnBetaLaw m N)| ≤
        2 * (N : ℝ) / (m : ℝ) ^ 2 := by
    rw [hmeanEq, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc
      (1 / 2 : ℝ) *
          |Real.log (1 + 1 / (m : ℝ)) -
            oneColumnLogHarmonic m N 1 / (N : ℝ)| ≤
          (1 / 2 : ℝ) * (((1 : ℝ) / (m : ℝ)) ^ 2 / 2 +
            2 * (N : ℝ) / (m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left habsLogAvg (by norm_num)
      _ ≤ 2 * (N : ℝ) / (m : ℝ) ^ 2 := by
        field_simp [hmR.ne']
        nlinarith
  calc
    |∫ q, oneColumnCenteredScalarLog m N q
        ∂(oneColumnBetaLaw m N)| ≤
        2 * (N : ℝ) / (m : ℝ) ^ 2 := hcoarse
    _ ≤ 4 * (N : ℝ) / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left
        (one_div_sq_le_two_div_mul_succ hmNat)
        (show 0 ≤ 2 * (N : ℝ) by positivity)
      calc
        2 * (N : ℝ) / (m : ℝ) ^ 2 =
            (2 * (N : ℝ)) * ((1 : ℝ) / (m : ℝ) ^ 2) := by ring
        _ ≤ (2 * (N : ℝ)) *
            (2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) := hmul
        _ = 4 * (N : ℝ) /
            ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by ring

/-- Integrability of the centered scalar logarithm. -/
theorem integrable_oneColumnCenteredScalarLog
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Integrable (oneColumnCenteredScalarLog m N) (oneColumnBetaLaw m N) := by
  letI : IsProbabilityMeasure (oneColumnBetaLaw m N) :=
    oneColumnBetaLaw_isProbability hN hNm
  rcases beta_log_moments_internal hN hNm with
    ⟨hb, _hbTwo, _hbThree, _hbMean, _hbSecond, _hbThird⟩
  unfold oneColumnCenteredScalarLog
  exact (integrable_const _).add (hb.div_const _)

/-- Square integrability needed by the scalar Taylor theorem. -/
theorem integrable_sq_oneColumnCenteredScalarLog
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Integrable (fun q ↦ oneColumnCenteredScalarLog m N q ^ 2)
      (oneColumnBetaLaw m N) := by
  letI : IsProbabilityMeasure (oneColumnBetaLaw m N) :=
    oneColumnBetaLaw_isProbability hN hNm
  rcases beta_log_moments_internal hN hNm with
    ⟨hb, hbTwo, _hbThree, _hbMean, _hbSecond, _hbThird⟩
  let a : ℝ := oneColumnScalarLog m
  let n : ℝ := N
  have hN0 : n ≠ 0 := by dsimp [n]; positivity
  have hcross : Integrable (fun q ↦ (2 * a / n) * oneColumnRankOneLog q)
      (oneColumnBetaLaw m N) := hb.const_mul _
  have hquad : Integrable (fun q ↦ (1 / n ^ 2) * oneColumnRankOneLog q ^ 2)
      (oneColumnBetaLaw m N) := hbTwo.const_mul _
  have hsum : Integrable
      (fun q ↦ a ^ 2 + (2 * a / n) * oneColumnRankOneLog q +
        (1 / n ^ 2) * oneColumnRankOneLog q ^ 2)
      (oneColumnBetaLaw m N) :=
    ((integrable_const _).add hcross).add hquad
  apply hsum.congr
  filter_upwards [] with q
  dsimp [oneColumnCenteredScalarLog, a, n]
  field_simp [hN0]
  ring

/-- The exact beta second moment implies the elementary dense-window bound
`E b^2 <= 2N^2/m^2`. -/
theorem integral_oneColumnRankOneLog_sq_le_coarse
    {m N : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) :
    (∫ q, oneColumnRankOneLog q ^ 2 ∂(oneColumnBetaLaw m N)) ≤
      2 * (N : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
  have hNm : N ≤ m := by omega
  have hmNat : 1 ≤ m := hN.trans hNm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmNat
  have hNRone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rcases beta_log_moments_internal hN hNm with
    ⟨_hb, _hbTwo, _hbThree, _hbMean, hbSecond, _hbThird⟩
  let H1 := oneColumnLogHarmonic m N 1
  let H2 := oneColumnLogHarmonic m N 2
  have hH1 : H1 ≤ 2 * (N : ℝ) / (m : ℝ) := by
    simpa only [H1] using oneColumnLogHarmonic_one_le hN h2Nm
  have hH2 : H2 ≤ 4 * (N : ℝ) / (m : ℝ) ^ 2 := by
    simpa only [H2] using oneColumnLogHarmonic_two_le hN h2Nm
  have hH10 : 0 ≤ H1 := by
    simpa only [H1] using oneColumnLogHarmonic_nonneg m N 1
  have hH1sq : H1 ^ 2 ≤ (2 * (N : ℝ) / (m : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hH10 hH1 2
  rw [hbSecond]
  change (H1 ^ 2 + H2) / 4 ≤ _
  calc
    (H1 ^ 2 + H2) / 4 ≤
        ((2 * (N : ℝ) / (m : ℝ)) ^ 2 +
          4 * (N : ℝ) / (m : ℝ) ^ 2) / 4 :=
      div_le_div_of_nonneg_right (add_le_add hH1sq hH2) (by norm_num)
    _ ≤ 2 * (N : ℝ) ^ 2 / (m : ℝ) ^ 2 := by
      field_simp [hmR.ne']
      nlinarith

/-- Second rank-one logarithmic moment at the reciprocal-product scale. -/
theorem integral_oneColumnRankOneLog_sq_le_concrete
    {m N : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) :
    (∫ q, oneColumnRankOneLog q ^ 2 ∂(oneColumnBetaLaw m N)) ≤
      4 * (N : ℝ) ^ 2 /
        ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
  have hNm : N ≤ m := by omega
  have hmNat : 1 ≤ m := hN.trans hNm
  calc
    (∫ q, oneColumnRankOneLog q ^ 2 ∂(oneColumnBetaLaw m N)) ≤
        2 * (N : ℝ) ^ 2 / (m : ℝ) ^ 2 :=
      integral_oneColumnRankOneLog_sq_le_coarse hN h2Nm
    _ = (2 * (N : ℝ) ^ 2) * ((1 : ℝ) / (m : ℝ) ^ 2) := by ring
    _ ≤ (2 * (N : ℝ) ^ 2) *
        (2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (one_div_sq_le_two_div_mul_succ hmNat) (by positivity)
    _ = 4 * (N : ℝ) ^ 2 /
        ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by ring

/-- The exact beta third absolute moment implies
`E |b|^3 <= 6N^3/m^3`. -/
theorem integral_abs_oneColumnRankOneLog_cube_le_coarse
    {m N : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) :
    (∫ q, |oneColumnRankOneLog q| ^ 3 ∂(oneColumnBetaLaw m N)) ≤
      6 * (N : ℝ) ^ 3 / (m : ℝ) ^ 3 := by
  have hNm : N ≤ m := by omega
  have hmNat : 1 ≤ m := hN.trans hNm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmNat
  have hNRone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rcases beta_log_moments_internal hN hNm with
    ⟨_hb, _hbTwo, _hbThree, _hbMean, _hbSecond, hbThird⟩
  let H1 := oneColumnLogHarmonic m N 1
  let H2 := oneColumnLogHarmonic m N 2
  let H3 := oneColumnLogHarmonic m N 3
  have hH1 : H1 ≤ 2 * (N : ℝ) / (m : ℝ) := by
    simpa only [H1] using oneColumnLogHarmonic_one_le hN h2Nm
  have hH2 : H2 ≤ 4 * (N : ℝ) / (m : ℝ) ^ 2 := by
    simpa only [H2] using oneColumnLogHarmonic_two_le hN h2Nm
  have hH3 : H3 ≤ 8 * (N : ℝ) / (m : ℝ) ^ 3 := by
    simpa only [H3] using oneColumnLogHarmonic_three_le hN h2Nm
  have hH10 : 0 ≤ H1 := by
    simpa only [H1] using oneColumnLogHarmonic_nonneg m N 1
  have hH20 : 0 ≤ H2 := by
    simpa only [H2] using oneColumnLogHarmonic_nonneg m N 2
  have hH1cube : H1 ^ 3 ≤ (2 * (N : ℝ) / (m : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hH10 hH1 3
  have hH1H2 : H1 * H2 ≤
      (2 * (N : ℝ) / (m : ℝ)) *
        (4 * (N : ℝ) / (m : ℝ) ^ 2) :=
    mul_le_mul hH1 hH2 hH20 (by positivity)
  rw [hbThird]
  change (H1 ^ 3 + 3 * H1 * H2 + 2 * H3) / 8 ≤ _
  calc
    (H1 ^ 3 + 3 * H1 * H2 + 2 * H3) / 8 ≤
        ((2 * (N : ℝ) / (m : ℝ)) ^ 3 +
          3 * ((2 * (N : ℝ) / (m : ℝ)) *
            (4 * (N : ℝ) / (m : ℝ) ^ 2)) +
          2 * (8 * (N : ℝ) / (m : ℝ) ^ 3)) / 8 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      have hprod3 := mul_le_mul_of_nonneg_left hH1H2 (by norm_num : (0 : ℝ) ≤ 3)
      have hthird2 := mul_le_mul_of_nonneg_left hH3 (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith
    _ ≤ 6 * (N : ℝ) ^ 3 / (m : ℝ) ^ 3 := by
      field_simp [hmR.ne']
      nlinarith

/-- Third rank-one logarithmic moment at the reciprocal-product scale.  The
extra hypothesis `N^2 <= m` is exactly the dense threshold used to trade the
raw `N^3/m^3` moment for `N/[m(m+1)]`. -/
theorem integral_abs_oneColumnRankOneLog_cube_le_concrete
    {m N : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m)
    (hN2m : N ^ 2 ≤ m) :
    (∫ q, |oneColumnRankOneLog q| ^ 3 ∂(oneColumnBetaLaw m N)) ≤
      12 * (N : ℝ) /
        ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
  have hNm : N ≤ m := by omega
  have hmNat : 1 ≤ m := hN.trans hNm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmNat
  have hN2mR : (N : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast hN2m
  have hcube : (N : ℝ) ^ 3 ≤ (N : ℝ) * (m : ℝ) := by
    calc
      (N : ℝ) ^ 3 = (N : ℝ) * (N : ℝ) ^ 2 := by ring
      _ ≤ (N : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hN2mR (Nat.cast_nonneg N)
  calc
    (∫ q, |oneColumnRankOneLog q| ^ 3 ∂(oneColumnBetaLaw m N)) ≤
        6 * (N : ℝ) ^ 3 / (m : ℝ) ^ 3 :=
      integral_abs_oneColumnRankOneLog_cube_le_coarse hN h2Nm
    _ ≤ 6 * ((N : ℝ) * (m : ℝ)) / (m : ℝ) ^ 3 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcube (by norm_num)) (by positivity)
    _ = 6 * (N : ℝ) / (m : ℝ) ^ 2 := by field_simp [hmR.ne']
    _ = (6 * (N : ℝ)) * ((1 : ℝ) / (m : ℝ) ^ 2) := by ring
    _ ≤ (6 * (N : ℝ)) *
        (2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (one_div_sq_le_two_div_mul_succ hmNat) (by positivity)
    _ = 12 * (N : ℝ) /
        ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by ring

/-- Concrete centered-scalar second moment.  The displayed constant `5` is a
deliberately simple envelope; the pointwise square estimate obtains
`9/(2m^2)` before
converting to the reciprocal-product denominator. -/
theorem integral_oneColumnCenteredScalarLog_sq_le_concrete
    {m N : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) :
    (∫ q, oneColumnCenteredScalarLog m N q ^ 2
        ∂(oneColumnBetaLaw m N)) ≤
      2 * 5 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
  have hNm : N ≤ m := by omega
  have hmNat : 1 ≤ m := hN.trans hNm
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmNat
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  letI : IsProbabilityMeasure (oneColumnBetaLaw m N) :=
    oneColumnBetaLaw_isProbability hN hNm
  rcases beta_log_moments_internal hN hNm with
    ⟨_hb, hbTwoInt, _hbThree, _hbMean, _hbSecond, _hbThird⟩
  let a : ℝ := oneColumnScalarLog m
  let n : ℝ := N
  have hN0 : n ≠ 0 := by dsimp [n]; positivity
  have ha0 : 0 ≤ a := by
    simpa only [a] using oneColumnScalarLog_nonneg hmNat
  have ha : a ≤ 1 / (2 * (m : ℝ)) := by
    simpa only [a] using oneColumnScalarLog_le_half_inv hmNat
  have haSq : a ^ 2 ≤ (1 / (2 * (m : ℝ))) ^ 2 :=
    pow_le_pow_left₀ ha0 ha 2
  have hcInt := integrable_sq_oneColumnCenteredScalarLog hN hNm
  have hmajorInt : Integrable
      (fun q ↦ 2 * a ^ 2 +
        (2 / n ^ 2) * oneColumnRankOneLog q ^ 2)
      (oneColumnBetaLaw m N) :=
    (integrable_const _).add (hbTwoInt.const_mul _)
  have hpoint : ∀ q : ℝ,
      oneColumnCenteredScalarLog m N q ^ 2 ≤
        2 * a ^ 2 + (2 / n ^ 2) * oneColumnRankOneLog q ^ 2 := by
    intro q
    dsimp [oneColumnCenteredScalarLog, a, n]
    have hsquare := sq_nonneg
      (oneColumnScalarLog m - oneColumnRankOneLog q / (N : ℝ))
    field_simp [hN0] at hsquare ⊢
    nlinarith
  have hbTwo := integral_oneColumnRankOneLog_sq_le_coarse hN h2Nm
  calc
    (∫ q, oneColumnCenteredScalarLog m N q ^ 2
        ∂(oneColumnBetaLaw m N)) ≤
        ∫ q, (2 * a ^ 2 +
          (2 / n ^ 2) * oneColumnRankOneLog q ^ 2)
          ∂(oneColumnBetaLaw m N) :=
      integral_mono hcInt hmajorInt hpoint
    _ = 2 * a ^ 2 + (2 / n ^ 2) *
        (∫ q, oneColumnRankOneLog q ^ 2
          ∂(oneColumnBetaLaw m N)) := by
      rw [integral_add (integrable_const _) (hbTwoInt.const_mul _),
        integral_const, integral_const_mul]
      simp
    _ ≤ 2 * (1 / (2 * (m : ℝ))) ^ 2 +
        (2 / n ^ 2) *
          (2 * (N : ℝ) ^ 2 / (m : ℝ) ^ 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left haSq (by norm_num))
        (mul_le_mul_of_nonneg_left hbTwo (by positivity))
    _ = 9 / (2 * (m : ℝ) ^ 2) := by
      dsimp only [n]
      field_simp [hmR.ne', hNR.ne']
      ring
    _ ≤ 5 * ((1 : ℝ) / (m : ℝ) ^ 2) := by
      field_simp [hmR.ne']
      norm_num
    _ ≤ 5 * (2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (one_div_sq_le_two_div_mul_succ hmNat) (by norm_num)
    _ = 2 * 5 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by ring

/-- The concrete beta-log package consumed by the one-step Taylor bridge.

The constants are, in structure-field order,
`Cmean = 4`, `CscalarTwo = 5`, `CbTwo = 4`, and `CbThree = 12`.
All beta-log identities used here come from the internal beta Mellin
calculation. -/
theorem oneColumnLogMomentBoundsAt_concrete
    {m N : ℕ} (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m)
    (hN2m : N ^ 2 ≤ m) :
    OneColumnLogMomentBoundsAt 4 5 4 12 m N := by
  have hNm : N ≤ m := by omega
  rcases beta_log_moments_internal hN hNm with
    ⟨_hb, hbTwo, hbThree, _hbMean, _hbSecond, _hbThird⟩
  refine
    { Cmean_nonneg := by norm_num
      CscalarTwo_nonneg := by norm_num
      CbTwo_nonneg := by norm_num
      CbThree_nonneg := by norm_num
      centeredScalar_integrable :=
        integrable_oneColumnCenteredScalarLog hN hNm
      centeredScalar_sq_integrable :=
        integrable_sq_oneColumnCenteredScalarLog hN hNm
      rankOne_sq_integrable := hbTwo
      rankOne_cube_integrable := hbThree
      centeredScalar_mean_le :=
        abs_integral_oneColumnCenteredScalarLog_le_concrete hN h2Nm
      centeredScalar_second_le :=
        integral_oneColumnCenteredScalarLog_sq_le_concrete hN h2Nm
      rankOne_second_le :=
        integral_oneColumnRankOneLog_sq_le_concrete hN h2Nm
      rankOne_third_le :=
        integral_abs_oneColumnRankOneLog_cube_le_concrete hN h2Nm hN2m }

/-- Paper-facing ambient-chain adapter.  In the one-column recursion the
physical hypotheses `N <= K <= m` and `2N <= K` automatically give the
beta-window condition `2N <= m`; the genuinely dense input left visible is
`N^2 <= m`. -/
theorem oneColumnLogMomentBoundsAt_concrete_of_K_chain
    {m K N : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m)
    (h2NK : 2 * N ≤ K) (hN2m : N ^ 2 ≤ m) :
    OneColumnLogMomentBoundsAt 4 5 4 12 m N := by
  have h2Nm : 2 * N ≤ m := h2NK.trans hKm
  exact oneColumnLogMomentBoundsAt_concrete hN h2Nm hN2m

/-- A convenient fixed-threshold specialization matching the conservative
dense cutoff used elsewhere in the capsule. -/
theorem oneColumnLogMomentBoundsAt_concrete_of_twentyFour_sq_le
    {m N : ℕ} (hN : 1 ≤ N) (hdense : 24 * N ^ 2 ≤ m) :
    OneColumnLogMomentBoundsAt 4 5 4 12 m N := by
  have hN2m : N ^ 2 ≤ m := by omega
  have h2Nm : 2 * N ≤ m := by
    have hNN : N ≤ N ^ 2 := by nlinarith
    omega
  exact oneColumnLogMomentBoundsAt_concrete hN h2Nm hN2m

/-- Direct specialization of the scalar `OneStepBridge` budget. -/
theorem oneColumnScalarTaylorBudget_le_concrete
    {CscoreOne CscoreTwo : ℝ} {m N : ℕ}
    (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) (hN2m : N ^ 2 ≤ m)
    (hscoreOne : 0 ≤ CscoreOne) (hscoreTwo : 0 ≤ CscoreTwo) :
    oneColumnScalarTaylorBudget CscoreOne CscoreTwo m N ≤
      (4 * CscoreOne + 5 * CscoreTwo) * (N : ℝ) ^ 2 /
        ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
  have h := oneColumnScalarTaylorBudget_le
    (oneColumnLogMomentBoundsAt_concrete hN h2Nm hN2m)
    hscoreOne hscoreTwo
  convert h using 1 <;> ring

/-- Direct specialization of the orbital `OneStepBridge` budget. -/
theorem oneColumnOrbitalTaylorBudget_le_concrete
    {CorbitalTwo CorbitalThree : ℝ} {m N : ℕ}
    (hN : 1 ≤ N) (h2Nm : 2 * N ≤ m) (hN2m : N ^ 2 ≤ m)
    (horbitalTwo : 0 ≤ CorbitalTwo)
    (horbitalThree : 0 ≤ CorbitalThree) :
    oneColumnOrbitalTaylorBudget CorbitalTwo CorbitalThree m N ≤
      (2 * CorbitalTwo + 2 * CorbitalThree) * (N : ℝ) ^ 2 /
        ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
  have h := oneColumnOrbitalTaylorBudget_le
    (oneColumnLogMomentBoundsAt_concrete hN h2Nm hN2m)
    horbitalTwo horbitalThree
  convert h using 1 <;> ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
