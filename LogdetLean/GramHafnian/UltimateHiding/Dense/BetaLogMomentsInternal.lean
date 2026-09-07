import LogdetLean.GramHafnian.UltimateHiding.Dense.BetaLogMomentExternal
import LogdetLean.NullCenterStandardization
import LogdetLean.GeneralRResidualMoments

/-!
# Internal logarithmic moments of the dense one-column beta variable

This module replaces the classical beta-calculus atom used by the first
version of the dense hiding argument.  The proof starts from the internally
verified Mellin transform of `betaMeasure`, identifies the first three
cumulants through the project's digamma and polygamma series, and evaluates
the integer shift by finite reciprocal-power sums.

The legacy-named helper module imported above owns only the notation
`oneColumnLogHarmonic` and its elementary bounds; it no longer declares an
external beta-moment axiom.
-/

open MeasureTheory ProbabilityTheory Finset

namespace LogdetLean.GramHafnian.UltimateHiding.Dense

noncomputable section

private theorem trigammaSeries_add_one_internal {x : ℝ} (hx : 0 < x) :
    LogdetLean.trigammaSeries (x + 1) =
      LogdetLean.trigammaSeries x - 1 / x ^ 2 := by
  unfold LogdetLean.trigammaSeries
  have hs := LogdetLean.summable_trigammaSeries_terms hx
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, add_zero]
  have hshift :
      (∑' b : ℕ, 1 / (x + ((b + 1 : ℕ) : ℝ)) ^ 2) =
        ∑' b : ℕ, 1 / ((x + 1) + (b : ℝ)) ^ 2 := by
    congr 1
    funext b
    push_cast
    ring_nf
  rw [hshift]
  ring

private theorem negPsiTwoSeries_add_one_internal {x : ℝ} (hx : 0 < x) :
    LogdetLean.negPsiTwoSeries (x + 1) =
      LogdetLean.negPsiTwoSeries x - 2 / x ^ 3 := by
  unfold LogdetLean.negPsiTwoSeries
  have hs := LogdetLean.summable_negPsiTwoSeries_terms hx
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero, add_zero]
  have hshift :
      (∑' b : ℕ, 1 / (x + ((b + 1 : ℕ) : ℝ)) ^ 3) =
        ∑' b : ℕ, 1 / ((x + 1) + (b : ℝ)) ^ 3 := by
    congr 1
    funext b
    push_cast
    ring_nf
  rw [hshift]
  ring

private theorem digammaSeries_add_nat_internal
    {x : ℝ} (hx : 0 < x) (N : ℕ) :
    LogdetLean.digammaSeries (x + N) =
      LogdetLean.digammaSeries x +
        ∑ j ∈ Finset.range N, 1 / (x + (j : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.cast_succ, show x + ((N : ℝ) + 1) = (x + N) + 1 by ring,
        LogdetLean.digammaSeries_add_one (by positivity), ih,
        Finset.sum_range_succ]
      ring

private theorem trigammaSeries_add_nat_internal
    {x : ℝ} (hx : 0 < x) (N : ℕ) :
    LogdetLean.trigammaSeries (x + N) =
      LogdetLean.trigammaSeries x -
        ∑ j ∈ Finset.range N, 1 / (x + (j : ℝ)) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.cast_succ, show x + ((N : ℝ) + 1) = (x + N) + 1 by ring,
        trigammaSeries_add_one_internal (by positivity), ih,
        Finset.sum_range_succ]
      ring

private theorem negPsiTwoSeries_add_nat_internal
    {x : ℝ} (hx : 0 < x) (N : ℕ) :
    LogdetLean.negPsiTwoSeries (x + N) =
      LogdetLean.negPsiTwoSeries x -
        2 * ∑ j ∈ Finset.range N, 1 / (x + (j : ℝ)) ^ 3 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.cast_succ, show x + ((N : ℝ) + 1) = (x + N) + 1 by ring,
        negPsiTwoSeries_add_one_internal (by positivity), ih,
        Finset.sum_range_succ]
      ring

private theorem oneColumnBetaShapeLeft_add_right
    (m N : ℕ) :
    oneColumnBetaShapeLeft m N + oneColumnBetaShapeRight N = (m : ℝ) + 1 := by
  unfold oneColumnBetaShapeLeft oneColumnBetaShapeRight
  ring

private theorem oneColumnBetaShapeLeft_add_cast_eq_denominator
    {m N : ℕ} (hNm : N ≤ m) (j : ℕ) :
    oneColumnBetaShapeLeft m N + (j : ℝ) =
      ((m + 1 - N + j : ℕ) : ℝ) := by
  have hNm1 : N ≤ m + 1 := hNm.trans (Nat.le_succ m)
  unfold oneColumnBetaShapeLeft
  rw [Nat.cast_add, Nat.cast_sub hNm1]
  push_cast
  ring

private theorem oneColumnLogHarmonic_eq_shifted_sum
    {m N r : ℕ} (hNm : N ≤ m) :
    oneColumnLogHarmonic m N r =
      ∑ j ∈ Finset.range N,
        (1 : ℝ) / (oneColumnBetaShapeLeft m N + (j : ℝ)) ^ r := by
  unfold oneColumnLogHarmonic
  apply Finset.sum_congr rfl
  intro j _
  rw [oneColumnBetaShapeLeft_add_cast_eq_denominator hNm]

private theorem digamma_oneColumnShape_sub_eq_harmonic
    {m N : ℕ} (hNm : N ≤ m) :
    LogdetLean.digammaSeries (oneColumnBetaShapeLeft m N) -
        LogdetLean.digammaSeries
          (oneColumnBetaShapeLeft m N + oneColumnBetaShapeRight N) =
      -oneColumnLogHarmonic m N 1 := by
  have hleft : 0 < oneColumnBetaShapeLeft m N :=
    oneColumnBetaShapeLeft_pos hNm
  have hrec := digammaSeries_add_nat_internal hleft N
  have hsum : oneColumnLogHarmonic m N 1 =
      ∑ j ∈ Finset.range N,
        (1 : ℝ) / (oneColumnBetaShapeLeft m N + (j : ℝ)) := by
    simpa only [pow_one] using
      (oneColumnLogHarmonic_eq_shifted_sum (r := 1) hNm)
  rw [show (N : ℝ) = oneColumnBetaShapeRight N by
    rfl, ← hsum] at hrec
  linarith

private theorem trigamma_oneColumnShape_sub_eq_harmonic
    {m N : ℕ} (hNm : N ≤ m) :
    LogdetLean.trigammaSeries (oneColumnBetaShapeLeft m N) -
        LogdetLean.trigammaSeries
          (oneColumnBetaShapeLeft m N + oneColumnBetaShapeRight N) =
      oneColumnLogHarmonic m N 2 := by
  have hleft : 0 < oneColumnBetaShapeLeft m N :=
    oneColumnBetaShapeLeft_pos hNm
  have hrec := trigammaSeries_add_nat_internal hleft N
  have hsum := oneColumnLogHarmonic_eq_shifted_sum (r := 2) hNm
  rw [show (N : ℝ) = oneColumnBetaShapeRight N by
    rfl, ← hsum] at hrec
  linarith

private theorem negPsiTwo_oneColumnShape_sub_eq_harmonic
    {m N : ℕ} (hNm : N ≤ m) :
    LogdetLean.negPsiTwoSeries (oneColumnBetaShapeLeft m N) -
        LogdetLean.negPsiTwoSeries
          (oneColumnBetaShapeLeft m N + oneColumnBetaShapeRight N) =
      2 * oneColumnLogHarmonic m N 3 := by
  have hleft : 0 < oneColumnBetaShapeLeft m N :=
    oneColumnBetaShapeLeft_pos hNm
  have hrec := negPsiTwoSeries_add_nat_internal hleft N
  have hsum := oneColumnLogHarmonic_eq_shifted_sum (r := 3) hNm
  rw [show (N : ℝ) = oneColumnBetaShapeRight N by
    rfl, ← hsum] at hrec
  linarith

theorem integral_log_oneColumnBetaLaw_eq
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    (∫ q, Real.log q ∂(oneColumnBetaLaw m N)) =
      -oneColumnLogHarmonic m N 1 := by
  have hleft : 0 < oneColumnBetaShapeLeft m N :=
    oneColumnBetaShapeLeft_pos hNm
  have hright : 0 < oneColumnBetaShapeRight N :=
    oneColumnBetaShapeRight_pos hN
  unfold oneColumnBetaLaw
  rw [LogdetLean.integral_log_betaMeasure_eq_digammaSeries_sub hleft hright]
  exact digamma_oneColumnShape_sub_eq_harmonic hNm

theorem integral_centered_sq_log_oneColumnBetaLaw_eq
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    (∫ q, (Real.log q -
        ∫ y, Real.log y ∂(oneColumnBetaLaw m N)) ^ 2
      ∂(oneColumnBetaLaw m N)) = oneColumnLogHarmonic m N 2 := by
  have hleft : 0 < oneColumnBetaShapeLeft m N :=
    oneColumnBetaShapeLeft_pos hNm
  have hright : 0 < oneColumnBetaShapeRight N :=
    oneColumnBetaShapeRight_pos hN
  unfold oneColumnBetaLaw
  rw [LogdetLean.integral_centered_sq_log_betaMeasure_eq_trigammaSeries_sub
    hleft hright]
  exact trigamma_oneColumnShape_sub_eq_harmonic hNm

theorem integral_centered_cube_log_oneColumnBetaLaw_eq
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    (∫ q, (Real.log q -
        ∫ y, Real.log y ∂(oneColumnBetaLaw m N)) ^ 3
      ∂(oneColumnBetaLaw m N)) = -2 * oneColumnLogHarmonic m N 3 := by
  have hleft : 0 < oneColumnBetaShapeLeft m N :=
    oneColumnBetaShapeLeft_pos hNm
  have hright : 0 < oneColumnBetaShapeRight N :=
    oneColumnBetaShapeRight_pos hN
  unfold oneColumnBetaLaw
  rw [LogdetLean.integral_centered_cube_log_betaMeasure_eq_negPsiTwoSeries_sub
    hleft hright]
  rw [negPsiTwo_oneColumnShape_sub_eq_harmonic hNm]
  ring

theorem integrable_log_oneColumnBetaLaw
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Integrable Real.log (oneColumnBetaLaw m N) := by
  have hleft : 0 < oneColumnBetaShapeLeft m N :=
    oneColumnBetaShapeLeft_pos hNm
  have hright : 0 < oneColumnBetaShapeRight N :=
    oneColumnBetaShapeRight_pos hN
  unfold oneColumnBetaLaw
  simpa only [pow_one] using
    (LogdetLean.integrable_pow_log_betaMeasure hleft hright 1)

theorem integrable_sq_log_oneColumnBetaLaw
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Integrable (fun q ↦ Real.log q ^ 2) (oneColumnBetaLaw m N) := by
  have hleft : 0 < oneColumnBetaShapeLeft m N :=
    oneColumnBetaShapeLeft_pos hNm
  have hright : 0 < oneColumnBetaShapeRight N :=
    oneColumnBetaShapeRight_pos hN
  unfold oneColumnBetaLaw
  exact LogdetLean.integrable_pow_log_betaMeasure hleft hright 2

theorem integrable_cube_log_oneColumnBetaLaw
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Integrable (fun q ↦ Real.log q ^ 3) (oneColumnBetaLaw m N) := by
  have hleft : 0 < oneColumnBetaShapeLeft m N :=
    oneColumnBetaShapeLeft_pos hNm
  have hright : 0 < oneColumnBetaShapeRight N :=
    oneColumnBetaShapeRight_pos hN
  unfold oneColumnBetaLaw
  exact LogdetLean.integrable_pow_log_betaMeasure hleft hright 3

theorem integral_sq_log_oneColumnBetaLaw_eq
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    (∫ q, Real.log q ^ 2 ∂(oneColumnBetaLaw m N)) =
      oneColumnLogHarmonic m N 1 ^ 2 + oneColumnLogHarmonic m N 2 := by
  letI : IsProbabilityMeasure (oneColumnBetaLaw m N) :=
    oneColumnBetaLaw_isProbability hN hNm
  have hlog := integrable_log_oneColumnBetaLaw hN hNm
  have hlog2 := integrable_sq_log_oneColumnBetaLaw hN hNm
  have hmem : MemLp Real.log 2 (oneColumnBetaLaw m N) :=
    (memLp_two_iff_integrable_sq hlog.aestronglyMeasurable).2 hlog2
  have hvarCentered := ProbabilityTheory.variance_eq_integral hmem.aemeasurable
  have hvarRaw := ProbabilityTheory.variance_eq_sub hmem
  have hcenter := integral_centered_sq_log_oneColumnBetaLaw_eq hN hNm
  have hmean := integral_log_oneColumnBetaLaw_eq hN hNm
  rw [hcenter] at hvarCentered
  rw [hmean] at hvarRaw
  rw [hvarCentered] at hvarRaw
  simp only [Pi.pow_apply] at hvarRaw
  exact (by nlinarith [hvarRaw] :
    (∫ q, Real.log q ^ 2 ∂(oneColumnBetaLaw m N)) =
      oneColumnLogHarmonic m N 1 ^ 2 + oneColumnLogHarmonic m N 2)

theorem integral_cube_log_oneColumnBetaLaw_eq
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    (∫ q, Real.log q ^ 3 ∂(oneColumnBetaLaw m N)) =
      -(oneColumnLogHarmonic m N 1 ^ 3 +
        3 * oneColumnLogHarmonic m N 1 * oneColumnLogHarmonic m N 2 +
        2 * oneColumnLogHarmonic m N 3) := by
  have hleft : 0 < oneColumnBetaShapeLeft m N :=
    oneColumnBetaShapeLeft_pos hNm
  have hright : 0 < oneColumnBetaShapeRight N :=
    oneColumnBetaShapeRight_pos hN
  have hcumulant :
      (∫ q, (Real.log q -
          ∫ y, Real.log y ∂(oneColumnBetaLaw m N)) ^ 3
        ∂(oneColumnBetaLaw m N)) =
        (∫ q, Real.log q ^ 3 ∂(oneColumnBetaLaw m N)) -
          3 * (∫ q, Real.log q ^ 2 ∂(oneColumnBetaLaw m N)) *
            (∫ q, Real.log q ∂(oneColumnBetaLaw m N)) +
          2 * (∫ q, Real.log q ∂(oneColumnBetaLaw m N)) ^ 3 := by
    unfold oneColumnBetaLaw
    calc
      (∫ q, (Real.log q -
          ∫ y, Real.log y ∂(betaMeasure (oneColumnBetaShapeLeft m N)
            (oneColumnBetaShapeRight N))) ^ 3
        ∂(betaMeasure (oneColumnBetaShapeLeft m N)
          (oneColumnBetaShapeRight N))) =
          iteratedDeriv 3
            (LogdetLean.betaLogCGF (oneColumnBetaShapeLeft m N)
              (oneColumnBetaShapeRight N)) 0 :=
        LogdetLean.integral_centered_cube_log_betaMeasure_eq_third_deriv_betaLogCGF
          hleft hright
      _ = iteratedDeriv 3
          (ProbabilityTheory.cgf Real.log
            (betaMeasure (oneColumnBetaShapeLeft m N)
              (oneColumnBetaShapeRight N))) 0 := by
        symm
        exact LogdetLean.logBeta_cumulant_eq_iteratedDeriv_betaLogCGF
          hleft hright 3
      _ = _ := LogdetLean.third_cgf_log_betaMeasure_eq_raw_moments hleft hright
  rw [integral_centered_cube_log_oneColumnBetaLaw_eq hN hNm,
    integral_log_oneColumnBetaLaw_eq hN hNm,
    integral_sq_log_oneColumnBetaLaw_eq hN hNm] at hcumulant
  nlinarith

theorem integrable_oneColumnRankOneLog_internal
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Integrable oneColumnRankOneLog (oneColumnBetaLaw m N) := by
  have hlog := integrable_log_oneColumnBetaLaw hN hNm
  change Integrable (fun q ↦ (1 / 2 : ℝ) * Real.log q)
    (oneColumnBetaLaw m N)
  exact hlog.const_mul (1 / 2 : ℝ)

theorem integrable_sq_oneColumnRankOneLog_internal
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Integrable (fun q ↦ oneColumnRankOneLog q ^ 2)
      (oneColumnBetaLaw m N) := by
  have hlog2 := integrable_sq_log_oneColumnBetaLaw hN hNm
  have hscaled := hlog2.const_mul (1 / 4 : ℝ)
  apply hscaled.congr
  filter_upwards with q
  unfold oneColumnRankOneLog
  ring

theorem integrable_abs_cube_oneColumnRankOneLog_internal
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Integrable (fun q ↦ |oneColumnRankOneLog q| ^ 3)
      (oneColumnBetaLaw m N) := by
  have hlog3 := integrable_cube_log_oneColumnBetaLaw hN hNm
  have hnorm := hlog3.norm.const_mul (1 / 8 : ℝ)
  apply hnorm.congr
  filter_upwards with q
  unfold oneColumnRankOneLog
  rw [Real.norm_eq_abs, abs_pow, abs_mul]
  norm_num
  ring

theorem integral_oneColumnRankOneLog_eq_internal
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    (∫ q, oneColumnRankOneLog q ∂(oneColumnBetaLaw m N)) =
      -oneColumnLogHarmonic m N 1 / 2 := by
  unfold oneColumnRankOneLog
  rw [integral_const_mul, integral_log_oneColumnBetaLaw_eq hN hNm]
  ring

theorem integral_sq_oneColumnRankOneLog_eq_internal
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    (∫ q, oneColumnRankOneLog q ^ 2 ∂(oneColumnBetaLaw m N)) =
      (oneColumnLogHarmonic m N 1 ^ 2 +
        oneColumnLogHarmonic m N 2) / 4 := by
  calc
    (∫ q, oneColumnRankOneLog q ^ 2 ∂(oneColumnBetaLaw m N)) =
        ∫ q, (1 / 4 : ℝ) * Real.log q ^ 2
          ∂(oneColumnBetaLaw m N) := by
      apply integral_congr_ae
      filter_upwards with q
      unfold oneColumnRankOneLog
      ring
    _ = (1 / 4 : ℝ) *
        (∫ q, Real.log q ^ 2 ∂(oneColumnBetaLaw m N)) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [integral_sq_log_oneColumnBetaLaw_eq hN hNm]
      ring

theorem integral_cube_oneColumnRankOneLog_eq_internal
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    (∫ q, oneColumnRankOneLog q ^ 3 ∂(oneColumnBetaLaw m N)) =
      -(oneColumnLogHarmonic m N 1 ^ 3 +
        3 * oneColumnLogHarmonic m N 1 * oneColumnLogHarmonic m N 2 +
        2 * oneColumnLogHarmonic m N 3) / 8 := by
  calc
    (∫ q, oneColumnRankOneLog q ^ 3 ∂(oneColumnBetaLaw m N)) =
        ∫ q, (1 / 8 : ℝ) * Real.log q ^ 3
          ∂(oneColumnBetaLaw m N) := by
      apply integral_congr_ae
      filter_upwards with q
      unfold oneColumnRankOneLog
      ring
    _ = (1 / 8 : ℝ) *
        (∫ q, Real.log q ^ 3 ∂(oneColumnBetaLaw m N)) := by
      rw [integral_const_mul]
    _ = _ := by
      rw [integral_cube_log_oneColumnBetaLaw_eq hN hNm]
      ring

theorem integral_abs_cube_oneColumnRankOneLog_eq_internal
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    (∫ q, |oneColumnRankOneLog q| ^ 3 ∂(oneColumnBetaLaw m N)) =
      (oneColumnLogHarmonic m N 1 ^ 3 +
        3 * oneColumnLogHarmonic m N 1 * oneColumnLogHarmonic m N 2 +
        2 * oneColumnLogHarmonic m N 3) / 8 := by
  have hsupport : ∀ᵐ q ∂(oneColumnBetaLaw m N), q ∈ Set.Ioo (0 : ℝ) 1 :=
    (mem_ae_iff.mpr (oneColumnBetaLaw_compl_Ioo_eq_zero m N))
  have habs :
      (fun q ↦ |oneColumnRankOneLog q| ^ 3) =ᵐ[oneColumnBetaLaw m N]
        (fun q ↦ -(oneColumnRankOneLog q ^ 3)) := by
    filter_upwards [hsupport] with q hq
    have hlog : Real.log q < 0 := Real.log_neg hq.1 hq.2
    have hnonpos : oneColumnRankOneLog q ≤ 0 := by
      unfold oneColumnRankOneLog
      linarith
    rw [abs_of_nonpos hnonpos]
    ring
  calc
    (∫ q, |oneColumnRankOneLog q| ^ 3 ∂(oneColumnBetaLaw m N)) =
        ∫ q, -(oneColumnRankOneLog q ^ 3)
          ∂(oneColumnBetaLaw m N) := integral_congr_ae habs
    _ = -(∫ q, oneColumnRankOneLog q ^ 3
          ∂(oneColumnBetaLaw m N)) := by rw [integral_neg]
    _ = _ := by
      rw [integral_cube_oneColumnRankOneLog_eq_internal hN hNm]
      ring

/-- Fully internal replacement for `beta_log_moments_external`. -/
theorem beta_log_moments_internal
    {m N : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    Integrable oneColumnRankOneLog (oneColumnBetaLaw m N) ∧
    Integrable (fun q ↦ oneColumnRankOneLog q ^ 2) (oneColumnBetaLaw m N) ∧
    Integrable (fun q ↦ |oneColumnRankOneLog q| ^ 3) (oneColumnBetaLaw m N) ∧
    (∫ q, oneColumnRankOneLog q ∂(oneColumnBetaLaw m N)) =
      -(oneColumnLogHarmonic m N 1) / 2 ∧
    (∫ q, oneColumnRankOneLog q ^ 2 ∂(oneColumnBetaLaw m N)) =
      ((oneColumnLogHarmonic m N 1) ^ 2 +
        oneColumnLogHarmonic m N 2) / 4 ∧
    (∫ q, |oneColumnRankOneLog q| ^ 3 ∂(oneColumnBetaLaw m N)) =
      ((oneColumnLogHarmonic m N 1) ^ 3 +
        3 * oneColumnLogHarmonic m N 1 * oneColumnLogHarmonic m N 2 +
        2 * oneColumnLogHarmonic m N 3) / 8 := by
  exact ⟨integrable_oneColumnRankOneLog_internal hN hNm,
    integrable_sq_oneColumnRankOneLog_internal hN hNm,
    integrable_abs_cube_oneColumnRankOneLog_internal hN hNm,
    integral_oneColumnRankOneLog_eq_internal hN hNm,
    integral_sq_oneColumnRankOneLog_eq_internal hN hNm,
    integral_abs_cube_oneColumnRankOneLog_eq_internal hN hNm⟩

end

end LogdetLean.GramHafnian.UltimateHiding.Dense
