import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Sharp34LowOrderScoreBounds
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H12_RawFourthExactRecurrenceBound
import Mathlib.Tactic

/-!
# Exact-variance low-order score bounds

The degree-two H8/H10 recurrence already determines the raw second moment of
`Tr Y` and the raw mean of `Tr(Y^2)`.  Keeping those exact quotients before
rounding yields

* centered `Tr Y` squared `L²` norm at most `(60/11) N²`;
* centered `Tr Y` `L²` norm at most `(29/12) N`;
* central score constants `5` and `44`;
* averaged quadratic score constant `573`.

No new scientific assumption is introduced.
-/

open MeasureTheory ProbabilityTheory
open scoped ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxHeartbeats 3600000
set_option maxRecDepth 100000

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration
open U08

def exactVarianceCenteredTraceOneL2Constant : ℝ := 29 / 12

def exactVarianceCentralScoreOneConstant : ℝ := 5

def exactVarianceCentralScoreTwoConstant : ℝ := 44

def exactVarianceOrbitalScoreTwoConstant : ℝ := 573

/-! ## Exact scalar recurrence inequalities -/

/-- Exact centered first-trace variance numerator in the dense range. -/
theorem h12TraceOneCenteredVarianceNumerator_le_sixty_dense_exactVariance
    {n c : ℝ} (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    11 * (h12TraceOneRawMeanNumerator n c -
        n ^ 2 * (n + 1) ^ 2 * h8H10DegreeTwoDenominator c) ≤
      60 * n ^ 2 * h8H10DegreeTwoDenominator c := by
  let e : ℝ := n - 1
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnRep : n = 1 + e := by dsimp only [e]; ring
  have hcRep : c = 13 * (1 + e) + d := by dsimp only [e, d]; ring
  rw [hnRep, hcRep]
  unfold h12TraceOneRawMeanNumerator h8H10DegreeTwoDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

/-- Quotient form of the exact centered first-trace variance estimate. -/
theorem h12TraceOneCenteredVarianceQuotient_le_sixty_div_eleven_exactVariance
    {n c : ℝ} (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceOneRawMeanNumerator n c / h8H10DegreeTwoDenominator c -
        (n * (n + 1)) ^ 2 ≤
      (60 / 11 : ℝ) * n ^ 2 := by
  have hc : 13 ≤ c := by nlinarith
  have hdenPos : 0 < h8H10DegreeTwoDenominator c := by
    unfold h8H10DegreeTwoDenominator
    exact mul_pos (by linarith) (by linarith)
  rw [show h12TraceOneRawMeanNumerator n c /
          h8H10DegreeTwoDenominator c - (n * (n + 1)) ^ 2 =
        (h12TraceOneRawMeanNumerator n c -
          n ^ 2 * (n + 1) ^ 2 * h8H10DegreeTwoDenominator c) /
            h8H10DegreeTwoDenominator c by
      field_simp [ne_of_gt hdenPos]
      ]
  apply (div_le_iff₀ hdenPos).2
  have hclear :=
    h12TraceOneCenteredVarianceNumerator_le_sixty_dense_exactVariance hn hdense
  nlinarith

/-- The two exact positive raw means, after insertion into the second central
log score, have coefficient at most `240/11`. -/
theorem h12CentralLogScoreTwoMeanNumerator_le_240_div_11_exactVariance
    {n c : ℝ} (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    11 * 8 * (c * h8H10DegreeTwoDenominator c * n * (n + 1) +
        h12TraceTwoRawMeanNumerator n c) ≤
      240 * c * h8H10DegreeTwoDenominator c * n ^ 2 := by
  let e : ℝ := n - 1
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnRep : n = 1 + e := by dsimp only [e]; ring
  have hcRep : c = 13 * (1 + e) + d := by dsimp only [e, d]; ring
  rw [hnRep, hcRep]
  unfold h12TraceTwoRawMeanNumerator h8H10DegreeTwoDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

theorem h12CentralLogScoreTwoMeanQuotient_le_240_div_11_exactVariance
    {n c : ℝ} (hn : 1 ≤ n) (hdense : 13 * n ≤ c) :
    8 * (n * (n + 1) +
        (h12TraceTwoRawMeanNumerator n c /
          h8H10DegreeTwoDenominator c) / c) ≤
      (240 / 11 : ℝ) * n ^ 2 := by
  have hc : 0 < c := by nlinarith
  have hdenPos : 0 < h8H10DegreeTwoDenominator c := by
    unfold h8H10DegreeTwoDenominator
    exact mul_pos (by nlinarith) (by nlinarith)
  rw [show 8 * (n * (n + 1) +
          (h12TraceTwoRawMeanNumerator n c /
            h8H10DegreeTwoDenominator c) / c) =
        (8 * (c * h8H10DegreeTwoDenominator c * n * (n + 1) +
          h12TraceTwoRawMeanNumerator n c)) /
            (c * h8H10DegreeTwoDenominator c) by
      field_simp [ne_of_gt hc, ne_of_gt hdenPos]
      ]
  apply (div_le_iff₀ (mul_pos hc hdenPos)).2
  have hclear :=
    h12CentralLogScoreTwoMeanNumerator_le_240_div_11_exactVariance hn hdense
  nlinarith

/-! ## Exact source moments and the centered first-trace norm -/

private theorem betaPrimeTraceOneSource_square_integral_eq_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ source, betaPrimeTraceOneSource N K source ^ 2
      ∂realBetaPrimeGaussianSourceLaw N K) =
      h12TraceOneRawMeanNumerator (N : ℝ) (concreteCOEExponent N K) /
        h8H10DegreeTwoDenominator (concreteCOEExponent N K) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [betaPrimeTraceOneSource_square_integral_eq_denominator_internal N K hgap,
    h8DenominatorSecondRawMoment_eq_traceMoments_internal]
  simpa only [h12TraceOneRawMeanRecurrenceMoment] using
    h12TraceOneRawMeanRecurrenceMoment_eq_exact
      (h8H10ExactTraceRecurrenceSystem_internal hN hdense)
      (by exact_mod_cast hN)
      (thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense)

private theorem betaPrimeTraceTwoSource_integral_eq_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ source, betaPrimeTraceTwoSource N K source
      ∂realBetaPrimeGaussianSourceLaw N K) =
      h12TraceTwoRawMeanNumerator (N : ℝ) (concreteCOEExponent N K) /
        h8H10DegreeTwoDenominator (concreteCOEExponent N K) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [betaPrimeTraceTwoSource_integral_eq_denominator_internal N K hgap,
    h10DenominatorFirstRawMoment_eq_traceMoments_internal]
  simpa only [h12TraceTwoRawMeanRecurrenceMoment] using
    h12TraceTwoRawMeanRecurrenceMoment_eq_exact
      (h8H10ExactTraceRecurrenceSystem_internal hN hdense)
      (by exact_mod_cast hN)
      (thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense)

/-- The exact squared centered `L²` estimate, retained before taking a
rational square-root ceiling. -/
theorem betaPrimeYTraceOne_centered_lpNorm_two_sq_le_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun u ↦ betaPrimeYTraceOne N K u -
        ∫ z, betaPrimeYTraceOne N K z ∂betaPrimeTraceFourLaw N K)
          2 (betaPrimeTraceFourLaw N K) ^ 2 ≤
      (60 / 11 : ℝ) * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let sourceMu := realBetaPrimeGaussianSourceLaw N K
  let X := betaPrimeTraceOneSource N K
  let targetMu := betaPrimeTraceFourLaw N K
  let g : (Fin 4 → ℝ) → ℝ := fun u ↦
    betaPrimeYTraceOne N K u - ∫ z, betaPrimeYTraceOne N K z ∂targetMu
  letI : IsProbabilityMeasure sourceMu :=
    realBetaPrimeGaussianSourceLaw_isProbability N K
  have hX : MemLp X 2 sourceMu := by
    simpa only [X, sourceMu] using
      U08.betaPrimeTraceOneSource_memLp_two_internal hgap
  have hSecond : (∫ source, X source ^ 2 ∂sourceMu) =
      h12TraceOneRawMeanNumerator (N : ℝ) (concreteCOEExponent N K) /
        h8H10DegreeTwoDenominator (concreteCOEExponent N K) := by
    simpa only [X, sourceMu] using
      betaPrimeTraceOneSource_square_integral_eq_exactVariance hN hdense
  have hSourceMean : (∫ source, X source ∂sourceMu) =
      (N : ℝ) * ((N : ℝ) + 1) := by
    simpa only [X, sourceMu] using
      U08.betaPrimeTraceOneSource_integral_eq_internal
        (N := N) (K := K) hN (by omega)
  have hVar : variance X sourceMu =
      h12TraceOneRawMeanNumerator (N : ℝ) (concreteCOEExponent N K) /
          h8H10DegreeTwoDenominator (concreteCOEExponent N K) -
        ((N : ℝ) * ((N : ℝ) + 1)) ^ 2 := by
    rw [variance_eq_sub hX]
    simp only [Pi.pow_apply, hSecond, hSourceMean]
  have hSourceSq :
      lpNorm (fun source ↦ X source - ∫ z, X z ∂sourceMu) 2 sourceMu ^ 2 ≤
        (60 / 11 : ℝ) * (N : ℝ) ^ 2 := by
    rw [U08.lpNorm_centered_two_eq_sqrt_variance hX,
      Real.sq_sqrt (variance_nonneg X sourceMu), hVar]
    exact h12TraceOneCenteredVarianceQuotient_le_sixty_div_eleven_exactVariance
      (by exact_mod_cast hN)
      (thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense)
  have hgMem : MemLp g 2 targetMu := by
    simpa only [g, targetMu] using
      betaPrimeYTraceOne_centered_memLp_two_proved_allDimensions hN hgap
  have hTargetMean : (∫ u, betaPrimeYTraceOne N K u ∂targetMu) =
      (N : ℝ) * ((N : ℝ) + 1) := by
    simpa only [targetMu] using
      betaPrimeYTraceOne_integral_external hN (by omega)
  have hcomp : g ∘ realBetaPrimeTracePowerVector 4 N K =
      fun source ↦ X source - ∫ z, X z ∂sourceMu := by
    funext source
    change betaPrimeTraceOneSource N K source -
        (∫ u, betaPrimeYTraceOne N K u ∂targetMu) =
      betaPrimeTraceOneSource N K source - ∫ z, X z ∂sourceMu
    rw [hTargetMean, hSourceMean]
  have hMap := h9_lpNorm_source_map
    (p := (2 : ENNReal)) hgMem.aestronglyMeasurable
  rw [hcomp] at hMap
  change lpNorm g 2 targetMu ^ 2 ≤ _
  rw [hMap]
  exact hSourceSq

theorem betaPrimeYTraceOne_centered_lpNorm_two_le_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun u ↦ betaPrimeYTraceOne N K u -
        ∫ z, betaPrimeYTraceOne N K z ∂betaPrimeTraceFourLaw N K)
          2 (betaPrimeTraceFourLaw N K) ≤
      exactVarianceCenteredTraceOneL2Constant * (N : ℝ) := by
  apply le_of_sq_le_sq
  · calc
      _ ≤ (60 / 11 : ℝ) * (N : ℝ) ^ 2 :=
        betaPrimeYTraceOne_centered_lpNorm_two_sq_le_exactVariance hN hdense
      _ ≤ (exactVarianceCenteredTraceOneL2Constant * (N : ℝ)) ^ 2 := by
        unfold exactVarianceCenteredTraceOneL2Constant
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
        nlinarith [sq_nonneg (N : ℝ)]
  · unfold exactVarianceCenteredTraceOneL2Constant
    positivity

/-! ## Concrete centered first trace -/

theorem concreteCOETraceOne_centered_lpNorm_two_sq_le_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun A ↦ concreteCOETraceOne N K A -
        (N : ℝ) * ((N : ℝ) + 1)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ^ 2 ≤
      (60 / 11 : ℝ) * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have h2NK : 2 * N ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  let g : (Fin 4 → ℝ) → ℝ := fun u ↦ betaPrimeYTraceOne N K u -
    ∫ z, betaPrimeYTraceOne N K z ∂betaPrimeTraceFourLaw N K
  have hmem := betaPrimeYTraceOne_centered_memLp_two_proved_allDimensions hN hgap
  have hraw : lpNorm (g ∘ f) 2 mu ^ 2 ≤
      (60 / 11 : ℝ) * (N : ℝ) ^ 2 := by
    rw [lpNorm_comp_concreteCOETracePowerVector hN h2NK
      hmem.aestronglyMeasurable]
    exact betaPrimeYTraceOne_centered_lpNorm_two_sq_le_exactVariance hN hdense
  have hmean := betaPrimeYTraceOne_integral_external hN
    (by omega : 2 * N + 2 ≤ K)
  have hfun : g ∘ f = fun A ↦ concreteCOETraceOne N K A -
      (N : ℝ) * ((N : ℝ) + 1) := by
    funext A
    simp only [g, f, Function.comp_apply]
    rw [show betaPrimeYTraceOne N K
        (concreteCOETracePowerVector 4 N K A) =
        concreteCOETraceOne N K A by
      exact concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne N K A,
      hmean]
  rw [← hfun]
  exact hraw

theorem concreteCOETraceOne_centered_lpNorm_two_le_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun A ↦ concreteCOETraceOne N K A -
        (N : ℝ) * ((N : ℝ) + 1)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      exactVarianceCenteredTraceOneL2Constant * (N : ℝ) := by
  apply le_of_sq_le_sq
  · calc
      _ ≤ (60 / 11 : ℝ) * (N : ℝ) ^ 2 :=
        concreteCOETraceOne_centered_lpNorm_two_sq_le_exactVariance hN hdense
      _ ≤ (exactVarianceCenteredTraceOneL2Constant * (N : ℝ)) ^ 2 := by
        unfold exactVarianceCenteredTraceOneL2Constant
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
        nlinarith [sq_nonneg (N : ℝ)]
  · unfold exactVarianceCenteredTraceOneL2Constant
    positivity

/-! ## Exact positive raw means -/

theorem concreteCOETraceOne_lpNorm_one_eq_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCOETraceOne N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      (N : ℝ) * ((N : ℝ) + 1) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  have hmem : MemLp (concreteCOETraceOne N K) 1 mu := by
    simpa only [mu] using concreteCOETraceOne_memLp_one_internal hN hgap
  have hnonneg : ∀ᵐ A ∂mu, 0 ≤ concreteCOETraceOne N K A := by
    filter_upwards
      [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
        with A hsupport
    have hY := concreteCOEY_posSemidef_of_support hgap A hsupport.2
    have htr := hY.trace_nonneg
    change 0 ≤ (Matrix.trace (concreteCOEY N K A)).re
    exact (Complex.nonneg_iff.mp htr).1
  rw [lpNorm_one_eq_integral_norm hmem.aestronglyMeasurable]
  calc
    (∫ A, ‖concreteCOETraceOne N K A‖ ∂mu) =
        ∫ A, concreteCOETraceOne N K A ∂mu := by
      apply integral_congr_ae
      filter_upwards [hnonneg] with A hA
      rw [Real.norm_eq_abs, abs_of_nonneg hA]
    _ = (N : ℝ) * ((N : ℝ) + 1) := by
      simpa only [mu] using integral_concreteCOETraceOne hN hgap

theorem concreteCOETraceTwo_lpNorm_one_eq_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCOETraceTwo N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      h12TraceTwoRawMeanNumerator (N : ℝ) (concreteCOEExponent N K) /
        h8H10DegreeTwoDenominator (concreteCOEExponent N K) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  have hmem : MemLp (concreteCOETraceTwo N K) 1 mu := by
    simpa only [mu] using concreteCOETraceTwo_memLp_one_internal hN hgap
  have hnonneg : ∀ᵐ A ∂mu, 0 ≤ concreteCOETraceTwo N K A := by
    filter_upwards
      [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
        with A hsupport
    exact concreteCOETraceTwo_nonneg_of_support hgap A hsupport.2
  rw [lpNorm_one_eq_integral_norm hmem.aestronglyMeasurable]
  calc
    (∫ A, ‖concreteCOETraceTwo N K A‖ ∂mu) =
        ∫ A, concreteCOETraceTwo N K A ∂mu := by
      apply integral_congr_ae
      filter_upwards [hnonneg] with A hA
      rw [Real.norm_eq_abs, abs_of_nonneg hA]
    _ = ∫ u, betaPrimeYTraceTwo N K u
          ∂(betaPrimeTraceFourLaw N K) := by
      simpa only [mu] using integral_concreteCOETraceTwo_eq_betaPrime hN hgap
    _ = ∫ source, betaPrimeTraceTwoSource N K source
          ∂realBetaPrimeGaussianSourceLaw N K :=
      U08.betaPrimeYTraceTwo_integral_eq_source_internal N K
    _ = h12TraceTwoRawMeanNumerator (N : ℝ) (concreteCOEExponent N K) /
          h8H10DegreeTwoDenominator (concreteCOEExponent N K) :=
      betaPrimeTraceTwoSource_integral_eq_exactVariance hN hdense

/-! ## Central density scores -/

theorem concreteCentralLogScoreOne_lpNorm_one_le_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCentralLogScoreOne N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      exactVarianceCentralScoreOneConstant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let centered : ConcreteMatrixState N → ℝ := fun A ↦
    concreteCOETraceOne N K A - (N : ℝ) * ((N : ℝ) + 1)
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hmem : MemLp centered 2 mu := by
    simpa only [centered, mu] using concreteCOETraceOne_centered_memLp_two hN hgap
  have hnormTwo : lpNorm centered 2 mu ≤
      exactVarianceCenteredTraceOneL2Constant * (N : ℝ) := by
    simpa only [centered, mu] using
      concreteCOETraceOne_centered_lpNorm_two_le_exactVariance hN hdense
  have hnormOne := (lpNorm_one_le_lpNorm_two_of_memLp hmem).trans hnormTwo
  rw [show concreteCentralLogScoreOne N K = (2 : ℝ) • centered by
    funext A
    simp [concreteCentralLogScoreOne, centered], lpNorm_const_smul]
  change |(2 : ℝ)| * lpNorm centered 1 mu ≤ _
  norm_num [exactVarianceCenteredTraceOneL2Constant] at hnormOne
  norm_num [exactVarianceCentralScoreOneConstant] at ⊢
  linarith

theorem concreteCentralDensityScoreTwo_lpNorm_one_le_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCentralDensityScoreTwo N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      exactVarianceCentralScoreTwoConstant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let centered : ConcreteMatrixState N → ℝ := fun A ↦
    concreteCOETraceOne N K A - (N : ℝ) * ((N : ℝ) + 1)
  let ellOne : ConcreteMatrixState N → ℝ := (2 : ℝ) • centered
  let ellTwo : ConcreteMatrixState N → ℝ := fun A ↦
    -8 * (concreteCOETraceOne N K A +
      concreteCOETraceTwo N K A / concreteCOEExponent N K)
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hc13 : 13 * (N : ℝ) ≤ concreteCOEExponent N K :=
    thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense
  have hcpos : 0 < concreteCOEExponent N K := by
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mu] using concreteCOETraceOne_centered_memLp_two hN hgap
  have hcenteredSq : lpNorm centered 2 mu ^ 2 ≤
      (60 / 11 : ℝ) * (N : ℝ) ^ 2 := by
    simpa only [centered, mu] using
      concreteCOETraceOne_centered_lpNorm_two_sq_le_exactVariance hN hdense
  have hellOne : MemLp ellOne 2 mu := hcentered.const_smul 2
  have hellOneSq : lpNorm ellOne 2 mu ^ 2 ≤
      (240 / 11 : ℝ) * (N : ℝ) ^ 2 := by
    rw [show ellOne = (2 : ℝ) • centered by rfl, lpNorm_const_smul]
    change (|(2 : ℝ)| * lpNorm centered 2 mu) ^ 2 ≤ _
    norm_num at ⊢
    nlinarith
  have hTraceOne : MemLp (concreteCOETraceOne N K) 1 mu := by
    simpa only [mu] using concreteCOETraceOne_memLp_one_internal hN hgap
  have hTraceTwo : MemLp (concreteCOETraceTwo N K) 1 mu := by
    simpa only [mu] using concreteCOETraceTwo_memLp_one_internal hN hgap
  have hTraceOneNorm : lpNorm (concreteCOETraceOne N K) 1 mu =
      (N : ℝ) * ((N : ℝ) + 1) := by
    simpa only [mu] using concreteCOETraceOne_lpNorm_one_eq_exactVariance hN hdense
  have hTraceTwoNorm : lpNorm (concreteCOETraceTwo N K) 1 mu =
      h12TraceTwoRawMeanNumerator (N : ℝ) (concreteCOEExponent N K) /
        h8H10DegreeTwoDenominator (concreteCOEExponent N K) := by
    simpa only [mu] using concreteCOETraceTwo_lpNorm_one_eq_exactVariance hN hdense
  have hellTwo : MemLp ellTwo 1 mu := by
    rw [show ellTwo = (-8 : ℝ) •
        ((concreteCOETraceOne N K) +
          (1 / concreteCOEExponent N K : ℝ) •
            concreteCOETraceTwo N K) by
      funext A
      simp [ellTwo]
      ring]
    exact (hTraceOne.add (hTraceTwo.const_smul _)).const_smul _
  have hsum := lpNorm_add_le hTraceOne (p := (1 : ENNReal)) (by norm_num)
    (g := (1 / concreteCOEExponent N K : ℝ) • concreteCOETraceTwo N K)
  have hsumNorm : lpNorm ((concreteCOETraceOne N K) +
      (1 / concreteCOEExponent N K : ℝ) • concreteCOETraceTwo N K) 1 mu ≤
      (N : ℝ) * ((N : ℝ) + 1) +
        (h12TraceTwoRawMeanNumerator (N : ℝ) (concreteCOEExponent N K) /
          h8H10DegreeTwoDenominator (concreteCOEExponent N K)) /
            concreteCOEExponent N K := by
    calc
      _ ≤ lpNorm (concreteCOETraceOne N K) 1 mu +
          lpNorm ((1 / concreteCOEExponent N K : ℝ) •
            concreteCOETraceTwo N K) 1 mu := hsum
      _ = (N : ℝ) * ((N : ℝ) + 1) +
          (h12TraceTwoRawMeanNumerator (N : ℝ) (concreteCOEExponent N K) /
            h8H10DegreeTwoDenominator (concreteCOEExponent N K)) /
              concreteCOEExponent N K := by
        rw [lpNorm_const_smul, hTraceOneNorm, hTraceTwoNorm]
        simp only [coe_nnnorm, Real.norm_eq_abs]
        rw [show |(1 / concreteCOEExponent N K : ℝ)| =
            1 / concreteCOEExponent N K by
          rw [abs_of_pos (one_div_pos.mpr hcpos)]]
        ring
  have hellTwoNorm : lpNorm ellTwo 1 mu ≤
      (240 / 11 : ℝ) * (N : ℝ) ^ 2 := by
    rw [show ellTwo = (-8 : ℝ) •
        ((concreteCOETraceOne N K) +
          (1 / concreteCOEExponent N K : ℝ) •
            concreteCOETraceTwo N K) by
      funext A
      simp [ellTwo]
      ring, lpNorm_const_smul]
    change |(-8 : ℝ)| * _ ≤ _
    norm_num at ⊢
    calc
      8 * lpNorm ((concreteCOETraceOne N K) +
          (concreteCOEExponent N K)⁻¹ • concreteCOETraceTwo N K) 1 mu ≤
        8 * ((N : ℝ) * ((N : ℝ) + 1) +
          (h12TraceTwoRawMeanNumerator (N : ℝ) (concreteCOEExponent N K) /
            h8H10DegreeTwoDenominator (concreteCOEExponent N K)) /
              concreteCOEExponent N K) :=
        mul_le_mul_of_nonneg_left (by simpa only [one_div] using hsumNorm)
          (by norm_num)
      _ ≤ (240 / 11 : ℝ) * (N : ℝ) ^ 2 :=
        h12CentralLogScoreTwoMeanQuotient_le_240_div_11_exactVariance
          (by exact_mod_cast hN) hc13
  have hsq : MemLp (fun A ↦ ellOne A * ellOne A) 1 mu :=
    hellOne.mul' hellOne
  have hsqNorm : lpNorm (fun A ↦ ellOne A ^ 2) 1 mu ≤
      (240 / 11 : ℝ) * (N : ℝ) ^ 2 := by
    have hholder := lpNorm_mul_le_lpNorm_two_mul hellOne hellOne
    have hpoint : (fun A ↦ ellOne A ^ 2) = fun A ↦ ellOne A * ellOne A := by
      funext A
      ring
    rw [hpoint]
    calc
      _ ≤ lpNorm ellOne 2 mu * lpNorm ellOne 2 mu := hholder
      _ = lpNorm ellOne 2 mu ^ 2 := by ring
      _ ≤ (240 / 11 : ℝ) * (N : ℝ) ^ 2 := hellOneSq
  have hpoint : concreteCentralDensityScoreTwo N K =
      (fun A ↦ ellOne A ^ 2) + ellTwo := by
    funext A
    simp only [concreteCentralDensityScoreTwo, secondDensityBell, Pi.add_apply]
    change concreteCentralLogScoreOne N K A ^ 2 +
        concreteCentralLogScoreTwo N K A = ellOne A ^ 2 + ellTwo A
    simp only [concreteCentralLogScoreOne, concreteCentralLogScoreTwo,
      ellOne, ellTwo, centered, Pi.smul_apply, smul_eq_mul]
  rw [hpoint]
  calc
    lpNorm ((fun A ↦ ellOne A ^ 2) + ellTwo) 1 mu ≤
        lpNorm (fun A ↦ ellOne A ^ 2) 1 mu + lpNorm ellTwo 1 mu :=
      lpNorm_add_le (by simpa [pow_two] using hsq) (by norm_num)
    _ ≤ (240 / 11 : ℝ) * (N : ℝ) ^ 2 +
        (240 / 11 : ℝ) * (N : ℝ) ^ 2 :=
      add_le_add hsqNorm hellTwoNorm
    _ ≤ exactVarianceCentralScoreTwoConstant * (N : ℝ) ^ 2 := by
      unfold exactVarianceCentralScoreTwoConstant
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
      nlinarith [sq_nonneg (N : ℝ)]

/-! ## Averaged quadratic orbital score -/

theorem concreteCenteredQuadraticDensity_lpNorm_two_le_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredQuadraticDensity N K) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      exactVarianceOrbitalScoreTwoConstant := by
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hc : (N : ℝ) ≤ concreteCOEExponent N K := by
    have hc13 := thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense
    nlinarith
  have H := concreteCOE_centeredQuadraticTraceInputs_of_bracket_zero
    hN hdense
      (integral_concreteCenteredQuadraticTraceBracket_eq_zero_dense_H14Rewire
        hN hdense)
  let Hsharp : CenteredQuadraticTraceInputs
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)
      (N : ℝ) (concreteCOEExponent N K)
      exactVarianceCenteredTraceOneL2Constant
      sharp34CenteredTraceTwoL2Constant
      sharp34CenteredTraceTwoL2Constant
      (concreteCOETraceOne N K) (concreteCOETraceTwo N K)
      (∫ A, concreteCOETraceOne N K A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K))
      (∫ A, concreteCOETraceOne N K A ^ 2
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K))
      (∫ A, concreteCOETraceTwo N K A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) := {
    trace_one_integrable := H.trace_one_integrable
    trace_square_integrable := H.trace_square_integrable
    trace_two_integrable := H.trace_two_integrable
    mean_one_eq := H.mean_one_eq
    mean_square_eq := H.mean_square_eq
    mean_two_eq := H.mean_two_eq
    bracket_integral_zero := H.bracket_integral_zero
    centered_one_memLp := H.centered_one_memLp
    centered_square_memLp := H.centered_square_memLp
    centered_two_memLp := H.centered_two_memLp
    centered_one_lpNorm_le := by
      rw [integral_concreteCOETraceOne hN (by omega)]
      exact concreteCOETraceOne_centered_lpNorm_two_le_exactVariance hN hdense
    centered_square_lpNorm_le := by
      exact concreteCOETraceOneSquare_centered_lpNorm_two_le_sharp34 hN hdense
    centered_two_lpNorm_le := by
      exact concreteCOETraceTwo_centered_lpNorm_two_le_sharp34 hN hdense }
  have hraw := Hsharp.normalized_bracket_lpNorm_two_le hNone hc
    (by norm_num [exactVarianceCenteredTraceOneL2Constant])
    (by norm_num [sharp34CenteredTraceTwoL2Constant])
    (by norm_num [sharp34CenteredTraceTwoL2Constant])
  change lpNorm (fun A ↦
      4 / ((N : ℝ) * ((N : ℝ) + 1)) *
        centeredQuadraticTraceBracket (N : ℝ) (concreteCOEExponent N K)
          (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
    exactVarianceOrbitalScoreTwoConstant
  calc
    _ ≤ 4 * (2 * sharp34CenteredTraceTwoL2Constant +
        2 * sharp34CenteredTraceTwoL2Constant +
        3 * exactVarianceCenteredTraceOneL2Constant) := hraw
    _ = exactVarianceOrbitalScoreTwoConstant := by
      norm_num [exactVarianceOrbitalScoreTwoConstant,
        sharp34CenteredTraceTwoL2Constant,
        exactVarianceCenteredTraceOneL2Constant]

theorem concreteCenteredQuadraticDensity_lpNorm_one_le_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredQuadraticDensity N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      exactVarianceOrbitalScoreTwoConstant := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hmem : MemLp (concreteCenteredQuadraticDensity N K) 2 mu := by
    simpa only [mu] using
      concreteCenteredQuadraticDensity_memLp_two_H14Rewire hN hdense
  exact (lpNorm_one_le_lpNorm_two_of_memLp hmem).trans <| by
    simpa only [mu] using
      concreteCenteredQuadraticDensity_lpNorm_two_le_exactVariance hN hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.LocalAnticoncentration

theorem abs_iteratedDeriv_one_concreteBaseCentralEventPath_le_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    |iteratedDeriv 1
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event) 0| ≤
      exactVarianceCentralScoreOneConstant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [(LogdetLean.GramHafnian.UltimateHiding.H3H4Central.coeCorner_centralEventPath_derivatives_external_derived_of_A1
    hN hgap event hevent).1]
  exact (abs_integral_indicator_le_lpNorm_one
    (concreteCentralLogScoreOne_memLp_one hN hgap) hevent).trans
      (concreteCentralLogScoreOne_lpNorm_one_le_exactVariance hN hdense)

theorem abs_iteratedDeriv_two_concreteBaseCentralEventPath_le_exactVariance
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    |iteratedDeriv 2
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event) y| ≤
      exactVarianceCentralScoreTwoConstant * (N : ℝ) ^ 2 := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let shifted := concreteCentralMatrixUpdate N y ⁻¹' event
  have hshifted : MeasurableSet shifted :=
    (measurable_concreteCentralMatrixUpdate N y) hevent
  rw [iteratedDeriv_concreteCentralEventPath_eq_zero_shift
    2 N mu event hevent y]
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [(LogdetLean.GramHafnian.UltimateHiding.H3H4Central.coeCorner_centralEventPath_derivatives_external_derived_of_A1
    hN hgap shifted hshifted).2]
  exact (abs_integral_indicator_le_lpNorm_one
    (concreteCentralDensityScoreTwo_memLp_one hN hdense) hshifted).trans
      (concreteCentralDensityScoreTwo_lpNorm_one_le_exactVariance hN hdense)

theorem abs_iteratedDeriv_two_concreteSharedBetaOrbitalEventPath_le_exactVariance
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    |iteratedDeriv 2
        (concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)
          q event) 0| ≤ exactVarianceOrbitalScoreTwoConstant := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let preevent := concreteCentralMatrixUpdate N
    (oneColumnCenteredScalarLog m N q) ⁻¹' event
  have hpre : MeasurableSet preevent :=
    (measurable_concreteCentralMatrixUpdate N _) hevent
  have hfun : concreteSharedBetaOrbitalEventPath m N mu q event =
      concreteProjectiveAveragedCenteredCOEEventPath N K preevent := by
    funext t
    exact concreteSharedBetaOrbitalEventPath_eq_projectiveCenteredCOE
      hN (by omega) q event hevent t
  rw [hfun,
    concrete_projectiveAveraged_centered_second_derivative_eq_density_indicator_integral_H14Rewire
      hN hdense preevent hpre]
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hmemOne : MemLp (concreteCenteredQuadraticDensity N K) 1 mu :=
    (concreteCenteredQuadraticDensity_memLp_two_H14Rewire
      hN hdense).mono_exponent (by norm_num)
  exact (abs_integral_indicator_le_lpNorm_one hmemOne hpre).trans
    (concreteCenteredQuadraticDensity_lpNorm_one_le_exactVariance hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
