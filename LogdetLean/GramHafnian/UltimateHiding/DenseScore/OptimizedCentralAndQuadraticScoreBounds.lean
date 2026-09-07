import LogdetLean.GramHafnian.UltimateHiding.DenseScore.OptimizedLowerTraceMomentBounds
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_CanonicalQuadraticScoreRewire
import Mathlib.Tactic

/-!
# Optimized low-order central and orbital score bounds

This module retains the exact constants in the proved H8--H10 trace estimates
instead of relaxing all three centered inputs to `2^40`.  It introduces no
scientific assumption.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Optimized dimension-free multiplier for the first central score. -/
def optimizedCentralScoreOneConstant : ℝ := 18432

/-- Optimized dimension-free multiplier for the second central density score. -/
def optimizedCentralScoreTwoConstant : ℝ := 339812384

/-- Optimized dimension-free multiplier for the averaged quadratic score. -/
def optimizedOrbitalScoreTwoConstant : ℝ := 241664

/-! ## Sharp transfers from the beta-prime trace law -/

theorem concreteCOETraceOne_centered_lpNorm_two_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun A ↦ concreteCOETraceOne N K A -
        (N : ℝ) * ((N : ℝ) + 1)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedCenteredTraceOneL3Constant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have h2NK : 2 * N ≤ K := by omega
  let f := concreteCOETracePowerVector 4 N K
  let g : (Fin 4 → ℝ) → ℝ := fun u ↦ betaPrimeYTraceOne N K u -
    ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)
  have hmem :=
    (betaPrimeYTraceOne_centered_three_momentPackage_optimized hN hgap).1
  have hraw : lpNorm (g ∘ f) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedCenteredTraceOneL3Constant * (N : ℝ) := by
    rw [lpNorm_comp_concreteCOETracePowerVector hN h2NK
      hmem.aestronglyMeasurable]
    exact betaPrimeYTraceOne_centered_lpNorm_two_le_optimized hN hdense
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

theorem concreteCOETraceOne_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCOETraceOne N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hmem := betaPrimeYTraceOne_memLp_one_proved_allDimensions hN hgap
  have htransport := lpNorm_comp_concreteCOETracePowerVector hN (by omega)
    (p := (1 : ENNReal)) hmem.aestronglyMeasurable
  have hfun : betaPrimeYTraceOne N K ∘
      concreteCOETracePowerVector 4 N K = concreteCOETraceOne N K := by
    funext A
    change concreteBetaPrimeYTraceOne N K A = concreteCOETraceOne N K A
    exact concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne N K A
  rw [hfun] at htransport
  rw [htransport]
  exact betaPrimeYTraceOne_lpNorm_one_le_optimized hN hdense

theorem concreteCOETraceTwo_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCOETraceTwo N K) 1
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedRawTraceTwoL1Constant * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hmem := betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap
  have htransport := lpNorm_comp_concreteCOETracePowerVector hN (by omega)
    (p := (1 : ENNReal)) hmem.aestronglyMeasurable
  have hfun : betaPrimeYTraceTwo N K ∘
      concreteCOETracePowerVector 4 N K = concreteCOETraceTwo N K := by
    funext A
    change concreteBetaPrimeYTraceTwo N K A = concreteCOETraceTwo N K A
    exact concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo N K A
  rw [hfun] at htransport
  rw [htransport]
  exact betaPrimeYTraceTwo_lpNorm_one_le_optimized hN hdense

theorem concreteCOETraceOneSquare_centered_lpNorm_two_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun A ↦ concreteCOETraceOne N K A ^ 2 -
        ∫ B, concreteCOETraceOne N K B ^ 2
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedCenteredTraceTwoL2Constant * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have h2NK : 2 * N ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  let g : (Fin 4 → ℝ) → ℝ := fun u ↦
    betaPrimeYTraceOne N K u ^ 2 -
      ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂(betaPrimeTraceFourLaw N K)
  have hbeta :=
    betaPrimeYTraceOneSquare_centered_two_momentPackage_optimized hN hgap
  have hraw : lpNorm (g ∘ f) 2 mu ≤
      optimizedCenteredTraceTwoL2Constant * (N : ℝ) ^ 3 := by
    rw [lpNorm_comp_concreteCOETracePowerVector hN h2NK
      hbeta.1.aestronglyMeasurable]
    exact hbeta.2 hdense
  have hmean := integral_concreteCOETraceOne_sq_eq_betaPrime hN hgap
  have hfun : g ∘ f = fun A ↦ concreteCOETraceOne N K A ^ 2 -
      ∫ B, concreteCOETraceOne N K B ^ 2 ∂mu := by
    funext A
    simp only [g, f, Function.comp_apply]
    rw [show betaPrimeYTraceOne N K
        (concreteCOETracePowerVector 4 N K A) =
        concreteCOETraceOne N K A by
      exact concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne N K A,
      hmean]
  rw [← hfun]
  exact hraw

theorem concreteCOETraceTwo_centered_lpNorm_two_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun A ↦ concreteCOETraceTwo N K A -
        ∫ B, concreteCOETraceTwo N K B
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedCenteredTraceTwoL2Constant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have h2NK : 2 * N ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  let g : (Fin 4 → ℝ) → ℝ := fun u ↦ betaPrimeYTraceTwo N K u -
    ∫ z, betaPrimeYTraceTwo N K z ∂(betaPrimeTraceFourLaw N K)
  have hbeta := betaPrimeYTraceTwo_centered_two_momentPackage_optimized hN hgap
  have hraw : lpNorm (g ∘ f) 2 mu ≤
      optimizedCenteredTraceTwoL2Constant * (N : ℝ) ^ 2 := by
    rw [lpNorm_comp_concreteCOETracePowerVector hN h2NK
      hbeta.1.aestronglyMeasurable]
    exact hbeta.2 hdense
  have hmean := integral_concreteCOETraceTwo_eq_betaPrime hN hgap
  have hfun : g ∘ f = fun A ↦ concreteCOETraceTwo N K A -
      ∫ B, concreteCOETraceTwo N K B ∂mu := by
    funext A
    simp only [g, f, Function.comp_apply]
    rw [show betaPrimeYTraceTwo N K
        (concreteCOETracePowerVector 4 N K A) =
        concreteCOETraceTwo N K A by
      exact concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo N K A,
      hmean]
  rw [← hfun]
  exact hraw

/-! ## Optimized central scores -/

theorem concreteCentralLogScoreOne_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCentralLogScoreOne N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedCentralScoreOneConstant * (N : ℝ) := by
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
      optimizedCenteredTraceOneL3Constant * (N : ℝ) := by
    simpa only [centered, mu] using
      concreteCOETraceOne_centered_lpNorm_two_le_optimized hN hdense
  have hnormOne := (lpNorm_one_le_lpNorm_two_of_memLp hmem).trans hnormTwo
  rw [show concreteCentralLogScoreOne N K = (2 : ℝ) • centered by
    funext A
    simp [concreteCentralLogScoreOne, centered], lpNorm_const_smul]
  change |(2 : ℝ)| * lpNorm centered 1 mu ≤ _
  norm_num [optimizedCenteredTraceOneL3Constant] at hnormOne
  norm_num [optimizedCentralScoreOneConstant] at ⊢
  linarith

theorem concreteCentralDensityScoreTwo_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCentralDensityScoreTwo N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedCentralScoreTwoConstant * (N : ℝ) ^ 2 := by
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
    U08.thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense
  have hcpos : 0 < concreteCOEExponent N K := by
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mu] using concreteCOETraceOne_centered_memLp_two hN hgap
  have hcenteredNorm : lpNorm centered 2 mu ≤
      optimizedCenteredTraceOneL3Constant * (N : ℝ) := by
    simpa only [centered, mu] using
      concreteCOETraceOne_centered_lpNorm_two_le_optimized hN hdense
  have hellOne : MemLp ellOne 2 mu := hcentered.const_smul 2
  have hellOneNorm : lpNorm ellOne 2 mu ≤ 18432 * (N : ℝ) := by
    rw [show ellOne = (2 : ℝ) • centered by rfl, lpNorm_const_smul]
    change |(2 : ℝ)| * lpNorm centered 2 mu ≤ _
    norm_num [optimizedCenteredTraceOneL3Constant] at hcenteredNorm
    norm_num at ⊢
    linarith
  have hTraceOne : MemLp (concreteCOETraceOne N K) 1 mu := by
    simpa only [mu] using concreteCOETraceOne_memLp_one_internal hN hgap
  have hTraceTwo : MemLp (concreteCOETraceTwo N K) 1 mu := by
    simpa only [mu] using concreteCOETraceTwo_memLp_one_internal hN hgap
  have hTraceOneNorm : lpNorm (concreteCOETraceOne N K) 1 mu ≤
      9218 * (N : ℝ) ^ 2 := by
    simpa only [mu, optimizedRawTraceOneL3Constant] using
      concreteCOETraceOne_lpNorm_one_le_optimized hN hdense
  have hTraceTwoNorm : lpNorm (concreteCOETraceTwo N K) 1 mu ≤
      20 * (N : ℝ) ^ 3 := by
    simpa only [mu, optimizedRawTraceTwoL1Constant] using
      concreteCOETraceTwo_lpNorm_one_le_optimized hN hdense
  have hellTwo : MemLp ellTwo 1 mu := by
    rw [show ellTwo = (-8 : ℝ) •
        ((concreteCOETraceOne N K) +
          (1 / concreteCOEExponent N K : ℝ) •
            concreteCOETraceTwo N K) by
      funext A
      simp [ellTwo]
      ring]
    exact (hTraceOne.add (hTraceTwo.const_smul _)).const_smul _
  have htwoScaled :
      lpNorm ((1 / concreteCOEExponent N K : ℝ) •
        concreteCOETraceTwo N K) 1 mu ≤ 2 * (N : ℝ) ^ 2 := by
    rw [lpNorm_const_smul]
    change |1 / concreteCOEExponent N K| *
        lpNorm (concreteCOETraceTwo N K) 1 mu ≤ _
    rw [abs_of_pos (one_div_pos.mpr hcpos)]
    calc
      (1 / concreteCOEExponent N K) *
          lpNorm (concreteCOETraceTwo N K) 1 mu ≤
        (1 / concreteCOEExponent N K) * (20 * (N : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hTraceTwoNorm (by positivity)
      _ ≤ 2 * (N : ℝ) ^ 2 := by
        rw [show (1 / concreteCOEExponent N K) * (20 * (N : ℝ) ^ 3) =
            (20 * (N : ℝ) ^ 3) / concreteCOEExponent N K by ring]
        apply (div_le_iff₀ hcpos).2
        have hN0 : (0 : ℝ) ≤ (N : ℝ) := by positivity
        have htwenty : 20 * (N : ℝ) ^ 3 ≤ 26 * (N : ℝ) ^ 3 := by
          nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) hN0]
        have htwentysix : 26 * (N : ℝ) ^ 3 ≤
            (2 * (N : ℝ) ^ 2) * concreteCOEExponent N K := by
          calc
            26 * (N : ℝ) ^ 3 =
                (2 * (N : ℝ) ^ 2) * (13 * (N : ℝ)) := by ring
            _ ≤ (2 * (N : ℝ) ^ 2) * concreteCOEExponent N K :=
              mul_le_mul_of_nonneg_left hc13 (by positivity)
        exact htwenty.trans htwentysix
  have hellTwoNorm : lpNorm ellTwo 1 mu ≤ 73760 * (N : ℝ) ^ 2 := by
    have hsum := lpNorm_add_le hTraceOne (p := (1 : ENNReal)) (by norm_num)
      (g := (1 / concreteCOEExponent N K : ℝ) • concreteCOETraceTwo N K)
    have hsumNorm : lpNorm ((concreteCOETraceOne N K) +
        (1 / concreteCOEExponent N K : ℝ) •
          concreteCOETraceTwo N K) 1 mu ≤ 9220 * (N : ℝ) ^ 2 := by
      calc
        _ ≤ lpNorm (concreteCOETraceOne N K) 1 mu +
            lpNorm ((1 / concreteCOEExponent N K : ℝ) •
              concreteCOETraceTwo N K) 1 mu := hsum
        _ ≤ 9218 * (N : ℝ) ^ 2 + 2 * (N : ℝ) ^ 2 :=
          add_le_add hTraceOneNorm htwoScaled
        _ = 9220 * (N : ℝ) ^ 2 := by ring
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
          8 * (9220 * (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (by simpa only [one_div] using hsumNorm)
          (by norm_num)
      _ = 73760 * (N : ℝ) ^ 2 := by ring
  have hsq : MemLp (fun A ↦ ellOne A * ellOne A) 1 mu :=
    hellOne.mul' hellOne
  have hsqNorm : lpNorm (fun A ↦ ellOne A ^ 2) 1 mu ≤
      339738624 * (N : ℝ) ^ 2 := by
    have hholder := lpNorm_mul_le_lpNorm_two_mul hellOne hellOne
    have hpoint : (fun A ↦ ellOne A ^ 2) = fun A ↦ ellOne A * ellOne A := by
      funext A
      ring
    rw [hpoint]
    calc
      _ ≤ lpNorm ellOne 2 mu * lpNorm ellOne 2 mu := hholder
      _ ≤ (18432 * (N : ℝ)) * (18432 * (N : ℝ)) :=
        mul_le_mul hellOneNorm hellOneNorm lpNorm_nonneg (by positivity)
      _ = 339738624 * (N : ℝ) ^ 2 := by ring
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
    _ ≤ 339738624 * (N : ℝ) ^ 2 + 73760 * (N : ℝ) ^ 2 :=
      add_le_add hsqNorm hellTwoNorm
    _ = optimizedCentralScoreTwoConstant * (N : ℝ) ^ 2 := by
      unfold optimizedCentralScoreTwoConstant
      ring

/-! ## Optimized averaged quadratic score -/

theorem concreteCenteredQuadraticDensity_lpNorm_two_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredQuadraticDensity N K) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedOrbitalScoreTwoConstant := by
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hc : (N : ℝ) ≤ concreteCOEExponent N K := by
    have hc13 := U08.thirteen_mul_dimension_le_concreteCOEExponent_of_dense
      hN hdense
    nlinarith
  have H := concreteCOE_centeredQuadraticTraceInputs_of_bracket_zero
    hN hdense
      (integral_concreteCenteredQuadraticTraceBracket_eq_zero_dense_H14Rewire
        hN hdense)
  let Hsharp : CenteredQuadraticTraceInputs
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)
      (N : ℝ) (concreteCOEExponent N K)
      optimizedCenteredTraceOneL3Constant
      optimizedCenteredTraceTwoL2Constant
      optimizedCenteredTraceTwoL2Constant
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
      exact concreteCOETraceOne_centered_lpNorm_two_le_optimized hN hdense
    centered_square_lpNorm_le := by
      exact concreteCOETraceOneSquare_centered_lpNorm_two_le_optimized hN hdense
    centered_two_lpNorm_le := by
      exact concreteCOETraceTwo_centered_lpNorm_two_le_optimized hN hdense }
  have hraw := Hsharp.normalized_bracket_lpNorm_two_le hNone hc
    (by norm_num [optimizedCenteredTraceOneL3Constant])
    (by norm_num [optimizedCenteredTraceTwoL2Constant])
    (by norm_num [optimizedCenteredTraceTwoL2Constant])
  change lpNorm (fun A ↦
      4 / ((N : ℝ) * ((N : ℝ) + 1)) *
        centeredQuadraticTraceBracket (N : ℝ) (concreteCOEExponent N K)
          (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
    optimizedOrbitalScoreTwoConstant
  calc
    _ ≤ 4 * (2 * optimizedCenteredTraceTwoL2Constant +
        2 * optimizedCenteredTraceTwoL2Constant +
        3 * optimizedCenteredTraceOneL3Constant) := hraw
    _ = optimizedOrbitalScoreTwoConstant := by
      norm_num [optimizedOrbitalScoreTwoConstant,
        optimizedCenteredTraceTwoL2Constant,
        optimizedCenteredTraceOneL3Constant]

theorem concreteCenteredQuadraticDensity_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredQuadraticDensity N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      optimizedOrbitalScoreTwoConstant := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hmem : MemLp (concreteCenteredQuadraticDensity N K) 2 mu := by
    simpa only [mu] using
      concreteCenteredQuadraticDensity_memLp_two_H14Rewire hN hdense
  exact (lpNorm_one_le_lpNorm_two_of_memLp hmem).trans <| by
    simpa only [mu] using
      concreteCenteredQuadraticDensity_lpNorm_two_le_optimized hN hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
