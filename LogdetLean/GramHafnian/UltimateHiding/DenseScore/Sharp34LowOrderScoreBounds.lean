import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.Sharp34H8H10VarianceBounds
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.OptimizedLowOrderEventScore
import Mathlib.Tactic

/-!
# Low-order consequences of the sharp H8/H10 variance bounds

This module propagates the centered `L²` constant 34 to a raw second-trace
constant 54 and to the averaged quadratic score.  The H9 first-trace input is
left at its independently proved optimized value, so this module can be used
without any new assumption.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

def sharp34RawTraceTwoL2Constant : ℝ := 54

def sharp34RawTraceOneTwoConstant : ℝ :=
  optimizedRawTraceOneL3Constant * sharp34RawTraceTwoL2Constant

def sharp34OrbitalScoreTwoConstant : ℝ := 111136

theorem betaPrimeYTraceTwo_memLp_two_sharp34
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceTwo N K) 2 (betaPrimeTraceFourLaw N K) := by
  let mu := betaPrimeTraceFourLaw N K
  let mean : ℝ := ∫ u, betaPrimeYTraceTwo N K u ∂mu
  let centered : (Fin 4 → ℝ) → ℝ :=
    fun u ↦ betaPrimeYTraceTwo N K u - mean
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mean, mu] using
      (betaPrimeYTraceTwo_centered_two_momentPackage_sharp34 hN hgap).1
  rw [show betaPrimeYTraceTwo N K =
      centered + (fun _ : Fin 4 → ℝ ↦ mean) by
    funext u
    simp [centered]]
  exact hcentered.add (memLp_const mean)

/-- Raw second trace `L²` bound: `34*N² + 20*N³ ≤ 54*N³`. -/
theorem betaPrimeYTraceTwo_lpNorm_two_le_sharp34
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceTwo N K) 2 (betaPrimeTraceFourLaw N K) ≤
      sharp34RawTraceTwoL2Constant * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  let mean : ℝ := ∫ u, betaPrimeYTraceTwo N K u ∂mu
  let centered : (Fin 4 → ℝ) → ℝ :=
    fun u ↦ betaPrimeYTraceTwo N K u - mean
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mean, mu] using
      (betaPrimeYTraceTwo_centered_two_momentPackage_sharp34 hN hgap).1
  have hcenteredNorm : lpNorm centered 2 mu ≤
      sharp34CenteredTraceTwoL2Constant * (N : ℝ) ^ 2 := by
    simpa only [centered, mean, mu] using
      (betaPrimeYTraceTwo_centered_two_momentPackage_sharp34 hN hgap).2 hdense
  have hmeanAbs : |mean| ≤
      optimizedRawTraceTwoL1Constant * (N : ℝ) ^ 3 := by
    simpa only [mean, mu, U08.betaPrimeYTraceTwoFormalMeanU08,
      optimizedRawTraceTwoL1Constant] using
      h14_betaPrimeYTraceTwoFormalMeanU08_abs_le_twenty_cube_internal hN hdense
  have htri := lpNorm_add_le hcentered (p := (2 : ENNReal)) (by norm_num)
    (g := fun _ : Fin 4 → ℝ ↦ mean)
  have hconstNorm : lpNorm (fun _ : Fin 4 → ℝ ↦ mean) 2 mu = |mean| := by
    rw [lpNorm_const (p := (2 : ENNReal)) (by norm_num)
      (IsProbabilityMeasure.ne_zero mu) mean]
    simp [Real.norm_eq_abs]
  rw [show betaPrimeYTraceTwo N K =
      centered + (fun _ : Fin 4 → ℝ ↦ mean) by
    funext u
    simp [centered]]
  calc
    lpNorm (centered + (fun _ : Fin 4 → ℝ ↦ mean)) 2 mu ≤
        lpNorm centered 2 mu +
          lpNorm (fun _ : Fin 4 → ℝ ↦ mean) 2 mu := htri
    _ = lpNorm centered 2 mu + |mean| := by rw [hconstNorm]
    _ ≤ sharp34CenteredTraceTwoL2Constant * (N : ℝ) ^ 2 +
        optimizedRawTraceTwoL1Constant * (N : ℝ) ^ 3 :=
      add_le_add hcenteredNorm hmeanAbs
    _ ≤ sharp34RawTraceTwoL2Constant * (N : ℝ) ^ 3 := by
      have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := zero_le_one.trans hNr
      unfold sharp34CenteredTraceTwoL2Constant
        optimizedRawTraceTwoL1Constant sharp34RawTraceTwoL2Constant
      nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (sub_nonneg.mpr hNr)]

/-- Mixed raw trace moment with the improved second-trace factor 54. -/
theorem betaPrimeYTraceOneTwo_momentPackage_sharp34
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u * betaPrimeYTraceTwo N K u) 1
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u *
          betaPrimeYTraceTwo N K u) 1 (betaPrimeTraceFourLaw N K) ≤
          sharp34RawTraceOneTwoConstant * (N : ℝ) ^ 5) := by
  have hone := betaPrimeYTraceOne_memLp_two_proved_allDimensions hN hgap
  have htwo := betaPrimeYTraceTwo_memLp_two_sharp34 hN hgap
  constructor
  · exact htwo.mul' hone
  · intro hdense
    have honeNorm := betaPrimeYTraceOne_lpNorm_two_le_optimized hN hdense
    have htwoNorm := betaPrimeYTraceTwo_lpNorm_two_le_sharp34 hN hdense
    have hOneNonneg :
        0 ≤ optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
      unfold optimizedRawTraceOneL3Constant
      positivity
    calc
      lpNorm (fun u ↦ betaPrimeYTraceOne N K u *
          betaPrimeYTraceTwo N K u) 1 (betaPrimeTraceFourLaw N K) ≤
        lpNorm (betaPrimeYTraceOne N K) 2 (betaPrimeTraceFourLaw N K) *
          lpNorm (betaPrimeYTraceTwo N K) 2
            (betaPrimeTraceFourLaw N K) :=
        lpNorm_mul_le_lpNorm_two_mul hone htwo
      _ ≤ (optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2) *
          (sharp34RawTraceTwoL2Constant * (N : ℝ) ^ 3) :=
        mul_le_mul honeNorm htwoNorm lpNorm_nonneg hOneNonneg
      _ = sharp34RawTraceOneTwoConstant * (N : ℝ) ^ 5 := by
        unfold sharp34RawTraceOneTwoConstant
        ring

theorem concreteCOETraceTwo_lpNorm_two_le_sharp34
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCOETraceTwo N K) 2
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ≤
      sharp34RawTraceTwoL2Constant * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hmem := betaPrimeYTraceTwo_memLp_two_sharp34 hN hgap
  have htransport := lpNorm_comp_concreteCOETracePowerVector hN (by omega)
    (p := (2 : ENNReal)) hmem.aestronglyMeasurable
  have hfun : betaPrimeYTraceTwo N K ∘
      concreteCOETracePowerVector 4 N K = concreteCOETraceTwo N K := by
    funext A
    change concreteBetaPrimeYTraceTwo N K A = concreteCOETraceTwo N K A
    exact concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo N K A
  rw [hfun] at htransport
  rw [htransport]
  exact betaPrimeYTraceTwo_lpNorm_two_le_sharp34 hN hdense

theorem concreteCOETraceOneSquare_centered_lpNorm_two_le_sharp34
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun A ↦ concreteCOETraceOne N K A ^ 2 -
        ∫ B, concreteCOETraceOne N K B ^ 2
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      sharp34CenteredTraceTwoL2Constant * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have h2NK : 2 * N ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  let g : (Fin 4 → ℝ) → ℝ := fun u ↦
    betaPrimeYTraceOne N K u ^ 2 -
      ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂(betaPrimeTraceFourLaw N K)
  have hbeta :=
    betaPrimeYTraceOneSquare_centered_two_momentPackage_sharp34 hN hgap
  have hraw : lpNorm (g ∘ f) 2 mu ≤
      sharp34CenteredTraceTwoL2Constant * (N : ℝ) ^ 3 := by
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

theorem concreteCOETraceTwo_centered_lpNorm_two_le_sharp34
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun A ↦ concreteCOETraceTwo N K A -
        ∫ B, concreteCOETraceTwo N K B
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      sharp34CenteredTraceTwoL2Constant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have h2NK : 2 * N ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let f := concreteCOETracePowerVector 4 N K
  let g : (Fin 4 → ℝ) → ℝ := fun u ↦ betaPrimeYTraceTwo N K u -
    ∫ z, betaPrimeYTraceTwo N K z ∂(betaPrimeTraceFourLaw N K)
  have hbeta := betaPrimeYTraceTwo_centered_two_momentPackage_sharp34 hN hgap
  have hraw : lpNorm (g ∘ f) 2 mu ≤
      sharp34CenteredTraceTwoL2Constant * (N : ℝ) ^ 2 := by
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

/-- Averaged quadratic density bound using centered H8/H10 constant 34. -/
theorem concreteCenteredQuadraticDensity_lpNorm_two_le_sharp34
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredQuadraticDensity N K) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      sharp34OrbitalScoreTwoConstant := by
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
      exact concreteCOETraceOne_centered_lpNorm_two_le_optimized hN hdense
    centered_square_lpNorm_le := by
      exact concreteCOETraceOneSquare_centered_lpNorm_two_le_sharp34 hN hdense
    centered_two_lpNorm_le := by
      exact concreteCOETraceTwo_centered_lpNorm_two_le_sharp34 hN hdense }
  have hraw := Hsharp.normalized_bracket_lpNorm_two_le hNone hc
    (by norm_num [optimizedCenteredTraceOneL3Constant])
    (by norm_num [sharp34CenteredTraceTwoL2Constant])
    (by norm_num [sharp34CenteredTraceTwoL2Constant])
  change lpNorm (fun A ↦
      4 / ((N : ℝ) * ((N : ℝ) + 1)) *
        centeredQuadraticTraceBracket (N : ℝ) (concreteCOEExponent N K)
          (concreteCOETraceOne N K A) (concreteCOETraceTwo N K A)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
    sharp34OrbitalScoreTwoConstant
  calc
    _ ≤ 4 * (2 * sharp34CenteredTraceTwoL2Constant +
        2 * sharp34CenteredTraceTwoL2Constant +
        3 * optimizedCenteredTraceOneL3Constant) := hraw
    _ = sharp34OrbitalScoreTwoConstant := by
      norm_num [sharp34OrbitalScoreTwoConstant,
        sharp34CenteredTraceTwoL2Constant,
        optimizedCenteredTraceOneL3Constant]

theorem concreteCenteredQuadraticDensity_lpNorm_one_le_sharp34
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredQuadraticDensity N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      sharp34OrbitalScoreTwoConstant := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hmem : MemLp (concreteCenteredQuadraticDensity N K) 2 mu := by
    simpa only [mu] using
      concreteCenteredQuadraticDensity_memLp_two_H14Rewire hN hdense
  exact (lpNorm_one_le_lpNorm_two_of_memLp hmem).trans <| by
    simpa only [mu] using
      concreteCenteredQuadraticDensity_lpNorm_two_le_sharp34 hN hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Eventwise second-order orbital score with the sharp H8/H10 constant. -/
theorem abs_iteratedDeriv_two_concreteSharedBetaOrbitalEventPath_le_sharp34
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    |iteratedDeriv 2
        (concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)
          q event) 0| ≤ sharp34OrbitalScoreTwoConstant := by
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
    (concreteCenteredQuadraticDensity_lpNorm_one_le_sharp34 hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
