import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteTraceMomentTransfer
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteScaledCOECornerProbability
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9MomentRewire
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Concrete central COE score bounds

This file derives the first two central density-score bounds from the literal
beta-prime trace moments.  The density scores are explicit functions; no event
derivative, total-variation, or hiding estimate is assumed here.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-- First logarithmic score for scalar transpose congruence. -/
def concreteCentralLogScoreOne (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  2 * (concreteCOETraceOne N K A - (N : ℝ) * ((N : ℝ) + 1))

/-- Second logarithmic score, with the forward-pushforward sign convention. -/
def concreteCentralLogScoreTwo (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  -8 * (concreteCOETraceOne N K A +
    concreteCOETraceTwo N K A / concreteCOEExponent N K)

/-- Second central density score, i.e. the second Bell polynomial. -/
def concreteCentralDensityScoreTwo (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  secondDensityBell (concreteCentralLogScoreOne N K A)
    (concreteCentralLogScoreTwo N K A)

def concreteCentralScoreOneConstant : ℝ :=
  2 * denseClassicalMomentConstant

def concreteCentralScoreTwoConstant : ℝ :=
  4 * denseClassicalMomentConstant ^ 2 +
    8 * (derivedRawTraceOneConstant + derivedPositiveRawTraceTwoConstant)

/-- On a probability space, the real `L^1` norm is at most `L^2`. -/
theorem lpNorm_one_le_lpNorm_two_of_memLp
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {f : Omega → ℝ} (hf : MemLp f 2 mu) :
    lpNorm f 1 mu ≤ lpNorm f 2 mu := by
  have hmono := eLpNorm_le_eLpNorm_of_exponent_le
    (μ := mu) (f := f) (p := (1 : ENNReal)) (q := (2 : ENNReal))
    (by norm_num) hf.aestronglyMeasurable
  have hfOne : MemLp f 1 mu := hf.mono_exponent (by norm_num)
  rw [← toReal_eLpNorm hfOne.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top hmono

/-- Exact first-trace mean in the concrete COE model. -/
theorem integral_concreteCOETraceOne
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    (∫ A, concreteCOETraceOne N K A
      ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)) =
      (N : ℝ) * ((N : ℝ) + 1) := by
  rw [integral_concreteCOETraceOne_eq_betaPrime hN hgap]
  exact betaPrimeYTraceOne_integral_external hN (by omega)

/-- The centered first trace belongs to `L^2` under the concrete COE law. -/
theorem concreteCOETraceOne_centered_memLp_two
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun A ↦ concreteCOETraceOne N K A -
        (N : ℝ) * ((N : ℝ) + 1)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have h2NK : 2 * N ≤ K := by omega
  let f := concreteCOETracePowerVector 4 N K
  let g : (Fin 4 → ℝ) → ℝ := fun u ↦ betaPrimeYTraceOne N K u -
    ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)
  have hraw : MemLp (g ∘ f) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) :=
    memLp_comp_concreteCOETracePowerVector hN h2NK
      (betaPrimeYTraceOne_centered_memLp_two_proved_allDimensions hN hgap)
  have hmean := betaPrimeYTraceOne_integral_external hN (by omega : 2 * N + 2 ≤ K)
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

/-- Dimension-sharp `L^2` estimate for the centered first trace. -/
theorem concreteCOETraceOne_centered_lpNorm_two_le
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun A ↦ concreteCOETraceOne N K A -
        (N : ℝ) * ((N : ℝ) + 1)) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      denseClassicalMomentConstant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have h2NK : 2 * N ≤ K := by omega
  let f := concreteCOETracePowerVector 4 N K
  let g : (Fin 4 → ℝ) → ℝ := fun u ↦ betaPrimeYTraceOne N K u -
    ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)
  have hmem :=
    betaPrimeYTraceOne_centered_memLp_two_proved_allDimensions hN hgap
  have hraw : lpNorm (g ∘ f) 2
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      denseClassicalMomentConstant * (N : ℝ) := by
    rw [lpNorm_comp_concreteCOETracePowerVector hN h2NK
      hmem.aestronglyMeasurable]
    exact betaPrimeYTraceOne_centered_lpNorm_two_le_proved_allDimensions hN hdense
  have hmean := betaPrimeYTraceOne_integral_external hN (by omega : 2 * N + 2 ≤ K)
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

/-- The first central score belongs to `L^1`. -/
theorem concreteCentralLogScoreOne_memLp_one
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCentralLogScoreOne N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  letI : IsProbabilityMeasure
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hcentered := concreteCOETraceOne_centered_memLp_two hN hgap
  rw [show concreteCentralLogScoreOne N K = (2 : ℝ) •
      (fun A ↦ concreteCOETraceOne N K A -
        (N : ℝ) * ((N : ℝ) + 1)) by
    funext A
    simp [concreteCentralLogScoreOne]]
  exact (hcentered.mono_exponent (by norm_num)).const_smul 2

/-- The first central score has `L^1` norm `O(N)`. -/
theorem concreteCentralLogScoreOne_lpNorm_one_le
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCentralLogScoreOne N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      concreteCentralScoreOneConstant * (N : ℝ) := by
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
      denseClassicalMomentConstant * (N : ℝ) := by
    simpa only [centered, mu] using
      concreteCOETraceOne_centered_lpNorm_two_le hN hdense
  have hnormOne : lpNorm centered 1 mu ≤
      denseClassicalMomentConstant * (N : ℝ) :=
    (lpNorm_one_le_lpNorm_two_of_memLp hmem).trans hnormTwo
  rw [show concreteCentralLogScoreOne N K = (2 : ℝ) • centered by
    funext A
    simp [concreteCentralLogScoreOne, centered], lpNorm_const_smul]
  change |(2 : ℝ)| * lpNorm centered 1 mu ≤ _
  norm_num [concreteCentralScoreOneConstant]
  linarith

/-- The second central density score belongs to `L^1` in the dense range. -/
theorem concreteCentralDensityScoreTwo_memLp_one
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCentralDensityScoreTwo N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let centered : ConcreteMatrixState N → ℝ := fun A ↦
    concreteCOETraceOne N K A - (N : ℝ) * ((N : ℝ) + 1)
  let ellOne : ConcreteMatrixState N → ℝ := (2 : ℝ) • centered
  let ellTwo : ConcreteMatrixState N → ℝ := fun A ↦
    -8 * (concreteCOETraceOne N K A +
      concreteCOETraceTwo N K A / concreteCOEExponent N K)
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mu] using concreteCOETraceOne_centered_memLp_two hN hgap
  have hellOne : MemLp ellOne 2 mu := hcentered.const_smul 2
  have hTraceOne : MemLp (concreteCOETraceOne N K) 1 mu := by
    simpa only [mu] using concreteCOETraceOne_memLp_one_internal hN hgap
  have hTraceTwo : MemLp (concreteCOETraceTwo N K) 1 mu := by
    simpa only [mu] using concreteCOETraceTwo_memLp_one_internal hN hgap
  have hellTwo : MemLp ellTwo 1 mu := by
    rw [show ellTwo = (-8 : ℝ) •
        ((concreteCOETraceOne N K) +
          (1 / concreteCOEExponent N K : ℝ) •
            (concreteCOETraceTwo N K)) by
      funext A
      simp [ellTwo]
      ring]
    exact (hTraceOne.add (hTraceTwo.const_smul _)).const_smul _
  have hsq : MemLp (fun A ↦ ellOne A ^ 2) 1 mu := by
    simpa only [pow_two] using hellOne.mul' hellOne
  rw [show concreteCentralDensityScoreTwo N K =
      (fun A ↦ ellOne A ^ 2) + ellTwo by
    funext A
    simp [concreteCentralDensityScoreTwo, secondDensityBell,
      concreteCentralLogScoreOne, concreteCentralLogScoreTwo,
      ellOne, ellTwo, centered]]
  exact hsq.add hellTwo

/-- The second central density score has `L^1` norm `O(N^2)`.  The estimate
uses only the centered first-trace `L^2` bound and the five concrete primitive
trace-monomial inputs proved in `ConcreteTraceMomentTransfer`. -/
theorem concreteCentralDensityScoreTwo_lpNorm_one_le
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCentralDensityScoreTwo N K) 1
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) ≤
      concreteCentralScoreTwoConstant * (N : ℝ) ^ 2 := by
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
  have hc : (N : ℝ) ≤ concreteCOEExponent N K := by
    unfold concreteCOEExponent
    have hdenseR : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hdense
    nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
  have hcpos : 0 < concreteCOEExponent N K :=
    (by exact_mod_cast hN : (0 : ℝ) < N).trans_le hc
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mu] using concreteCOETraceOne_centered_memLp_two hN hgap
  have hcenteredNorm : lpNorm centered 2 mu ≤
      denseClassicalMomentConstant * (N : ℝ) := by
    simpa only [centered, mu] using
      concreteCOETraceOne_centered_lpNorm_two_le hN hdense
  have hellOne : MemLp ellOne 2 mu := hcentered.const_smul 2
  have hellOneNorm : lpNorm ellOne 2 mu ≤
      2 * denseClassicalMomentConstant * (N : ℝ) := by
    rw [show ellOne = (2 : ℝ) • centered by rfl, lpNorm_const_smul]
    change |(2 : ℝ)| * lpNorm centered 2 mu ≤ _
    norm_num
    linarith
  have hTraceOne : MemLp (concreteCOETraceOne N K) 1 mu := by
    simpa only [mu] using concreteCOETraceOne_memLp_one_internal hN hgap
  have hTraceTwo : MemLp (concreteCOETraceTwo N K) 1 mu := by
    simpa only [mu] using concreteCOETraceTwo_memLp_one_internal hN hgap
  have hTraceOneNorm : lpNorm (concreteCOETraceOne N K) 1 mu ≤
      derivedRawTraceOneConstant * (N : ℝ) ^ 2 := by
    simpa only [mu] using concreteCOETraceOne_lpNorm_one_le_internal hN hdense
  have hTraceTwoNorm : lpNorm (concreteCOETraceTwo N K) 1 mu ≤
      derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3 := by
    simpa only [mu] using concreteCOETraceTwo_lpNorm_one_le_internal hN hdense
  have hellTwo : MemLp ellTwo 1 mu := by
    rw [show ellTwo = (-8 : ℝ) •
        ((concreteCOETraceOne N K) +
          (1 / concreteCOEExponent N K : ℝ) •
            (concreteCOETraceTwo N K)) by
      funext A
      simp [ellTwo]
      ring]
    exact (hTraceOne.add (hTraceTwo.const_smul _)).const_smul _
  have hellTwoNorm : lpNorm ellTwo 1 mu ≤
      8 * (derivedRawTraceOneConstant + derivedPositiveRawTraceTwoConstant) *
        (N : ℝ) ^ 2 := by
    have hsum := lpNorm_add_le hTraceOne (p := (1 : ENNReal)) (by norm_num)
      (g := (1 / concreteCOEExponent N K : ℝ) • concreteCOETraceTwo N K)
    have hratio : (N : ℝ) / concreteCOEExponent N K ≤ 1 :=
      (div_le_one hcpos).2 hc
    have htwoScaled :
        lpNorm ((1 / concreteCOEExponent N K : ℝ) •
          concreteCOETraceTwo N K) 1 mu ≤
          derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 2 := by
      rw [lpNorm_const_smul]
      change |1 / concreteCOEExponent N K| *
          lpNorm (concreteCOETraceTwo N K) 1 mu ≤ _
      rw [abs_of_pos (one_div_pos.mpr hcpos)]
      calc
        (1 / concreteCOEExponent N K) *
            lpNorm (concreteCOETraceTwo N K) 1 mu ≤
          (1 / concreteCOEExponent N K) *
            (derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left hTraceTwoNorm (by positivity)
        _ = derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 2 *
            ((N : ℝ) / concreteCOEExponent N K) := by ring
        _ ≤ derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 2 := by
          calc
            derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 2 *
                ((N : ℝ) / concreteCOEExponent N K) ≤
              derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 2 * 1 :=
                mul_le_mul_of_nonneg_left hratio (by
                  exact mul_nonneg (by
                    norm_num [derivedPositiveRawTraceTwoConstant,
                      derivedRawTraceProductConstant,
                      denseClassicalMomentConstant]) (sq_nonneg _))
            _ = derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 2 := by ring
    have hsumNorm : lpNorm ((concreteCOETraceOne N K) +
        (1 / concreteCOEExponent N K : ℝ) •
          concreteCOETraceTwo N K) 1 mu ≤
        (derivedRawTraceOneConstant + derivedPositiveRawTraceTwoConstant) *
          (N : ℝ) ^ 2 := by
      calc
        _ ≤ lpNorm (concreteCOETraceOne N K) 1 mu +
            lpNorm ((1 / concreteCOEExponent N K : ℝ) •
              concreteCOETraceTwo N K) 1 mu := hsum
        _ ≤ derivedRawTraceOneConstant * (N : ℝ) ^ 2 +
            derivedPositiveRawTraceTwoConstant * (N : ℝ) ^ 2 :=
          add_le_add hTraceOneNorm htwoScaled
        _ = _ := by ring
    rw [show ellTwo = (-8 : ℝ) •
        ((concreteCOETraceOne N K) +
          (1 / concreteCOEExponent N K : ℝ) •
            (concreteCOETraceTwo N K)) by
      funext A
      simp [ellTwo]
      ring, lpNorm_const_smul]
    change |(-8 : ℝ)| * _ ≤ _
    norm_num
    have hmul : 8 * lpNorm ((concreteCOETraceOne N K) +
          (1 / concreteCOEExponent N K : ℝ) •
            concreteCOETraceTwo N K) 1 mu ≤
        8 * ((derivedRawTraceOneConstant + derivedPositiveRawTraceTwoConstant) *
          (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hsumNorm (by norm_num)
    calc
      8 * lpNorm ((concreteCOETraceOne N K) +
          (concreteCOEExponent N K)⁻¹ •
            concreteCOETraceTwo N K) 1 mu ≤
        8 * ((derivedRawTraceOneConstant + derivedPositiveRawTraceTwoConstant) *
          (N : ℝ) ^ 2) := by
          simpa only [one_div] using hmul
      _ = 8 * (derivedRawTraceOneConstant + derivedPositiveRawTraceTwoConstant) *
          (N : ℝ) ^ 2 := by ring
  have hsq : MemLp (fun A ↦ ellOne A * ellOne A) 1 mu :=
    hellOne.mul' hellOne
  have hsqNorm : lpNorm (fun A ↦ ellOne A ^ 2) 1 mu ≤
      4 * denseClassicalMomentConstant ^ 2 * (N : ℝ) ^ 2 := by
    have hholder := lpNorm_mul_le_lpNorm_two_mul hellOne hellOne
    have hpoint : (fun A ↦ ellOne A ^ 2) = fun A ↦ ellOne A * ellOne A := by
      funext A
      ring
    rw [hpoint]
    calc
      _ ≤ lpNorm ellOne 2 mu * lpNorm ellOne 2 mu := hholder
      _ ≤ (2 * denseClassicalMomentConstant * (N : ℝ)) *
          (2 * denseClassicalMomentConstant * (N : ℝ)) :=
        mul_le_mul hellOneNorm hellOneNorm lpNorm_nonneg (by
          exact mul_nonneg (mul_nonneg (by norm_num)
            (by norm_num [denseClassicalMomentConstant]))
            (by exact_mod_cast (Nat.zero_le N)))
      _ = _ := by ring
  have hpoint : concreteCentralDensityScoreTwo N K =
      (fun A ↦ ellOne A ^ 2) + ellTwo := by
    funext A
    simp only [concreteCentralDensityScoreTwo, secondDensityBell,
      Pi.add_apply]
    change concreteCentralLogScoreOne N K A ^ 2 +
        concreteCentralLogScoreTwo N K A = ellOne A ^ 2 + ellTwo A
    simp only [concreteCentralLogScoreOne, concreteCentralLogScoreTwo,
      ellOne, ellTwo, centered, Pi.smul_apply]
    simp only [smul_eq_mul]
  rw [hpoint]
  calc
    lpNorm ((fun A ↦ ellOne A ^ 2) + ellTwo) 1 mu ≤
        lpNorm (fun A ↦ ellOne A ^ 2) 1 mu + lpNorm ellTwo 1 mu :=
      lpNorm_add_le (by simpa [pow_two] using hsq) (by norm_num)
    _ ≤ 4 * denseClassicalMomentConstant ^ 2 * (N : ℝ) ^ 2 +
        8 * (derivedRawTraceOneConstant + derivedPositiveRawTraceTwoConstant) *
          (N : ℝ) ^ 2 :=
      add_le_add hsqNorm hellTwoNorm
    _ = concreteCentralScoreTwoConstant * (N : ℝ) ^ 2 := by
      simp only [concreteCentralScoreTwoConstant]
      ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
