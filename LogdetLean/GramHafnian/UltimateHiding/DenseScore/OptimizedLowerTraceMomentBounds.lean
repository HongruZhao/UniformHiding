import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CubicTraceThreeRemainderBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_ProjectiveCancellationAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10_ExactCenteredVarianceClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9ExactEndpointSteinProof
import Mathlib.Tactic

/-!
# Optimized lower-trace moment bounds

This module keeps the exact H9 and H10 estimates that were deliberately
relaxed to the common `2^40` endpoint constant in the original compatibility
layer.  The resulting constants are used by the optimized cubic-remainder
certificate.

No new scientific interface is introduced here.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open U08

def optimizedCenteredTraceOneL3Constant : ℝ := 9216

def optimizedRawTraceOneL3Constant : ℝ := 9218

def optimizedRawTraceOneSquareConstant : ℝ :=
  optimizedRawTraceOneL3Constant ^ 2

def optimizedRawTraceOneCubeConstant : ℝ :=
  optimizedRawTraceOneL3Constant ^ 3

def optimizedCenteredTraceTwoL2Constant : ℝ := 8192

def optimizedRawTraceTwoL1Constant : ℝ := 20

def optimizedRawTraceTwoL2Constant : ℝ := 8212

def optimizedRawTraceOneTwoConstant : ℝ :=
  optimizedRawTraceOneL3Constant * optimizedRawTraceTwoL2Constant

/-! ## Sharp H9 source transport -/

/-- The literal H9 package with the exact source constants retained:
`1024 + 8192 = 9216`. -/
theorem betaPrimeYTraceOne_centered_three_momentPackage_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 3
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u -
          ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 3
            (betaPrimeTraceFourLaw N K) ≤
          optimizedCenteredTraceOneL3Constant * (N : ℝ)) := by
  let hinv : H9InverseWishartDenominatorPackage N K :=
    h9InverseWishartDenominatorPackage_internal_allDimensions hN hgap
  obtain ⟨hNumMem, hNumDense⟩ :=
    h9SourceNumeratorPackage_of_fixedGaussianWick hN hgap hinv
  obtain ⟨hDenMem, hDenDense⟩ :=
    h9SourceDenominatorPackage_internal hN hinv
  let mu := realBetaPrimeGaussianSourceLaw N K
  let g := h9BetaPrimeTraceOneFixedCenter N K
  let f := realBetaPrimeTracePowerVector 4 N K
  have hsourceFour : MemLp
      (h9SourceNumeratorFluctuation N K +
        h9SourceDenominatorFluctuation N K) 4 mu :=
    hNumMem.add hDenMem
  have hdecomp : g ∘ f =
      h9SourceNumeratorFluctuation N K +
        h9SourceDenominatorFluctuation N K := by
    simpa only [g, f] using h9BetaPrimeTraceOneFixedCenter_comp_source N K
  have hgMeas : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K) := by
    simpa [g] using
      (measurable_h9BetaPrimeTraceOneFixedCenter N K).aestronglyMeasurable
  have hfMeas : AEMeasurable f mu :=
    (measurable_realBetaPrimeTracePowerVector_external 4 N K).aemeasurable
  have hfixedFour : MemLp g 4 (betaPrimeTraceFourLaw N K) := by
    unfold betaPrimeTraceFourLaw
    refine (memLp_map_measure_iff ?_ hfMeas).2 ?_
    · exact hgMeas
    · rw [hdecomp]
      exact hsourceFour
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  have hfixedThree : MemLp g 3 (betaPrimeTraceFourLaw N K) :=
    hfixedFour.mono_exponent (by norm_num)
  have hmean :
      (∫ u, betaPrimeYTraceOne N K u ∂(betaPrimeTraceFourLaw N K)) =
        (N : ℝ) * ((N : ℝ) + 1) :=
    betaPrimeYTraceOne_integral_external hN (by omega)
  have hcenter :
      (fun u ↦ betaPrimeYTraceOne N K u -
        ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) =
        h9BetaPrimeTraceOneFixedCenter N K := by
    funext u
    rw [hmean]
    rfl
  constructor
  · rw [hcenter]
    simpa [g] using hfixedThree
  · intro hdense
    have hfourTriangle :
        lpNorm (h9SourceNumeratorFluctuation N K +
            h9SourceDenominatorFluctuation N K) 4 mu ≤
          lpNorm (h9SourceNumeratorFluctuation N K) 4 mu +
            lpNorm (h9SourceDenominatorFluctuation N K) 4 mu :=
      lpNorm_add_le hNumMem (by norm_num)
    have hfourBudget :
        lpNorm (h9SourceNumeratorFluctuation N K +
            h9SourceDenominatorFluctuation N K) 4 mu ≤
          optimizedCenteredTraceOneL3Constant * (N : ℝ) := by
      calc
        _ ≤ lpNorm (h9SourceNumeratorFluctuation N K) 4 mu +
              lpNorm (h9SourceDenominatorFluctuation N K) 4 mu :=
            hfourTriangle
        _ ≤ 1024 * (N : ℝ) + 8192 * (N : ℝ) :=
            add_le_add (hNumDense hdense) (hDenDense hdense)
        _ = optimizedCenteredTraceOneL3Constant * (N : ℝ) := by
          unfold optimizedCenteredTraceOneL3Constant
          ring
    have hmapNorm : lpNorm g 4 (betaPrimeTraceFourLaw N K) =
        lpNorm (h9SourceNumeratorFluctuation N K +
          h9SourceDenominatorFluctuation N K) 4 mu := by
      rw [← hdecomp]
      exact h9_lpNorm_source_map hgMeas
    have hfixedFourBound :
        lpNorm g 4 (betaPrimeTraceFourLaw N K) ≤
          optimizedCenteredTraceOneL3Constant * (N : ℝ) := by
      rw [hmapNorm]
      exact hfourBudget
    have hfixedThreeBound :
        lpNorm g 3 (betaPrimeTraceFourLaw N K) ≤
          optimizedCenteredTraceOneL3Constant * (N : ℝ) :=
      (h9_lpNorm_le_of_exponent_le hfixedFour (by norm_num)).trans
        hfixedFourBound
    rw [hcenter]
    simpa [g] using hfixedThreeBound

theorem betaPrimeYTraceOne_centered_lpNorm_three_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun u ↦ betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 3
        (betaPrimeTraceFourLaw N K) ≤
      optimizedCenteredTraceOneL3Constant * (N : ℝ) :=
  (betaPrimeYTraceOne_centered_three_momentPackage_optimized
    hN (by omega)).2 hdense

theorem betaPrimeYTraceOne_centered_lpNorm_two_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun u ↦ betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 2
        (betaPrimeTraceFourLaw N K) ≤
      optimizedCenteredTraceOneL3Constant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  have hthree :=
    (betaPrimeYTraceOne_centered_three_momentPackage_optimized hN hgap).1
  exact (U08.lpNorm_le_lpNorm_of_exponent_le_probability
    hthree (by norm_num)).trans
      (betaPrimeYTraceOne_centered_lpNorm_three_le_optimized hN hdense)

/-! ## Optimized raw first-trace moments -/

theorem betaPrimeYTraceOne_lpNorm_three_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceOne N K) 3 (betaPrimeTraceFourLaw N K) ≤
      optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  let mean : ℝ := ∫ u, betaPrimeYTraceOne N K u ∂mu
  let centered : (Fin 4 → ℝ) → ℝ :=
    fun u ↦ betaPrimeYTraceOne N K u - mean
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hcentered : MemLp centered 3 mu := by
    simpa only [centered, mean, mu] using
      (betaPrimeYTraceOne_centered_three_momentPackage_optimized hN hgap).1
  have hcenteredNorm : lpNorm centered 3 mu ≤
      optimizedCenteredTraceOneL3Constant * (N : ℝ) := by
    simpa only [centered, mean, mu] using
      betaPrimeYTraceOne_centered_lpNorm_three_le_optimized hN hdense
  have hmean : mean = (N : ℝ) * ((N : ℝ) + 1) := by
    simpa only [mean, mu] using
      betaPrimeYTraceOne_integral_external hN (by omega)
  have hmean0 : 0 ≤ mean := by rw [hmean]; positivity
  have hconstNorm : lpNorm (fun _ : Fin 4 → ℝ ↦ mean) 3 mu = mean := by
    rw [lpNorm_const (p := (3 : ENNReal)) (by norm_num)
      (IsProbabilityMeasure.ne_zero mu) mean]
    simp [Real.norm_eq_abs, abs_of_nonneg hmean0]
  have htri := lpNorm_add_le hcentered (p := (3 : ENNReal)) (by norm_num)
    (g := fun _ : Fin 4 → ℝ ↦ mean)
  rw [show betaPrimeYTraceOne N K =
      centered + (fun _ : Fin 4 → ℝ ↦ mean) by
    funext u
    simp [centered]]
  calc
    lpNorm (centered + (fun _ : Fin 4 → ℝ ↦ mean)) 3 mu ≤
        lpNorm centered 3 mu +
          lpNorm (fun _ : Fin 4 → ℝ ↦ mean) 3 mu := htri
    _ = lpNorm centered 3 mu + mean := by rw [hconstNorm]
    _ ≤ optimizedCenteredTraceOneL3Constant * (N : ℝ) +
        (N : ℝ) * ((N : ℝ) + 1) := by
      rw [hmean]
      exact add_le_add hcenteredNorm le_rfl
    _ ≤ optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
      have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := zero_le_one.trans hNr
      unfold optimizedCenteredTraceOneL3Constant
        optimizedRawTraceOneL3Constant
      nlinarith [mul_nonneg hN0 (sub_nonneg.mpr hNr)]

private theorem lpNorm_mul_le_lpNorm_two_mul_optimized
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f g : Omega → ℝ} (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    lpNorm (fun ω ↦ f ω * g ω) 1 mu ≤
      lpNorm f 2 mu * lpNorm g 2 mu := by
  have hprod : MemLp (fun ω ↦ f ω * g ω) 1 mu := hg.mul' hf
  have he : eLpNorm (fun ω ↦ f ω * g ω) 1 mu ≤
      eLpNorm f 2 mu * eLpNorm g 2 mu := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      hf.aestronglyMeasurable hg.aestronglyMeasurable
      (fun x y : ℝ ↦ x * y) 1 (by
        filter_upwards [] with ω
        simp [nnnorm_mul])
  rw [← toReal_eLpNorm hprod.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable,
    ← toReal_eLpNorm hg.aestronglyMeasurable,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) he

private theorem lpNorm_mul_le_of_holder_three_optimized
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p q s : ENNReal} {f g : Omega → ℝ}
    (hf : MemLp f q mu) (hg : MemLp g p mu)
    [ENNReal.HolderTriple p q s] :
    lpNorm (fun ω ↦ g ω * f ω) s mu ≤
      lpNorm g p mu * lpNorm f q mu := by
  have hprod : MemLp (fun ω ↦ g ω * f ω) s mu := hf.mul' hg
  have he : eLpNorm (fun ω ↦ g ω * f ω) s mu ≤
      eLpNorm g p mu * eLpNorm f q mu := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := p) (q := q) (r := s)
      hg.aestronglyMeasurable hf.aestronglyMeasurable
      (fun x y : ℝ ↦ x * y) 1 (by
        filter_upwards [] with ω
        simp [nnnorm_mul])
  rw [← toReal_eLpNorm hprod.aestronglyMeasurable,
    ← toReal_eLpNorm hg.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top hg.eLpNorm_ne_top hf.eLpNorm_ne_top) he

theorem betaPrimeYTraceOne_lpNorm_two_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceOne N K) 2 (betaPrimeTraceFourLaw N K) ≤
      optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  have hthree := betaPrimeYTraceOne_memLp_three_internal hN hgap
  exact (U08.lpNorm_le_lpNorm_of_exponent_le_probability
    hthree (by norm_num)).trans
      (betaPrimeYTraceOne_lpNorm_three_le_optimized hN hdense)

theorem betaPrimeYTraceOne_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceOne N K) 1 (betaPrimeTraceFourLaw N K) ≤
      optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  have hthree := betaPrimeYTraceOne_memLp_three_internal hN hgap
  exact (U08.lpNorm_le_lpNorm_of_exponent_le_probability
    hthree (by norm_num)).trans
      (betaPrimeYTraceOne_lpNorm_three_le_optimized hN hdense)

theorem betaPrimeYTraceOneSquare_momentPackage_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u ^ 2) 1
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u ^ 2) 1
            (betaPrimeTraceFourLaw N K) ≤
          optimizedRawTraceOneSquareConstant * (N : ℝ) ^ 4) := by
  have htwo := betaPrimeYTraceOne_memLp_two_proved_allDimensions hN hgap
  constructor
  · simpa only [pow_two] using htwo.mul' htwo
  · intro hdense
    have hnorm := betaPrimeYTraceOne_lpNorm_two_le_optimized hN hdense
    have hbound : 0 ≤ optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
      unfold optimizedRawTraceOneL3Constant
      positivity
    calc
      lpNorm (fun u ↦ betaPrimeYTraceOne N K u ^ 2) 1
          (betaPrimeTraceFourLaw N K) ≤
        lpNorm (betaPrimeYTraceOne N K) 2 (betaPrimeTraceFourLaw N K) *
          lpNorm (betaPrimeYTraceOne N K) 2
            (betaPrimeTraceFourLaw N K) := by
          simpa only [pow_two] using
            lpNorm_mul_le_lpNorm_two_mul_optimized htwo htwo
      _ ≤ (optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2) *
          (optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2) :=
        mul_le_mul hnorm hnorm lpNorm_nonneg hbound
      _ = optimizedRawTraceOneSquareConstant * (N : ℝ) ^ 4 := by
        unfold optimizedRawTraceOneSquareConstant
        ring

theorem betaPrimeYTraceOneCube_momentPackage_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u ^ 3) 1
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u ^ 3) 1
            (betaPrimeTraceFourLaw N K) ≤
          optimizedRawTraceOneCubeConstant * (N : ℝ) ^ 6) := by
  let mu := betaPrimeTraceFourLaw N K
  let f := betaPrimeYTraceOne N K
  have hf : MemLp f 3 mu := by
    simpa only [f, mu] using betaPrimeYTraceOne_memLp_three_internal hN hgap
  let p32 : ENNReal := ((3 / 2 : NNReal) : ENNReal)
  letI : ENNReal.HolderTriple 3 3 p32 := by
    have h : NNReal.HolderTriple 3 3 (3 / 2) := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((3 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal)
        ((3 / 2 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  have hsq : MemLp (fun u ↦ f u * f u) p32 mu := hf.mul' hf
  have hsqNorm : lpNorm (fun u ↦ f u * f u) p32 mu ≤
      lpNorm f 3 mu * lpNorm f 3 mu :=
    lpNorm_mul_le_of_holder_three_optimized hf hf
  letI : ENNReal.HolderTriple p32 3 1 := by
    have h : NNReal.HolderTriple (3 / 2) 3 1 := by
      rw [NNReal.holderTriple_iff]
      norm_num
    change ENNReal.HolderTriple
      ((3 / 2 : NNReal) : ENNReal) ((3 : NNReal) : ENNReal)
        ((1 : NNReal) : ENNReal)
    exact h.coe_ennreal (by norm_num)
  have hcube : MemLp (fun u ↦ (f u * f u) * f u) 1 mu := hf.mul' hsq
  constructor
  · convert hcube using 1
    funext u
    simp only [f]
    ring
  · intro hdense
    have hfNorm : lpNorm f 3 mu ≤
        optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
      simpa only [f, mu] using
        betaPrimeYTraceOne_lpNorm_three_le_optimized hN hdense
    have hbound0 :
        0 ≤ optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2 := by
      unfold optimizedRawTraceOneL3Constant
      positivity
    change lpNorm (fun u ↦ f u ^ 3) 1 mu ≤ _
    calc
      lpNorm (fun u ↦ f u ^ 3) 1 mu =
          lpNorm (fun u ↦ (f u * f u) * f u) 1 mu := by
        congr 1
        funext u
        ring
      _ ≤ lpNorm (fun u ↦ f u * f u) p32 mu * lpNorm f 3 mu :=
        lpNorm_mul_le_of_holder_three_optimized hf hsq
      _ ≤ (lpNorm f 3 mu * lpNorm f 3 mu) * lpNorm f 3 mu := by
        exact mul_le_mul_of_nonneg_right hsqNorm lpNorm_nonneg
      _ ≤ ((optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2) *
            (optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2)) *
          (optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2) := by
        exact mul_le_mul
          (mul_le_mul hfNorm hfNorm lpNorm_nonneg hbound0)
          hfNorm lpNorm_nonneg (mul_nonneg hbound0 hbound0)
      _ = optimizedRawTraceOneCubeConstant * (N : ℝ) ^ 6 := by
        unfold optimizedRawTraceOneCubeConstant
        ring

/-! ## Optimized H10 and raw second-trace moments -/

theorem betaPrimeYTraceTwo_centered_two_momentPackage_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
        (fun u ↦ betaPrimeYTraceTwo N K u -
          ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm
            (fun u ↦ betaPrimeYTraceTwo N K u -
              ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
            2 (betaPrimeTraceFourLaw N K) ≤
          optimizedCenteredTraceTwoL2Constant * (N : ℝ) ^ 2) := by
  have hCore :=
    U08.betaPrimeYTraceTwo_centered_memLp_two_and_lpNorm_eq_sqrt_internal
      hgap (U08.h14FiniteGaussianFourthWickFormula_internal N K)
  refine ⟨hCore.1, ?_⟩
  intro hdense
  rw [hCore.2]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by unfold optimizedCenteredTraceTwoL2Constant; positivity, ?_⟩
  rw [U08.h10DenominatorCenteredVariance_eq_traceRecurrence_internal hN hdense]
  calc
    _ ≤ (2 : ℝ) ^ 26 * (N : ℝ) ^ 4 :=
      U08.h10_traceRecurrenceVariance_le_twoPow26_dense
        (U08.h8H10ExactTraceRecurrenceSystem_internal hN hdense)
        (by exact_mod_cast hN)
        (U08.thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense)
    _ = (optimizedCenteredTraceTwoL2Constant * (N : ℝ) ^ 2) ^ 2 := by
      unfold optimizedCenteredTraceTwoL2Constant
      ring

theorem betaPrimeYTraceOneSquare_centered_two_momentPackage_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
        (fun u ↦ betaPrimeYTraceOne N K u ^ 2 -
          ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm
            (fun u ↦ betaPrimeYTraceOne N K u ^ 2 -
              ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
            2 (betaPrimeTraceFourLaw N K) ≤
          optimizedCenteredTraceTwoL2Constant * (N : ℝ) ^ 3) := by
  have hCore :=
    U08.betaPrimeYTraceOneSquare_centered_memLp_two_and_lpNorm_eq_sqrt_internal
      hgap (U08.h14FiniteGaussianFourthWickFormula_internal N K)
  refine ⟨hCore.1, ?_⟩
  intro hdense
  rw [hCore.2]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by unfold optimizedCenteredTraceTwoL2Constant; positivity, ?_⟩
  rw [U08.h8DenominatorCenteredVariance_eq_traceRecurrence_internal hN hdense]
  calc
    _ ≤ (2 : ℝ) ^ 26 * (N : ℝ) ^ 6 :=
      U08.h8_traceRecurrenceVariance_le_twoPow26_dense
        (U08.h8H10ExactTraceRecurrenceSystem_internal hN hdense)
        (by exact_mod_cast hN)
        (U08.thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense)
    _ = (optimizedCenteredTraceTwoL2Constant * (N : ℝ) ^ 3) ^ 2 := by
      unfold optimizedCenteredTraceTwoL2Constant
      ring

theorem betaPrimeYTraceTwo_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceTwo N K) 1 (betaPrimeTraceFourLaw N K) ≤
      optimizedRawTraceTwoL1Constant * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hmem := betaPrimeYTraceTwo_memLp_one_positive_internal hN hgap
  rw [lpNorm_one_eq_integral_norm hmem.aestronglyMeasurable]
  calc
    (∫ u, ‖betaPrimeYTraceTwo N K u‖ ∂betaPrimeTraceFourLaw N K) =
        ∫ u, betaPrimeYTraceTwo N K u ∂betaPrimeTraceFourLaw N K := by
      apply integral_congr_ae
      filter_upwards
        [betaPrimeYTraceTwo_nonneg_le_traceOne_sq_ae_internal hN hgap]
          with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg hu.1]
    _ = U08.betaPrimeYTraceTwoFormalMeanU08 N K := rfl
    _ ≤ |U08.betaPrimeYTraceTwoFormalMeanU08 N K| := le_abs_self _
    _ ≤ optimizedRawTraceTwoL1Constant * (N : ℝ) ^ 3 := by
      simpa only [optimizedRawTraceTwoL1Constant] using
        h14_betaPrimeYTraceTwoFormalMeanU08_abs_le_twenty_cube_internal
          hN hdense

theorem betaPrimeYTraceTwo_memLp_two_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceTwo N K) 2 (betaPrimeTraceFourLaw N K) := by
  let mu := betaPrimeTraceFourLaw N K
  let mean : ℝ := ∫ u, betaPrimeYTraceTwo N K u ∂mu
  let centered : (Fin 4 → ℝ) → ℝ :=
    fun u ↦ betaPrimeYTraceTwo N K u - mean
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mean, mu] using
      (betaPrimeYTraceTwo_centered_two_momentPackage_optimized hN hgap).1
  rw [show betaPrimeYTraceTwo N K =
      centered + (fun _ : Fin 4 → ℝ ↦ mean) by
    funext u
    simp [centered]]
  exact hcentered.add (memLp_const mean)

theorem betaPrimeYTraceTwo_lpNorm_two_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceTwo N K) 2 (betaPrimeTraceFourLaw N K) ≤
      optimizedRawTraceTwoL2Constant * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  let mean : ℝ := ∫ u, betaPrimeYTraceTwo N K u ∂mu
  let centered : (Fin 4 → ℝ) → ℝ :=
    fun u ↦ betaPrimeYTraceTwo N K u - mean
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mean, mu] using
      (betaPrimeYTraceTwo_centered_two_momentPackage_optimized hN hgap).1
  have hcenteredNorm : lpNorm centered 2 mu ≤
      optimizedCenteredTraceTwoL2Constant * (N : ℝ) ^ 2 := by
    simpa only [centered, mean, mu] using
      (betaPrimeYTraceTwo_centered_two_momentPackage_optimized hN hgap).2 hdense
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
    _ ≤ optimizedCenteredTraceTwoL2Constant * (N : ℝ) ^ 2 +
        optimizedRawTraceTwoL1Constant * (N : ℝ) ^ 3 :=
      add_le_add hcenteredNorm hmeanAbs
    _ ≤ optimizedRawTraceTwoL2Constant * (N : ℝ) ^ 3 := by
      have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hN0 : (0 : ℝ) ≤ (N : ℝ) := zero_le_one.trans hNr
      unfold optimizedCenteredTraceTwoL2Constant
        optimizedRawTraceTwoL1Constant optimizedRawTraceTwoL2Constant
      nlinarith [mul_nonneg (sq_nonneg (N : ℝ)) (sub_nonneg.mpr hNr)]

theorem betaPrimeYTraceOneTwo_momentPackage_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u * betaPrimeYTraceTwo N K u) 1
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u *
          betaPrimeYTraceTwo N K u) 1 (betaPrimeTraceFourLaw N K) ≤
          optimizedRawTraceOneTwoConstant * (N : ℝ) ^ 5) := by
  have hone := betaPrimeYTraceOne_memLp_two_proved_allDimensions hN hgap
  have htwo := betaPrimeYTraceTwo_memLp_two_optimized hN hgap
  constructor
  · exact htwo.mul' hone
  · intro hdense
    have honeNorm := betaPrimeYTraceOne_lpNorm_two_le_optimized hN hdense
    have htwoNorm := betaPrimeYTraceTwo_lpNorm_two_le_optimized hN hdense
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
        lpNorm_mul_le_lpNorm_two_mul_optimized hone htwo
      _ ≤ (optimizedRawTraceOneL3Constant * (N : ℝ) ^ 2) *
          (optimizedRawTraceTwoL2Constant * (N : ℝ) ^ 3) :=
        mul_le_mul honeNorm htwoNorm lpNorm_nonneg hOneNonneg
      _ = optimizedRawTraceOneTwoConstant * (N : ℝ) ^ 5 := by
        unfold optimizedRawTraceOneTwoConstant
        ring

#print axioms betaPrimeYTraceOne_centered_three_momentPackage_optimized
#print axioms betaPrimeYTraceOneCube_momentPackage_optimized
#print axioms betaPrimeYTraceTwo_centered_two_momentPackage_optimized
#print axioms betaPrimeYTraceOneSquare_centered_two_momentPackage_optimized
#print axioms betaPrimeYTraceTwo_lpNorm_one_le_optimized
#print axioms betaPrimeYTraceOneTwo_momentPackage_optimized

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
