import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H9ExactEndpointSteinProof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.SecondMomentEngine
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.Tactic

/-!
# Kernel-derived compatibility projections for the proved H9 package

The historical H9 declaration and its projections remain available for source
compatibility.  This module provides the same centered `L^2` consequences and
the raw first-trace packages, but derives them from the all-dimensional Stein
proof.  Downstream paper-facing modules can therefore be rewired without
changing any public theorem statement.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Centered `Tr Y` in `L^2`, derived from the proved all-dimensional H9
`L^3` package. -/
theorem betaPrimeYTraceOne_centered_two_momentPackage_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 2
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u -
          ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 2
            (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ)) := by
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  have hthree :=
    betaPrimeYTraceOne_centered_three_momentPackage_proved_allDimensions hN hgap
  constructor
  · exact hthree.1.mono_exponent (by norm_num)
  · intro hdense
    exact (U08.lpNorm_le_lpNorm_of_exponent_le_probability
      hthree.1 (by norm_num)).trans
      (hthree.2 hdense)

theorem betaPrimeYTraceOne_centered_memLp_two_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 2
      (betaPrimeTraceFourLaw N K) :=
  (betaPrimeYTraceOne_centered_two_momentPackage_proved_allDimensions
    hN hgap).1

theorem betaPrimeYTraceOne_centered_lpNorm_two_le_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun u ↦ betaPrimeYTraceOne N K u -
      ∫ z, betaPrimeYTraceOne N K z ∂(betaPrimeTraceFourLaw N K)) 2
        (betaPrimeTraceFourLaw N K) ≤
      denseClassicalMomentConstant * (N : ℝ) :=
  (betaPrimeYTraceOne_centered_two_momentPackage_proved_allDimensions
    hN (by omega)).2 hdense

/-- Raw first trace in `L^2`, from the proved centered package and the exact
mean. -/
theorem betaPrimeYTraceOne_memLp_two_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceOne N K) 2 (betaPrimeTraceFourLaw N K) := by
  let mu := betaPrimeTraceFourLaw N K
  let mean : ℝ := ∫ u, betaPrimeYTraceOne N K u ∂mu
  let centered : (Fin 4 → ℝ) → ℝ :=
    fun u ↦ betaPrimeYTraceOne N K u - mean
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mean, mu] using
      betaPrimeYTraceOne_centered_memLp_two_proved_allDimensions hN hgap
  have hconst : MemLp (fun _ : Fin 4 → ℝ ↦ mean) 2 mu := memLp_const mean
  rw [show betaPrimeYTraceOne N K =
      centered + (fun _ : Fin 4 → ℝ ↦ mean) by
    funext u
    simp [centered]]
  exact hcentered.add hconst

/-- Dense-regime raw first-trace `L^2` bound from the proved H9 package. -/
theorem betaPrimeYTraceOne_lpNorm_two_le_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceOne N K) 2 (betaPrimeTraceFourLaw N K) ≤
      derivedRawTraceOneConstant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := betaPrimeTraceFourLaw N K
  let mean : ℝ := ∫ u, betaPrimeYTraceOne N K u ∂mu
  let centered : (Fin 4 → ℝ) → ℝ :=
    fun u ↦ betaPrimeYTraceOne N K u - mean
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hcentered : MemLp centered 2 mu := by
    simpa only [centered, mean, mu] using
      betaPrimeYTraceOne_centered_memLp_two_proved_allDimensions hN hgap
  have hcenteredNorm : lpNorm centered 2 mu ≤
      denseClassicalMomentConstant * (N : ℝ) := by
    simpa only [centered, mean, mu] using
      betaPrimeYTraceOne_centered_lpNorm_two_le_proved_allDimensions hN hdense
  have htri := lpNorm_add_le hcentered (p := (2 : ENNReal)) (by norm_num)
    (g := fun _ : Fin 4 → ℝ ↦ mean)
  have hmean : mean = (N : ℝ) * ((N : ℝ) + 1) := by
    simpa only [mean, mu] using
      betaPrimeYTraceOne_integral_external hN (by omega)
  have hmeanNonneg : 0 ≤ mean := by rw [hmean]; positivity
  have hconstNorm : lpNorm (fun _ : Fin 4 → ℝ ↦ mean) 2 mu = mean := by
    rw [lpNorm_const (p := (2 : ENNReal)) (by norm_num)
      (IsProbabilityMeasure.ne_zero mu) mean]
    simp [Real.norm_eq_abs, abs_of_nonneg hmeanNonneg]
  rw [show betaPrimeYTraceOne N K =
      centered + (fun _ : Fin 4 → ℝ ↦ mean) by
    funext u
    simp [centered]]
  calc
    lpNorm (centered + (fun _ : Fin 4 → ℝ ↦ mean)) 2 mu ≤
        lpNorm centered 2 mu +
          lpNorm (fun _ : Fin 4 → ℝ ↦ mean) 2 mu := htri
    _ = lpNorm centered 2 mu + mean := by rw [hconstNorm]
    _ ≤ denseClassicalMomentConstant * (N : ℝ) +
        ((N : ℝ) * ((N : ℝ) + 1)) := by
      rw [hmean]
      exact add_le_add hcenteredNorm le_rfl
    _ ≤ derivedRawTraceOneConstant * (N : ℝ) ^ 2 := by
      have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      norm_num [derivedRawTraceOneConstant, denseClassicalMomentConstant] at ⊢
      nlinarith [sq_nonneg ((N : ℝ) - 1)]

theorem betaPrimeYTraceOne_memLp_one_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceOne N K) 1 (betaPrimeTraceFourLaw N K) := by
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  exact (betaPrimeYTraceOne_memLp_two_proved_allDimensions hN hgap).mono_exponent
    (by norm_num)

theorem betaPrimeYTraceOne_lpNorm_one_le_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceOne N K) 1 (betaPrimeTraceFourLaw N K) ≤
      derivedRawTraceOneConstant * (N : ℝ) ^ 2 := by
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  have htwo := betaPrimeYTraceOne_memLp_two_proved_allDimensions hN
    (by omega : 2 * N + 8 ≤ K)
  exact (U08.lpNorm_le_lpNorm_of_exponent_le_probability
    htwo (by norm_num)).trans
    (betaPrimeYTraceOne_lpNorm_two_le_proved_allDimensions hN hdense)

private theorem lpNorm_mul_le_lpNorm_two_mul_h9_rewire
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

theorem betaPrimeYTraceOneSquare_memLp_one_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u ^ 2) 1
      (betaPrimeTraceFourLaw N K) := by
  have htwo := betaPrimeYTraceOne_memLp_two_proved_allDimensions hN hgap
  simpa only [pow_two] using htwo.mul' htwo

theorem betaPrimeYTraceOneSquare_lpNorm_one_le_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun u ↦ betaPrimeYTraceOne N K u ^ 2) 1
        (betaPrimeTraceFourLaw N K) ≤
      derivedRawTraceProductConstant * (N : ℝ) ^ 4 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have htwo := betaPrimeYTraceOne_memLp_two_proved_allDimensions hN hgap
  have hnorm := betaPrimeYTraceOne_lpNorm_two_le_proved_allDimensions hN hdense
  have hbound : 0 ≤ derivedRawTraceOneConstant * (N : ℝ) ^ 2 := by
    norm_num [derivedRawTraceOneConstant, denseClassicalMomentConstant]
  calc
    lpNorm (fun u ↦ betaPrimeYTraceOne N K u ^ 2) 1
        (betaPrimeTraceFourLaw N K) ≤
      lpNorm (betaPrimeYTraceOne N K) 2 (betaPrimeTraceFourLaw N K) *
        lpNorm (betaPrimeYTraceOne N K) 2
          (betaPrimeTraceFourLaw N K) := by
        simpa only [pow_two] using
          lpNorm_mul_le_lpNorm_two_mul_h9_rewire htwo htwo
    _ ≤ (derivedRawTraceOneConstant * (N : ℝ) ^ 2) *
        (derivedRawTraceOneConstant * (N : ℝ) ^ 2) :=
      mul_le_mul hnorm hnorm lpNorm_nonneg hbound
    _ = derivedRawTraceProductConstant * (N : ℝ) ^ 4 := by
      simp [derivedRawTraceOneConstant, derivedRawTraceProductConstant]
      ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
