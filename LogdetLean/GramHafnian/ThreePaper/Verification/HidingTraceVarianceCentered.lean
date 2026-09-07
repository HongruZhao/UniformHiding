import LogdetLean.GramHafnian.UltimateHiding.DenseScore.UltraNGeTwoRawMomentBounds
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CubicTraceThreeRemainderBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCenteredMatrixMomentExternal

/-!
# Isolated verification of the printed centered S moments

For the literal `S = Y - (N+1) I`, this file gives the three orders in
`eq:hide-S-moments`, with the printed hypotheses `2 ≤ N` and `16*N ≤ K`.
The constants are explicit and independent of both parameters.  Integrability
is part of every package.  No theorem below assumes a moment or score bound
as an extra hypothesis.  This module is not imported by any public endpoint.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.ThreePaper.Verification

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

private theorem centeredOne_eq_centeredMean
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    betaPrimeCenteredMatrixTraceOne N K =
      fun u ↦ betaPrimeYTraceOne N K u -
        ∫ z, betaPrimeYTraceOne N K z ∂betaPrimeTraceFourLaw N K := by
  funext u
  rw [betaPrimeYTraceOne_integral_external (by omega : 1 ≤ N) (by omega)]
  rfl

theorem hiding_S_traceOne_betaPrime
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (betaPrimeCenteredMatrixTraceOne N K) 3 (betaPrimeTraceFourLaw N K) ∧
      lpNorm (betaPrimeCenteredMatrixTraceOne N K) 3 (betaPrimeTraceFourLaw N K) ≤
        denseClassicalMomentConstant * (N : ℝ) := by
  rw [centeredOne_eq_centeredMean hN hdense]
  exact ⟨betaPrimeYTraceOne_centered_memLp_three_proved_allDimensions
      (by omega) (by omega),
    betaPrimeYTraceOne_centered_lpNorm_three_le_proved_allDimensions
      (by omega) hdense⟩

theorem hiding_S_traceTwo_betaPrime
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (betaPrimeCenteredMatrixTraceTwo N K) (3 / 2) (betaPrimeTraceFourLaw N K) ∧
      lpNorm (betaPrimeCenteredMatrixTraceTwo N K) (3 / 2)
          (betaPrimeTraceFourLaw N K) ≤ 30 * (N : ℝ) ^ 3 := by
  let mu := betaPrimeTraceFourLaw N K
  let n : ℝ := N
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : 0 ≤ n := by linarith
  have hgap : 2 * N + 8 ≤ K := by omega
  have h1 : MemLp (betaPrimeYTraceOne N K) 2 mu :=
    (betaPrimeYTraceOne_four_momentPackage_ultraNGeTwo hN hgap).1.mono_exponent
      (by norm_num)
  have h2 : MemLp (betaPrimeYTraceTwo N K) 2 mu :=
    (betaPrimeYTraceTwo_two_momentPackage_ultraNGeTwo hN hgap).1
  have hm1 : lpNorm (betaPrimeYTraceOne N K) 2 mu ≤ 3 * n ^ 2 := by
    calc
      _ ≤ ultraNGeTwoRawTraceOneL4Constant * n ^ 2 :=
        betaPrimeYTraceOne_lpNorm_two_le_ultraNGeTwo hN hdense
      _ ≤ _ := by
        unfold ultraNGeTwoRawTraceOneL4Constant
        nlinarith [sq_nonneg n]
  have hm2 : lpNorm (betaPrimeYTraceTwo N K) 2 mu ≤ 10 * n ^ 3 := by
    calc
      _ ≤ ultraNGeTwoRawTraceTwoL2Constant * n ^ 3 :=
        (betaPrimeYTraceTwo_two_momentPackage_ultraNGeTwo hN hgap).2 hdense
      _ ≤ _ := by
        unfold ultraNGeTwoRawTraceTwoL2Constant
        nlinarith [pow_nonneg (by linarith : 0 ≤ n) 3]
  let f := betaPrimeYTraceTwo N K -
    (fun u ↦ 2 * (n + 1) * betaPrimeYTraceOne N K u)
  let g : (Fin 4 → ℝ) → ℝ := fun _ ↦ n * (n + 1) ^ 2
  have hf : MemLp f 2 mu := h2.sub (h1.const_mul _)
  have hg : MemLp g 2 mu := memLp_const _
  have heq : betaPrimeCenteredMatrixTraceTwo N K = f + g := rfl
  have hmem : MemLp (betaPrimeCenteredMatrixTraceTwo N K) 2 mu := by
    rw [heq]
    exact hf.add hg
  have hnorm : lpNorm (betaPrimeCenteredMatrixTraceTwo N K) 2 mu ≤ 30 * n ^ 3 := by
    rw [heq]
    have htri := lpNorm_add_le hf (p := (2 : ENNReal)) (by norm_num) (g := g)
    have hsub := lpNorm_sub_le h2 (p := (2 : ENNReal)) (by norm_num)
      (g := fun u ↦ 2 * (n + 1) * betaPrimeYTraceOne N K u)
    have hscale : lpNorm (fun u ↦ 2 * (n + 1) * betaPrimeYTraceOne N K u) 2 mu =
        2 * (n + 1) * lpNorm (betaPrimeYTraceOne N K) 2 mu := by
      change lpNorm ((2 * (n + 1)) • betaPrimeYTraceOne N K) 2 mu = _
      rw [lpNorm_const_smul]
      change ‖2 * (n + 1)‖ * _ = _
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * (n + 1))]
    have hconst : lpNorm g 2 mu = n * (n + 1) ^ 2 := by
      dsimp [g]
      rw [lpNorm_const (p := (2 : ENNReal)) (by norm_num)
        (IsProbabilityMeasure.ne_zero mu)]
      simp [Real.norm_eq_abs, abs_of_nonneg hn0]
    rw [hscale] at hsub
    rw [hconst] at htri
    have hscaleBound := mul_le_mul_of_nonneg_left hm1
      (by positivity : 0 ≤ 2 * (n + 1))
    change lpNorm f 2 mu ≤ _ at hsub
    nlinarith [sq_nonneg (n - 1), mul_nonneg (by linarith : 0 ≤ n - 1)
      (by positivity : 0 ≤ n ^ 2)]
  have hexp : (3 / 2 : ENNReal) ≤ 2 := by
    rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
    norm_num
  exact ⟨hmem.mono_exponent hexp,
    (U08.lpNorm_le_lpNorm_of_exponent_le_probability hmem hexp).trans hnorm⟩

theorem hiding_S_traceThree_betaPrime
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (betaPrimeCenteredMatrixTraceThree N K) 1 (betaPrimeTraceFourLaw N K) ∧
      lpNorm (betaPrimeCenteredMatrixTraceThree N K) 1 (betaPrimeTraceFourLaw N K) ≤
        (derivedRawTraceThreeConstant + 64) * (N : ℝ) ^ 4 := by
  let mu := betaPrimeTraceFourLaw N K
  let n : ℝ := N
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ N by omega)
  have hn0 : 0 ≤ n := by linarith
  have hgap : 2 * N + 8 ≤ K := by omega
  have h1 : MemLp (betaPrimeYTraceOne N K) 1 mu :=
    (betaPrimeYTraceOne_four_momentPackage_ultraNGeTwo hN hgap).1.mono_exponent
      (by norm_num)
  have h2 : MemLp (betaPrimeYTraceTwo N K) 1 mu :=
    (betaPrimeYTraceTwo_two_momentPackage_ultraNGeTwo hN hgap).1.mono_exponent
      (by norm_num)
  have h3 : MemLp (betaPrimeYTraceThree N K) 1 mu :=
    betaPrimeYTraceThree_memLp_one_internal (by omega) hgap
  have hm1 : lpNorm (betaPrimeYTraceOne N K) 1 mu ≤ 2 * n ^ 2 := by
    calc
      _ ≤ ultraNGeTwoRawTraceOneL1Constant * n ^ 2 :=
        betaPrimeYTraceOne_lpNorm_one_le_ultraNGeTwo hN hdense
      _ ≤ _ := by unfold ultraNGeTwoRawTraceOneL1Constant; nlinarith [sq_nonneg n]
  have hm2 : lpNorm (betaPrimeYTraceTwo N K) 1 mu ≤ 5 * n ^ 3 := by
    calc
      _ ≤ ultraNGeTwoRawTraceTwoL1Constant * n ^ 3 :=
        betaPrimeYTraceTwo_lpNorm_one_le_ultraNGeTwo hN hdense
      _ ≤ _ := by
        unfold ultraNGeTwoRawTraceTwoL1Constant
        nlinarith [pow_nonneg (by linarith : 0 ≤ n) 3]
  have hm3 := betaPrimeYTraceThree_lpNorm_one_le_internal (N := N) (K := K)
    (by omega) hdense
  let f := betaPrimeYTraceThree N K -
    (fun u ↦ 3 * (n + 1) * betaPrimeYTraceTwo N K u)
  let g : (Fin 4 → ℝ) → ℝ := fun u ↦
    3 * (n + 1) ^ 2 * betaPrimeYTraceOne N K u
  let a : (Fin 4 → ℝ) → ℝ := fun _ ↦ n * (n + 1) ^ 3
  have hf : MemLp f 1 mu := h3.sub (h2.const_mul _)
  have hg : MemLp g 1 mu := h1.const_mul _
  have ha : MemLp a 1 mu := memLp_const _
  have heq : betaPrimeCenteredMatrixTraceThree N K = f + g - a := rfl
  have hmem : MemLp (betaPrimeCenteredMatrixTraceThree N K) 1 mu := by
    rw [heq]; exact (hf.add hg).sub ha
  refine ⟨hmem, ?_⟩
  rw [heq]
  have ht1 := lpNorm_sub_le h3 (p := (1 : ENNReal)) (by norm_num)
    (g := fun u ↦ 3 * (n + 1) * betaPrimeYTraceTwo N K u)
  have ht2 := lpNorm_add_le hf (p := (1 : ENNReal)) (by norm_num) (g := g)
  have ht3 := lpNorm_sub_le (hf.add hg) (p := (1 : ENNReal)) (by norm_num) (g := a)
  have hs2 : lpNorm (fun u ↦ 3 * (n + 1) * betaPrimeYTraceTwo N K u) 1 mu =
      3 * (n + 1) * lpNorm (betaPrimeYTraceTwo N K) 1 mu := by
    change lpNorm ((3 * (n + 1)) • betaPrimeYTraceTwo N K) 1 mu = _
    rw [lpNorm_const_smul]
    change ‖3 * (n + 1)‖ * _ = _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 3 * (n + 1))]
  have hs1 : lpNorm g 1 mu = 3 * (n + 1) ^ 2 * lpNorm (betaPrimeYTraceOne N K) 1 mu := by
    dsimp [g]
    change lpNorm ((3 * (n + 1) ^ 2) • betaPrimeYTraceOne N K) 1 mu = _
    rw [lpNorm_const_smul]
    change ‖3 * (n + 1) ^ 2‖ * _ = _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 3 * (n + 1) ^ 2)]
  have hc : lpNorm a 1 mu = n * (n + 1) ^ 3 := by
    dsimp [a]
    rw [lpNorm_const (p := (1 : ENNReal)) (by norm_num) (IsProbabilityMeasure.ne_zero mu)]
    simp [Real.norm_eq_abs, abs_of_nonneg hn0, abs_of_nonneg (by linarith : 0 ≤ n + 1)]
  rw [hs2] at ht1
  rw [hs1] at ht2
  rw [hc] at ht3
  change lpNorm f 1 mu ≤ _ at ht1
  have hscale1 := mul_le_mul_of_nonneg_left hm1 (by positivity : 0 ≤ 3 * (n + 1) ^ 2)
  have hscale2 := mul_le_mul_of_nonneg_left hm2 (by positivity : 0 ≤ 3 * (n + 1))
  change lpNorm (betaPrimeYTraceThree N K) 1 mu ≤ derivedRawTraceThreeConstant * n ^ 4 at hm3
  change lpNorm (f + g - a) 1 mu ≤ (derivedRawTraceThreeConstant + 64) * n ^ 4
  have hnpow : n ≤ n ^ 2 := by nlinarith
  have hnpow2 : n ^ 2 ≤ n ^ 3 := by
    nlinarith [mul_nonneg (show 0 ≤ n - 1 by linarith) (sq_nonneg n)]
  have hnpow3 : n ^ 3 ≤ n ^ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ n - 1 by linarith) (pow_nonneg hn0 3)]
  nlinarith

private theorem centeredOne_comp (N K : ℕ) :
    betaPrimeCenteredMatrixTraceOne N K ∘ concreteCOETracePowerVector 4 N K =
      concreteCOECenteredMatrixTraceOne N K := by
  funext A
  change concreteBetaPrimeYTraceOne N K A - (N : ℝ) * ((N : ℝ) + 1) = _
  simp only [concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne,
    concreteCOECenteredMatrixTraceOne]

private theorem centeredTwo_comp (N K : ℕ) :
    betaPrimeCenteredMatrixTraceTwo N K ∘ concreteCOETracePowerVector 4 N K =
      concreteCOECenteredMatrixTraceTwo N K := by
  funext A
  change concreteBetaPrimeYTraceTwo N K A -
    2 * ((N : ℝ) + 1) * concreteBetaPrimeYTraceOne N K A +
    (N : ℝ) * ((N : ℝ) + 1) ^ 2 = _
  simp only [concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne,
    concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo, concreteCOECenteredMatrixTraceTwo]

private theorem centeredThree_comp (N K : ℕ) :
    betaPrimeCenteredMatrixTraceThree N K ∘ concreteCOETracePowerVector 4 N K =
      concreteCOECenteredMatrixTraceThree N K := by
  funext A
  change concreteBetaPrimeYTraceThree N K A -
    3 * ((N : ℝ) + 1) * concreteBetaPrimeYTraceTwo N K A +
    3 * ((N : ℝ) + 1) ^ 2 * concreteBetaPrimeYTraceOne N K A -
    (N : ℝ) * ((N : ℝ) + 1) ^ 3 = _
  simp only [concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne,
    concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo,
    concreteBetaPrimeYTraceThree_eq_concreteCOETraceThree, concreteCOECenteredMatrixTraceThree]

theorem hiding_S_traceOne_concrete
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCOECenteredMatrixTraceOne N K) 3
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ∧
      lpNorm (concreteCOECenteredMatrixTraceOne N K) 3
          (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ≤
        denseClassicalMomentConstant * (N : ℝ) := by
  obtain ⟨hm, hb⟩ := hiding_S_traceOne_betaPrime hN hdense
  have hpull := memLp_comp_concreteCOETracePowerVector (by omega : 1 ≤ N) (by omega) hm
  have hnorm := lpNorm_comp_concreteCOETracePowerVector (by omega : 1 ≤ N)
    (by omega) (p := (3 : ENNReal)) hm.aestronglyMeasurable
  rw [centeredOne_comp] at hpull hnorm
  exact ⟨hpull, hnorm.le.trans hb⟩

theorem hiding_S_traceTwo_concrete
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCOECenteredMatrixTraceTwo N K) (3 / 2)
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ∧
      lpNorm (concreteCOECenteredMatrixTraceTwo N K) (3 / 2)
          (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ≤
        30 * (N : ℝ) ^ 3 := by
  obtain ⟨hm, hb⟩ := hiding_S_traceTwo_betaPrime hN hdense
  have hpull := memLp_comp_concreteCOETracePowerVector (by omega : 1 ≤ N) (by omega) hm
  have hnorm := lpNorm_comp_concreteCOETracePowerVector (by omega : 1 ≤ N)
    (by omega) (p := (3 / 2 : ENNReal)) hm.aestronglyMeasurable
  rw [centeredTwo_comp] at hpull hnorm
  exact ⟨hpull, hnorm.le.trans hb⟩

theorem hiding_S_traceThree_concrete
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCOECenteredMatrixTraceThree N K) 1
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ∧
      lpNorm (concreteCOECenteredMatrixTraceThree N K) 1
          (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ≤
        (derivedRawTraceThreeConstant + 64) * (N : ℝ) ^ 4 := by
  obtain ⟨hm, hb⟩ := hiding_S_traceThree_betaPrime hN hdense
  have hpull := memLp_comp_concreteCOETracePowerVector (by omega : 1 ≤ N) (by omega) hm
  have hnorm := lpNorm_comp_concreteCOETracePowerVector (by omega : 1 ≤ N)
    (by omega) (p := (1 : ENNReal)) hm.aestronglyMeasurable
  rw [centeredThree_comp] at hpull hnorm
  exact ⟨hpull, hnorm.le.trans hb⟩

/-- The three literal matrix traces from the printed `eq:hide-S-moments`.
`concreteCOECenteredMatrix` is exactly `cZ-(N+1)I`; the traces are real on
the COE support, and these real parts agree pointwise with the scalar
centered trace coordinates.  Each bound above separately proves `MemLp`. -/
theorem hiding_S_moments_literal
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun A ↦ (Matrix.trace (concreteCOECenteredMatrix N K A)).re) 3
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ≤
      denseClassicalMomentConstant * (N : ℝ) ∧
    lpNorm (fun A ↦ (Matrix.trace
      (concreteCOECenteredMatrix N K A * concreteCOECenteredMatrix N K A)).re) (3 / 2)
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ≤
      30 * (N : ℝ) ^ 3 ∧
    lpNorm (fun A ↦ (Matrix.trace
      (concreteCOECenteredMatrix N K A * concreteCOECenteredMatrix N K A *
        concreteCOECenteredMatrix N K A)).re) 1
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ≤
      (derivedRawTraceThreeConstant + 64) * (N : ℝ) ^ 4 := by
  simp_rw [concreteCOECenteredMatrix_trace_re, concreteCOECenteredMatrix_sq_trace_re,
    concreteCOECenteredMatrix_cube_trace_re]
  exact ⟨(hiding_S_traceOne_concrete hN hdense).2,
    (hiding_S_traceTwo_concrete hN hdense).2, (hiding_S_traceThree_concrete hN hdense).2⟩

/-- Finiteness for the actual matrix traces, not just their polynomial
coordinates.  This rules out relying on the totalized value of `lpNorm`
for a nonintegrable observable. -/
theorem hiding_S_moments_literal_memLp
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (fun A ↦ (Matrix.trace (concreteCOECenteredMatrix N K A)).re) 3
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ∧
    MemLp (fun A ↦ (Matrix.trace
      (concreteCOECenteredMatrix N K A * concreteCOECenteredMatrix N K A)).re) (3 / 2)
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ∧
    MemLp (fun A ↦ (Matrix.trace
      (concreteCOECenteredMatrix N K A * concreteCOECenteredMatrix N K A *
        concreteCOECenteredMatrix N K A)).re) 1
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) := by
  simp_rw [concreteCOECenteredMatrix_trace_re, concreteCOECenteredMatrix_sq_trace_re,
    concreteCOECenteredMatrix_cube_trace_re]
  exact ⟨(hiding_S_traceOne_concrete hN hdense).1,
    (hiding_S_traceTwo_concrete hN hdense).1, (hiding_S_traceThree_concrete hN hdense).1⟩

/-- One universal constant for all three printed S-moment bounds. -/
def hidingSMomentConstant : ℝ :=
  max denseClassicalMomentConstant (max 30 (derivedRawTraceThreeConstant + 64))

theorem hidingSMomentConstant_pos : 0 < hidingSMomentConstant := by
  exact lt_of_lt_of_le (by norm_num [denseClassicalMomentConstant]) (le_max_left _ _)

/-- The printed common-C statement on actual matrix traces, with no
parameter-dependent constant and no additional hypothesis. -/
theorem hiding_S_moments_literal_commonConstant
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun A ↦ (Matrix.trace (concreteCOECenteredMatrix N K A)).re) 3
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ≤
      hidingSMomentConstant * (N : ℝ) ∧
    lpNorm (fun A ↦ (Matrix.trace
      (concreteCOECenteredMatrix N K A * concreteCOECenteredMatrix N K A)).re) (3 / 2)
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ≤
      hidingSMomentConstant * (N : ℝ) ^ 3 ∧
    lpNorm (fun A ↦ (Matrix.trace
      (concreteCOECenteredMatrix N K A * concreteCOECenteredMatrix N K A *
        concreteCOECenteredMatrix N K A)).re) 1
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K) ≤
      hidingSMomentConstant * (N : ℝ) ^ 4 := by
  obtain ⟨h1, h2, h3⟩ := hiding_S_moments_literal hN hdense
  have hC1 : denseClassicalMomentConstant ≤ hidingSMomentConstant := le_max_left _ _
  have hC2 : 30 ≤ hidingSMomentConstant := (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : derivedRawTraceThreeConstant + 64 ≤ hidingSMomentConstant :=
    (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right hC1 (by positivity)),
    h2.trans (mul_le_mul_of_nonneg_right hC2 (by positivity)),
    h3.trans (mul_le_mul_of_nonneg_right hC3 (by positivity))⟩

#print axioms hiding_S_traceOne_betaPrime
#print axioms hiding_S_traceTwo_betaPrime
#print axioms hiding_S_traceThree_betaPrime
#print axioms hiding_S_traceOne_concrete
#print axioms hiding_S_traceTwo_concrete
#print axioms hiding_S_traceThree_concrete
#print axioms hiding_S_moments_literal
#print axioms hiding_S_moments_literal_memLp
#print axioms hiding_S_moments_literal_commonConstant

end

end LogdetLean.GramHafnian.ThreePaper.Verification
