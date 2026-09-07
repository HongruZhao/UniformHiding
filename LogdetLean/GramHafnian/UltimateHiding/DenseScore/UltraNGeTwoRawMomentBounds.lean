import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H12_RawFourthExactRecurrenceBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.PositiveTraceMomentInternal
import Mathlib.Tactic

/-!
# Ultra-sharp raw lower-trace moments in dimensions at least two

For `N >= 2`, the exact H8/H10 recurrences give the source bounds

* `E T1^4 <= 34 N^8`, hence `||T1||_4 <= (1147/475) N^2`;
* `E T2^2 <= 88 N^6`, hence `||T2||_2 <= (7439/793) N^3`;
* the exact recurrence gives `E T2 <= (533/108) N^3`.

Together with positivity and the exact first-trace mean, these imply the
rational raw lower-moment ledger used by the ultra cubic remainder.
The missing dimension-one projective case is handled separately by the
already checked identity `Q_v = 0`.
-/

open MeasureTheory
open scoped MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

set_option maxHeartbeats 3600000
set_option maxRecDepth 100000

open U08
open LogdetLean.GramHafnian.Wishart
open Matrix Unitary

def ultraNGeTwoRawTraceOneL4Constant : ℝ := 1147 / 475

def ultraNGeTwoRawTraceOneCubeConstant : ℝ :=
  ultraNGeTwoRawTraceOneL4Constant ^ 3

def ultraNGeTwoRawTraceOneSquareConstant : ℝ :=
  ultraNGeTwoRawTraceOneL4Constant ^ 2

def ultraNGeTwoRawTraceTwoL2Constant : ℝ := 7439 / 793

def ultraNGeTwoRawTraceOneTwoConstant : ℝ :=
  ultraNGeTwoRawTraceOneL4Constant * ultraNGeTwoRawTraceTwoL2Constant

def ultraNGeTwoRawTraceTwoL1Constant : ℝ := 533 / 108

def ultraNGeTwoRawTraceOneL1Constant : ℝ := 3 / 2

/-- Sharp coefficient-positive degree-two recurrence estimate at `n >= 2`.
The endpoint `n = 2`, `c = 26` fixes the rational coefficient `533/108`. -/
theorem h12TraceTwoRawMeanNumerator_le_533_div_108_dense_ultraNGeTwo
    {n c : ℝ} (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    108 * h12TraceTwoRawMeanNumerator n c ≤
      533 * n ^ 3 * h8H10DegreeTwoDenominator c := by
  let e : ℝ := n - 2
  let d : ℝ := c - 13 * n
  have he : 0 ≤ e := by dsimp only [e]; linarith
  have hd : 0 ≤ d := by dsimp only [d]; linarith
  have hnRep : n = 2 + e := by dsimp only [e]; ring
  have hcRep : c = 13 * (2 + e) + d := by dsimp only [e, d]; ring
  rw [hnRep, hcRep]
  unfold h12TraceTwoRawMeanNumerator h8H10DegreeTwoDenominator
  apply sub_nonneg.mp
  ring_nf
  positivity

private theorem h12TraceTwoRawMeanRecurrenceMoment_le_ultraNGeTwo
    {n c x2 y x3 xy z x4 x2y y2 xz q : ℝ}
    (h : H8H10ExactTraceRecurrenceSystem
      n c x2 y x3 xy z x4 x2y y2 xz q)
    (hn : 2 ≤ n) (hdense : 13 * n ≤ c) :
    h12TraceTwoRawMeanRecurrenceMoment n x2 y ≤
      ultraNGeTwoRawTraceTwoL1Constant * n ^ 3 := by
  have hnOne : 1 ≤ n := by linarith
  have hc : 26 ≤ c := by nlinarith
  have hdenPos : 0 < h8H10DegreeTwoDenominator c := by
    unfold h8H10DegreeTwoDenominator
    exact mul_pos (by linarith) (by linarith)
  rw [h12TraceTwoRawMeanRecurrenceMoment_eq_exact h hnOne hdense]
  apply (div_le_iff₀ hdenPos).2
  have hnum :=
    h12TraceTwoRawMeanNumerator_le_533_div_108_dense_ultraNGeTwo hn hdense
  unfold ultraNGeTwoRawTraceTwoL1Constant
  nlinarith

private theorem h10DenominatorFirstRawMoment_le_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    h10DenominatorFirstRawMoment N K ≤
      ultraNGeTwoRawTraceTwoL1Constant * (N : ℝ) ^ 3 := by
  have hNOne : 1 ≤ N := by omega
  rw [h10DenominatorFirstRawMoment_eq_traceMoments_internal]
  simpa only [h12TraceTwoRawMeanRecurrenceMoment] using
    h12TraceTwoRawMeanRecurrenceMoment_le_ultraNGeTwo
      (h8H10ExactTraceRecurrenceSystem_internal hNOne hdense)
      (by exact_mod_cast hN)
      (thirteen_mul_dimension_le_concreteCOEExponent_of_dense hNOne hdense)

theorem betaPrimeTraceTwoSource_integral_le_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ source, betaPrimeTraceTwoSource N K source
      ∂realBetaPrimeGaussianSourceLaw N K) ≤
      ultraNGeTwoRawTraceTwoL1Constant * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [betaPrimeTraceTwoSource_integral_eq_denominator_internal N K hgap]
  exact h10DenominatorFirstRawMoment_le_ultraNGeTwo hN hdense

private theorem betaPrimeTraceOneSource_memLp_four_ultraNGeTwo
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeTraceOneSource N K) 4
      (realBetaPrimeGaussianSourceLaw N K) := by
  have hmeas : AEStronglyMeasurable (betaPrimeTraceOneSource N K)
      (realBetaPrimeGaussianSourceLaw N K) := by
    exact ((measurable_const.mul (measurable_pi_apply _)).comp
      (measurable_realBetaPrimeTracePowerVector_internal 4 N K)).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hmeas (by norm_num) (by norm_num)).mp
  simpa [Real.rpow_natCast, norm_pow] using
    (integrable_betaPrimeTraceOneSource_fourth_h14_low
      (N := N) (K := K) hgap).norm

private theorem betaPrimeTraceTwoSource_memLp_two_ultraNGeTwo
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeTraceTwoSource N K) 2
      (realBetaPrimeGaussianSourceLaw N K) := by
  have hmeas : AEStronglyMeasurable (betaPrimeTraceTwoSource N K)
      (realBetaPrimeGaussianSourceLaw N K) := by
    exact (((measurable_const.pow_const 2).mul (measurable_pi_apply _)).comp
      (measurable_realBetaPrimeTracePowerVector_internal 4 N K)).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hmeas (by norm_num) (by norm_num)).mp
  simpa [Real.rpow_natCast, norm_pow] using
    (integrable_betaPrimeTraceTwoSource_square_h14_low
      (N := N) (K := K) hgap).norm

private theorem memLp_betaPrime_of_source_ultraNGeTwo
    {N K : ℕ} {p : ENNReal} {g : (Fin 4 → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (betaPrimeTraceFourLaw N K))
    (hsource : MemLp (g ∘ realBetaPrimeTracePowerVector 4 N K) p
      (realBetaPrimeGaussianSourceLaw N K)) :
    MemLp g p (betaPrimeTraceFourLaw N K) := by
  let f := realBetaPrimeTracePowerVector 4 N K
  let mu := realBetaPrimeGaussianSourceLaw N K
  have hmap : Measure.map f mu = betaPrimeTraceFourLaw N K := rfl
  have hgMap : AEStronglyMeasurable g (Measure.map f mu) := by
    simpa only [hmap] using hg
  have hf : AEMeasurable f mu :=
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  have hraw : MemLp g p (Measure.map f mu) :=
    (memLp_map_measure_iff hgMap hf).2 (by
      simpa only [f, mu] using hsource)
  simpa only [hmap] using hraw

private theorem lpNorm_two_sq_eq_integral_sq_ultraNGeTwo
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {f : Omega → ℝ}
    (hf : MemLp f 2 mu) :
    lpNorm f 2 mu ^ 2 = ∫ x, f x ^ 2 ∂mu := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (p := (2 : ENNReal))
    (by norm_num) (by norm_num) hf.aestronglyMeasurable]
  norm_num
  have hnonneg : 0 ≤ ∫ x, f x ^ 2 ∂mu :=
    integral_nonneg fun _ ↦ sq_nonneg _
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hnonneg]

/-! ## Source-to-beta-prime fourth and second moments -/

/-- Raw first-trace fourth moment, bounded by the convenient rational fourth
root majorant `1147/475`. -/
theorem betaPrimeYTraceOne_four_momentPackage_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceOne N K) 4 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (betaPrimeYTraceOne N K) 4 (betaPrimeTraceFourLaw N K) ≤
          ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2) := by
  let sourceMu := realBetaPrimeGaussianSourceLaw N K
  let X := betaPrimeTraceOneSource N K
  have hSource : MemLp X 4 sourceMu := by
    simpa only [X, sourceMu] using
      betaPrimeTraceOneSource_memLp_four_ultraNGeTwo hgap
  have hTargetMeas : AEStronglyMeasurable (betaPrimeYTraceOne N K)
      (betaPrimeTraceFourLaw N K) := by
    apply Measurable.aestronglyMeasurable
    unfold betaPrimeYTraceOne
    fun_prop
  have hcomp : betaPrimeYTraceOne N K ∘
      realBetaPrimeTracePowerVector 4 N K = betaPrimeTraceOneSource N K := rfl
  have hTarget : MemLp (betaPrimeYTraceOne N K) 4
      (betaPrimeTraceFourLaw N K) := by
    apply memLp_betaPrime_of_source_ultraNGeTwo hTargetMeas
    rw [hcomp]
    simpa only [X, sourceMu] using hSource
  refine ⟨hTarget, ?_⟩
  intro hdense
  have hPow : lpNorm X 4 sourceMu ^ 4 ≤ 34 * (N : ℝ) ^ 8 := by
    rw [U08.lpNorm_four_pow_four_eq_integral_pow_four_h9 hSource]
    simpa only [X, sourceMu, U08.h12RawTraceOneFourthConstantTwoPlus] using
      U08.betaPrimeTraceOneSource_fourth_integral_le_34_internal hN hdense
  have hSourceNorm : lpNorm X 4 sourceMu ≤
      ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0) (by
      unfold ultraNGeTwoRawTraceOneL4Constant
      positivity)
    calc
      lpNorm X 4 sourceMu ^ 4 ≤ 34 * (N : ℝ) ^ 8 := hPow
      _ ≤ (1147 / 475 : ℝ) ^ 4 * (N : ℝ) ^ 8 := by
        exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2) ^ 4 := by
        unfold ultraNGeTwoRawTraceOneL4Constant
        ring
  have hMapNorm := h9_lpNorm_source_map
    (p := (4 : ENNReal)) hTargetMeas
  rw [hcomp] at hMapNorm
  rw [show lpNorm (betaPrimeYTraceOne N K) 4
      (betaPrimeTraceFourLaw N K) = lpNorm X 4 sourceMu by
    simpa only [X, sourceMu] using hMapNorm]
  exact hSourceNorm

/-- Raw second-trace square moment, bounded by the convenient rational square
root majorant `7439/793`. -/
theorem betaPrimeYTraceTwo_two_momentPackage_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (betaPrimeYTraceTwo N K) 2 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (betaPrimeYTraceTwo N K) 2 (betaPrimeTraceFourLaw N K) ≤
          ultraNGeTwoRawTraceTwoL2Constant * (N : ℝ) ^ 3) := by
  let sourceMu := realBetaPrimeGaussianSourceLaw N K
  let X := betaPrimeTraceTwoSource N K
  have hSource : MemLp X 2 sourceMu := by
    simpa only [X, sourceMu] using
      betaPrimeTraceTwoSource_memLp_two_ultraNGeTwo hgap
  have hTargetMeas : AEStronglyMeasurable (betaPrimeYTraceTwo N K)
      (betaPrimeTraceFourLaw N K) := by
    apply Measurable.aestronglyMeasurable
    unfold betaPrimeYTraceTwo
    fun_prop
  have hcomp : betaPrimeYTraceTwo N K ∘
      realBetaPrimeTracePowerVector 4 N K = betaPrimeTraceTwoSource N K := rfl
  have hTarget : MemLp (betaPrimeYTraceTwo N K) 2
      (betaPrimeTraceFourLaw N K) := by
    apply memLp_betaPrime_of_source_ultraNGeTwo hTargetMeas
    rw [hcomp]
    simpa only [X, sourceMu] using hSource
  refine ⟨hTarget, ?_⟩
  intro hdense
  have hSq : lpNorm X 2 sourceMu ^ 2 ≤ 88 * (N : ℝ) ^ 6 := by
    rw [lpNorm_two_sq_eq_integral_sq_ultraNGeTwo hSource]
    simpa only [X, sourceMu, U08.h12RawTraceTwoSquareConstantTwoPlus] using
      U08.betaPrimeTraceTwoSource_square_integral_le_88_internal hN hdense
  have hSourceNorm : lpNorm X 2 sourceMu ≤
      ultraNGeTwoRawTraceTwoL2Constant * (N : ℝ) ^ 3 := by
    apply le_of_sq_le_sq
    · calc
        lpNorm X 2 sourceMu ^ 2 ≤ 88 * (N : ℝ) ^ 6 := hSq
        _ ≤ (7439 / 793 : ℝ) ^ 2 * (N : ℝ) ^ 6 := by
          exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = (ultraNGeTwoRawTraceTwoL2Constant * (N : ℝ) ^ 3) ^ 2 := by
          unfold ultraNGeTwoRawTraceTwoL2Constant
          ring
    · unfold ultraNGeTwoRawTraceTwoL2Constant
      positivity
  have hMapNorm := h9_lpNorm_source_map
    (p := (2 : ENNReal)) hTargetMeas
  rw [hcomp] at hMapNorm
  rw [show lpNorm (betaPrimeYTraceTwo N K) 2
      (betaPrimeTraceFourLaw N K) = lpNorm X 2 sourceMu by
    simpa only [X, sourceMu] using hMapNorm]
  exact hSourceNorm

/-! ## Probability-space monotonicity and Holder consequences -/

theorem betaPrimeYTraceOne_lpNorm_three_le_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceOne N K) 3 (betaPrimeTraceFourLaw N K) ≤
      ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  have hfour := (betaPrimeYTraceOne_four_momentPackage_ultraNGeTwo
    hN hgap).1
  exact (U08.lpNorm_le_lpNorm_of_exponent_le_probability
    hfour (by norm_num)).trans
      ((betaPrimeYTraceOne_four_momentPackage_ultraNGeTwo hN hgap).2 hdense)

theorem betaPrimeYTraceOne_lpNorm_two_le_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceOne N K) 2 (betaPrimeTraceFourLaw N K) ≤
      ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  have hfour := (betaPrimeYTraceOne_four_momentPackage_ultraNGeTwo
    hN hgap).1
  exact (U08.lpNorm_le_lpNorm_of_exponent_le_probability
    hfour (by norm_num)).trans
      ((betaPrimeYTraceOne_four_momentPackage_ultraNGeTwo hN hgap).2 hdense)

private theorem lpNorm_mul_le_lpNorm_two_mul_ultraNGeTwo
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {f g : Omega → ℝ} (hf : MemLp f 2 mu) (hg : MemLp g 2 mu) :
    lpNorm (fun omega ↦ f omega * g omega) 1 mu ≤
      lpNorm f 2 mu * lpNorm g 2 mu := by
  have hprod : MemLp (fun omega ↦ f omega * g omega) 1 mu := hg.mul' hf
  have he : eLpNorm (fun omega ↦ f omega * g omega) 1 mu ≤
      eLpNorm f 2 mu * eLpNorm g 2 mu := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      hf.aestronglyMeasurable hg.aestronglyMeasurable
      (fun x y : ℝ ↦ x * y) 1 (by
        filter_upwards [] with omega
        simp [nnnorm_mul])
  rw [← toReal_eLpNorm hprod.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable,
    ← toReal_eLpNorm hg.aestronglyMeasurable,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top) he

private theorem lpNorm_mul_le_of_holder_ultraNGeTwo
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p q s : ENNReal} {f g : Omega → ℝ}
    (hf : MemLp f q mu) (hg : MemLp g p mu)
    [ENNReal.HolderTriple p q s] :
    lpNorm (fun omega ↦ g omega * f omega) s mu ≤
      lpNorm g p mu * lpNorm f q mu := by
  have hprod : MemLp (fun omega ↦ g omega * f omega) s mu := hf.mul' hg
  have he : eLpNorm (fun omega ↦ g omega * f omega) s mu ≤
      eLpNorm g p mu * eLpNorm f q mu := by
    simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (p := p) (q := q) (r := s)
      hg.aestronglyMeasurable hf.aestronglyMeasurable
      (fun x y : ℝ ↦ x * y) 1 (by
        filter_upwards [] with omega
        simp [nnnorm_mul])
  rw [← toReal_eLpNorm hprod.aestronglyMeasurable,
    ← toReal_eLpNorm hg.aestronglyMeasurable,
    ← toReal_eLpNorm hf.aestronglyMeasurable,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono
    (ENNReal.mul_ne_top hg.eLpNorm_ne_top hf.eLpNorm_ne_top) he

theorem betaPrimeYTraceOneSquare_momentPackage_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u ^ 2) 1
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u ^ 2) 1
            (betaPrimeTraceFourLaw N K) ≤
          ultraNGeTwoRawTraceOneSquareConstant * (N : ℝ) ^ 4) := by
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  have hfour := (betaPrimeYTraceOne_four_momentPackage_ultraNGeTwo hN hgap).1
  have htwo : MemLp (betaPrimeYTraceOne N K) 2
      (betaPrimeTraceFourLaw N K) := hfour.mono_exponent (by norm_num)
  constructor
  · simpa only [pow_two] using htwo.mul' htwo
  · intro hdense
    have hnorm := betaPrimeYTraceOne_lpNorm_two_le_ultraNGeTwo hN hdense
    have hbound : 0 ≤ ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2 := by
      unfold ultraNGeTwoRawTraceOneL4Constant
      positivity
    calc
      lpNorm (fun u ↦ betaPrimeYTraceOne N K u ^ 2) 1
          (betaPrimeTraceFourLaw N K) ≤
        lpNorm (betaPrimeYTraceOne N K) 2 (betaPrimeTraceFourLaw N K) *
          lpNorm (betaPrimeYTraceOne N K) 2
            (betaPrimeTraceFourLaw N K) := by
          simpa only [pow_two] using
            lpNorm_mul_le_lpNorm_two_mul_ultraNGeTwo htwo htwo
      _ ≤ (ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2) *
          (ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2) :=
        mul_le_mul hnorm hnorm lpNorm_nonneg hbound
      _ = ultraNGeTwoRawTraceOneSquareConstant * (N : ℝ) ^ 4 := by
        unfold ultraNGeTwoRawTraceOneSquareConstant
          ultraNGeTwoRawTraceOneL4Constant
        ring

theorem betaPrimeYTraceOneCube_momentPackage_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u ^ 3) 1
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u ^ 3) 1
            (betaPrimeTraceFourLaw N K) ≤
          ultraNGeTwoRawTraceOneCubeConstant * (N : ℝ) ^ 6) := by
  let mu := betaPrimeTraceFourLaw N K
  let f := betaPrimeYTraceOne N K
  letI : IsProbabilityMeasure mu := betaPrimeTraceFourLaw_isProbability N K
  have hfour := (betaPrimeYTraceOne_four_momentPackage_ultraNGeTwo hN hgap).1
  have hf : MemLp f 3 mu := by
    simpa only [f, mu] using hfour.mono_exponent (by norm_num)
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
    lpNorm_mul_le_of_holder_ultraNGeTwo hf hf
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
        ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2 := by
      simpa only [f, mu] using
        betaPrimeYTraceOne_lpNorm_three_le_ultraNGeTwo hN hdense
    have hbound0 :
        0 ≤ ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2 := by
      unfold ultraNGeTwoRawTraceOneL4Constant
      positivity
    change lpNorm (fun u ↦ f u ^ 3) 1 mu ≤ _
    calc
      lpNorm (fun u ↦ f u ^ 3) 1 mu =
          lpNorm (fun u ↦ (f u * f u) * f u) 1 mu := by
        congr 1
        funext u
        ring
      _ ≤ lpNorm (fun u ↦ f u * f u) p32 mu * lpNorm f 3 mu :=
        lpNorm_mul_le_of_holder_ultraNGeTwo hf hsq
      _ ≤ (lpNorm f 3 mu * lpNorm f 3 mu) * lpNorm f 3 mu := by
        exact mul_le_mul_of_nonneg_right hsqNorm lpNorm_nonneg
      _ ≤ ((ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2) *
            (ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2)) *
          (ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2) := by
        exact mul_le_mul
          (mul_le_mul hfNorm hfNorm lpNorm_nonneg hbound0)
          hfNorm lpNorm_nonneg (mul_nonneg hbound0 hbound0)
      _ = ultraNGeTwoRawTraceOneCubeConstant * (N : ℝ) ^ 6 := by
        unfold ultraNGeTwoRawTraceOneCubeConstant
          ultraNGeTwoRawTraceOneL4Constant
        ring

theorem betaPrimeYTraceOneTwo_momentPackage_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun u ↦ betaPrimeYTraceOne N K u * betaPrimeYTraceTwo N K u) 1
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun u ↦ betaPrimeYTraceOne N K u * betaPrimeYTraceTwo N K u)
            1 (betaPrimeTraceFourLaw N K) ≤
          ultraNGeTwoRawTraceOneTwoConstant * (N : ℝ) ^ 5) := by
  letI : IsProbabilityMeasure (betaPrimeTraceFourLaw N K) :=
    betaPrimeTraceFourLaw_isProbability N K
  have hfour := (betaPrimeYTraceOne_four_momentPackage_ultraNGeTwo hN hgap).1
  have hone : MemLp (betaPrimeYTraceOne N K) 2
      (betaPrimeTraceFourLaw N K) := hfour.mono_exponent (by norm_num)
  have htwo := (betaPrimeYTraceTwo_two_momentPackage_ultraNGeTwo hN hgap).1
  constructor
  · exact htwo.mul' hone
  · intro hdense
    have honeNorm := betaPrimeYTraceOne_lpNorm_two_le_ultraNGeTwo hN hdense
    have htwoNorm :=
      (betaPrimeYTraceTwo_two_momentPackage_ultraNGeTwo hN hgap).2 hdense
    calc
      lpNorm (fun u ↦ betaPrimeYTraceOne N K u * betaPrimeYTraceTwo N K u)
          1 (betaPrimeTraceFourLaw N K) ≤
        lpNorm (betaPrimeYTraceOne N K) 2 (betaPrimeTraceFourLaw N K) *
          lpNorm (betaPrimeYTraceTwo N K) 2
            (betaPrimeTraceFourLaw N K) :=
        lpNorm_mul_le_lpNorm_two_mul_ultraNGeTwo hone htwo
      _ ≤ (ultraNGeTwoRawTraceOneL4Constant * (N : ℝ) ^ 2) *
          (ultraNGeTwoRawTraceTwoL2Constant * (N : ℝ) ^ 3) :=
        mul_le_mul honeNorm htwoNorm lpNorm_nonneg (by
          unfold ultraNGeTwoRawTraceOneL4Constant
          positivity)
      _ = ultraNGeTwoRawTraceOneTwoConstant * (N : ℝ) ^ 5 := by
        unfold ultraNGeTwoRawTraceOneTwoConstant
          ultraNGeTwoRawTraceOneL4Constant ultraNGeTwoRawTraceTwoL2Constant
        ring

/-! ## Exact positive first moments -/

private theorem trace_mul_nonneg_of_posSemidef_ultraNGeTwo
    {n : Type*} [Fintype n] [DecidableEq n]
    (C A : Matrix n n ℝ) (hC : C.PosSemidef) (hA : A.PosSemidef) :
    0 ≤ Matrix.trace (C * A) := by
  let S : Matrix n n ℝ := CFC.sqrt C
  let P : Matrix n n ℝ := S * A * S
  have hS : S.PosSemidef := (CFC.sqrt_nonneg C).posSemidef
  have hSstar : Sᴴ = S := hS.isHermitian.eq
  have hP : P.PosSemidef := by
    have h := hA.mul_mul_conjTranspose_same S
    rw [hSstar] at h
    exact h
  have hSS : S * S = C := by
    simpa only [S, pow_two] using CFC.sq_sqrt C
  have htrace : Matrix.trace P = Matrix.trace (C * A) := by
    calc
      Matrix.trace P = Matrix.trace ((S * A) * S) := by rfl
      _ = Matrix.trace (S * S * A) := Matrix.trace_mul_cycle S A S
      _ = Matrix.trace (C * A) := by rw [hSS]
  rw [← htrace]
  exact hP.trace_nonneg

private theorem betaPrimeTraceOneSource_nonneg_ultraNGeTwo
    {N K : ℕ} (hc : 0 ≤ concreteCOEExponent N K)
    (source : BetaPrimeGaussianSource N K) :
    0 ≤ betaPrimeTraceOneSource N K source := by
  let C := scaledInverseWishartDenominator N K source
  let A := realWishartGram source.1
  have hC : C.PosSemidef := by
    dsimp only [C, scaledInverseWishartDenominator]
    exact (realWishartGram_inv_posSemidef source.2).smul hc
  have hA : A.PosSemidef := realWishartGram_posSemidef source.1
  simpa only [C, A,
    betaPrimeTraceOneSource_eq_scaledInverseWishart_trace_h14_low] using
    trace_mul_nonneg_of_posSemidef_ultraNGeTwo C A hC hA

theorem betaPrimeYTraceOne_lpNorm_one_le_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceOne N K) 1 (betaPrimeTraceFourLaw N K) ≤
      ultraNGeTwoRawTraceOneL1Constant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let sourceMu := realBetaPrimeGaussianSourceLaw N K
  let X := betaPrimeTraceOneSource N K
  letI : IsProbabilityMeasure sourceMu :=
    realBetaPrimeGaussianSourceLaw_isProbability N K
  have hfour : MemLp X 4 sourceMu := by
    simpa only [X, sourceMu] using
      betaPrimeTraceOneSource_memLp_four_ultraNGeTwo hgap
  have hone : MemLp X 1 sourceMu := hfour.mono_exponent (by norm_num)
  have hc : 0 ≤ concreteCOEExponent N K := by
    have hdenseR : 16 * (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdense
    unfold concreteCOEExponent
    nlinarith [show (2 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
  have hSourceNorm : lpNorm X 1 sourceMu = (N : ℝ) * ((N : ℝ) + 1) := by
    rw [lpNorm_one_eq_integral_norm hone.aestronglyMeasurable]
    calc
      (∫ source, ‖X source‖ ∂sourceMu) = ∫ source, X source ∂sourceMu := by
        apply integral_congr_ae
        filter_upwards [] with source
        rw [Real.norm_eq_abs,
          abs_of_nonneg (betaPrimeTraceOneSource_nonneg_ultraNGeTwo hc source)]
      _ = (N : ℝ) * ((N : ℝ) + 1) := by
        simpa only [X, sourceMu] using
          U08.betaPrimeTraceOneSource_integral_eq_internal
            (N := N) (K := K) (by omega) (by omega)
  have hTargetMeas : AEStronglyMeasurable (betaPrimeYTraceOne N K)
      (betaPrimeTraceFourLaw N K) := by
    apply Measurable.aestronglyMeasurable
    unfold betaPrimeYTraceOne
    fun_prop
  have hMapNorm := h9_lpNorm_source_map
    (p := (1 : ENNReal)) hTargetMeas
  have hcomp : betaPrimeYTraceOne N K ∘
      realBetaPrimeTracePowerVector 4 N K = betaPrimeTraceOneSource N K := rfl
  rw [hcomp] at hMapNorm
  rw [hMapNorm, hSourceNorm]
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  unfold ultraNGeTwoRawTraceOneL1Constant
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ N)
    (sub_nonneg.mpr (by linarith : (1 : ℝ) ≤ N))]

theorem betaPrimeYTraceTwo_lpNorm_one_le_ultraNGeTwo
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (betaPrimeYTraceTwo N K) 1 (betaPrimeTraceFourLaw N K) ≤
      ultraNGeTwoRawTraceTwoL1Constant * (N : ℝ) ^ 3 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let sourceMu := realBetaPrimeGaussianSourceLaw N K
  let X := betaPrimeTraceTwoSource N K
  letI : IsProbabilityMeasure sourceMu :=
    realBetaPrimeGaussianSourceLaw_isProbability N K
  have htwo : MemLp X 2 sourceMu := by
    simpa only [X, sourceMu] using
      betaPrimeTraceTwoSource_memLp_two_ultraNGeTwo hgap
  have hone : MemLp X 1 sourceMu := htwo.mono_exponent (by norm_num)
  have hc : 0 ≤ concreteCOEExponent N K := by
    have hdenseR : 16 * (N : ℝ) ≤ (K : ℝ) := by exact_mod_cast hdense
    unfold concreteCOEExponent
    nlinarith [show (2 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
  have hNpos : 0 < (N : ℝ) := by positivity
  have hSourceNonneg (source : BetaPrimeGaussianSource N K) : 0 ≤ X source := by
    have htrace := U08.betaPrimeTraceOneSource_sq_le_dimension_mul_traceTwoSource
      hc source
    dsimp only [X]
    nlinarith [sq_nonneg (betaPrimeTraceOneSource N K source)]
  have hSourceNorm : lpNorm X 1 sourceMu = ∫ source, X source ∂sourceMu := by
    rw [lpNorm_one_eq_integral_norm hone.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with source
    rw [Real.norm_eq_abs, abs_of_nonneg (hSourceNonneg source)]
  have hSourceBound : lpNorm X 1 sourceMu ≤
      ultraNGeTwoRawTraceTwoL1Constant * (N : ℝ) ^ 3 := by
    rw [hSourceNorm]
    simpa only [X, sourceMu] using
      betaPrimeTraceTwoSource_integral_le_ultraNGeTwo hN hdense
  have hTargetMeas : AEStronglyMeasurable (betaPrimeYTraceTwo N K)
      (betaPrimeTraceFourLaw N K) := by
    apply Measurable.aestronglyMeasurable
    unfold betaPrimeYTraceTwo
    fun_prop
  have hMapNorm := h9_lpNorm_source_map
    (p := (1 : ENNReal)) hTargetMeas
  have hcomp : betaPrimeYTraceTwo N K ∘
      realBetaPrimeTracePowerVector 4 N K = betaPrimeTraceTwoSource N K := rfl
  rw [hcomp] at hMapNorm
  rw [hMapNorm]
  exact hSourceBound

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
