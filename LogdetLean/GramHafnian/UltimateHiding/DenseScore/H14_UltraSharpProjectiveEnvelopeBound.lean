import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_StrongTwoSquareProductBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_FourthRadialProducerConditional
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Ultra-sharp H14 projective envelope

The original producer proves that each of the two normalized fourth-radial
terms costs `2^16 * N^2`, then relaxes their sum to the common `2^40`
constant.  This module retains the exact sum `2^17` and propagates it through
the H14 matrix and product-law transports.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL
open U08

def h14UltraNormalizedFourthRemainderConstant : ℝ := (2 : ℝ) ^ 17

def h14UltraProjectiveEnvelopeConstant : ℝ :=
  h14BetaPrimeProjectiveLowerMomentConstant +
    4096 * h14UltraNormalizedFourthRemainderConstant

theorem h14UltraProjectiveEnvelopeConstant_eq :
    h14UltraProjectiveEnvelopeConstant = 537133056 := by
  norm_num [h14UltraProjectiveEnvelopeConstant,
    h14UltraNormalizedFourthRemainderConstant,
    h14BetaPrimeProjectiveLowerMomentConstant]

/-- The exact pre-relaxation output of the checked H14 radial producer. -/
theorem integral_h14BetaPrimeNormalizedFourthRemainder_le_ultra
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (HWick : H14FiniteGaussianFourthWickFormula N K)
    (Hden : H14DenominatorFourthTracePolynomialBounds N K)
    (hdense : 16 * N ≤ K) :
    (∫ u, h14BetaPrimeNormalizedFourthRemainder N K u
      ∂betaPrimeTraceFourLaw N K) ≤
      h14UltraNormalizedFourthRemainderConstant * (N : ℝ) ^ 2 := by
  let n : ℝ := N
  let c : ℝ := concreteCOEExponent N K
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < N by omega)
  have hdenseR : (16 : ℝ) * n ≤ (K : ℝ) := by
    dsimp only [n]
    exact_mod_cast hdense
  have hc : n ≤ c := by
    have hNreal : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    dsimp only [n] at hdenseR
    dsimp only [n, c]
    unfold concreteCOEExponent
    linarith
  have hcpos : 0 < c := hn.trans_le hc
  have hsource := U08.h14_explicitGaussianFourthSourceBounds_conditional
    hgap HWick Hden
  have hOneBound := hsource.1 hdense
  have hTwoBound := hsource.2 hdense
  have hOneInt := U08.integrable_betaPrimeTraceOneSource_fourth_h14 hgap
  have hTwoInt := U08.integrable_betaPrimeTraceTwoSource_square_h14 hgap
  have hmapMeas : AEMeasurable (realBetaPrimeTracePowerVector 4 N K)
      (realBetaPrimeGaussianSourceLaw N K) :=
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  have hremMeas : AEStronglyMeasurable
      (h14BetaPrimeNormalizedFourthRemainder N K)
      (betaPrimeTraceFourLaw N K) :=
    (U08.integrable_h14BetaPrimeNormalizedFourthRemainder_internal
      hgap).aestronglyMeasurable
  have hpush :
      (∫ u, h14BetaPrimeNormalizedFourthRemainder N K u
        ∂betaPrimeTraceFourLaw N K) =
      ∫ source,
        h14BetaPrimeNormalizedFourthRemainder N K
          (realBetaPrimeTracePowerVector 4 N K source)
        ∂realBetaPrimeGaussianSourceLaw N K := by
    unfold betaPrimeTraceFourLaw
    exact integral_map hmapMeas hremMeas
  rw [hpush]
  change (∫ source,
      betaPrimeTraceOneSource N K source ^ 4 /
          (n ^ 4 * c ^ 2) +
        betaPrimeTraceTwoSource N K source ^ 2 /
          (n ^ 2 * c ^ 2)
      ∂realBetaPrimeGaussianSourceLaw N K) ≤
        h14UltraNormalizedFourthRemainderConstant * n ^ 2
  have hOneDiv : Integrable
      (fun source ↦ betaPrimeTraceOneSource N K source ^ 4 /
        (n ^ 4 * c ^ 2))
      (realBetaPrimeGaussianSourceLaw N K) :=
    hOneInt.div_const (n ^ 4 * c ^ 2)
  have hTwoDiv : Integrable
      (fun source ↦ betaPrimeTraceTwoSource N K source ^ 2 /
        (n ^ 2 * c ^ 2))
      (realBetaPrimeGaussianSourceLaw N K) :=
    hTwoInt.div_const (n ^ 2 * c ^ 2)
  rw [integral_add hOneDiv hTwoDiv, integral_div, integral_div]
  have hdenOne : 0 < n ^ 4 * c ^ 2 := by positivity
  have hdenTwo : 0 < n ^ 2 * c ^ 2 := by positivity
  have hOneScaled :
      (∫ source, betaPrimeTraceOneSource N K source ^ 4
        ∂realBetaPrimeGaussianSourceLaw N K) / (n ^ 4 * c ^ 2) ≤
        (2 : ℝ) ^ 16 * n ^ 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ 16 * n ^ 8) / (n ^ 4 * c ^ 2) :=
        (div_le_div_iff_of_pos_right hdenOne).2
          (by simpa only [n] using hOneBound)
      _ = ((2 : ℝ) ^ 16 * n ^ 4) / c ^ 2 := by
        field_simp [hn.ne'] <;> ring
      _ ≤ ((2 : ℝ) ^ 16 * n ^ 4) / n ^ 2 := by
        exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn)
          (by nlinarith [sq_nonneg (c - n)])
      _ = (2 : ℝ) ^ 16 * n ^ 2 := by
        field_simp [hn.ne'] <;> ring
  have hTwoScaled :
      (∫ source, betaPrimeTraceTwoSource N K source ^ 2
        ∂realBetaPrimeGaussianSourceLaw N K) / (n ^ 2 * c ^ 2) ≤
        (2 : ℝ) ^ 16 * n ^ 2 := by
    calc
      _ ≤ ((2 : ℝ) ^ 16 * n ^ 6) / (n ^ 2 * c ^ 2) :=
        (div_le_div_iff_of_pos_right hdenTwo).2
          (by simpa only [n] using hTwoBound)
      _ = ((2 : ℝ) ^ 16 * n ^ 4) / c ^ 2 := by
        field_simp [hn.ne'] <;> ring
      _ ≤ ((2 : ℝ) ^ 16 * n ^ 4) / n ^ 2 := by
        exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn)
          (by nlinarith [sq_nonneg (c - n)])
      _ = (2 : ℝ) ^ 16 * n ^ 2 := by
        field_simp [hn.ne'] <;> ring
  calc
    _ ≤ (2 : ℝ) ^ 16 * n ^ 2 + (2 : ℝ) ^ 16 * n ^ 2 :=
      add_le_add hOneScaled hTwoScaled
    _ = h14UltraNormalizedFourthRemainderConstant * n ^ 2 := by
      unfold h14UltraNormalizedFourthRemainderConstant
      ring

/-- Sharp beta-prime H14 envelope with no endpoint-sized relaxation. -/
theorem h14_betaPrimeProjectiveCancellationEnvelope_momentPackage_ultra
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (HWick : H14FiniteGaussianFourthWickFormula N K)
    (Hden : H14DenominatorFourthTracePolynomialBounds N K) :
    Integrable (h14BetaPrimeProjectiveCancellationEnvelope N K)
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        (∫ u, h14BetaPrimeProjectiveCancellationEnvelope N K u
          ∂betaPrimeTraceFourLaw N K) ≤
          h14UltraProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  have hlower := integrable_h14BetaPrimeProjectiveLowerEnvelope_internal hgap
  have hfourth :=
    U08.integrable_h14BetaPrimeNormalizedFourthRemainder_internal hgap
  have hfourthScaled := hfourth.const_mul (4096 : ℝ)
  have hfull : Integrable (h14BetaPrimeProjectiveCancellationEnvelope N K)
      (betaPrimeTraceFourLaw N K) := by
    change Integrable (fun u ↦
      h14BetaPrimeProjectiveLowerEnvelope N K u +
        4096 * h14BetaPrimeNormalizedFourthRemainder N K u)
      (betaPrimeTraceFourLaw N K)
    exact hlower.add hfourthScaled
  refine ⟨hfull, ?_⟩
  intro hdense
  have hlowerBound := integral_h14BetaPrimeProjectiveLowerEnvelope_le_internal
    hN hgap hdense
  have hfourthBound := integral_h14BetaPrimeNormalizedFourthRemainder_le_ultra
    hN hgap HWick Hden hdense
  have hscaled := mul_le_mul_of_nonneg_left hfourthBound
    (show (0 : ℝ) ≤ 4096 by norm_num)
  change
    (∫ u, h14BetaPrimeProjectiveLowerEnvelope N K u +
        4096 * h14BetaPrimeNormalizedFourthRemainder N K u
      ∂betaPrimeTraceFourLaw N K) ≤
      h14UltraProjectiveEnvelopeConstant * (N : ℝ) ^ 2
  rw [integral_add hlower hfourthScaled, integral_const_mul]
  calc
    _ ≤ h14BetaPrimeProjectiveLowerMomentConstant * (N : ℝ) ^ 2 +
        4096 *
          (h14UltraNormalizedFourthRemainderConstant * (N : ℝ) ^ 2) :=
      add_le_add hlowerBound hscaled
    _ = h14UltraProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
      unfold h14UltraProjectiveEnvelopeConstant
      ring

/-- Push the ultra-sharp beta-prime envelope through exact H6. -/
theorem h14ProjectiveCancellationEnvelope_momentPackage_of_H6_ultra
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K)
    (HWick : H14FiniteGaussianFourthWickFormula N K)
    (Hden : H14DenominatorFourthTracePolynomialBounds N K) :
    Integrable (h14ProjectiveCancellationEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h14ProjectiveCancellationEnvelope N K A
            ∂concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) ≤
          h14UltraProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) :=
    concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K
  let f : ConcreteMatrixState N → Fin 4 → ℝ :=
    concreteCOETracePowerVector 4 N K
  let b : (Fin 4 → ℝ) → ℝ :=
    h14BetaPrimeProjectiveCancellationEnvelope N K
  have hBeta := h14_betaPrimeProjectiveCancellationEnvelope_momentPackage_ultra
    hN hgap HWick Hden
  have hf : AEMeasurable f μ := by
    simpa only [f, μ] using
      (measurable_concreteCOETracePowerVector_internal 4 N K).aemeasurable
  have hmap : Measure.map f μ = betaPrimeTraceFourLaw N K := by
    simpa only [f, μ] using hH6
  have hbMap : AEStronglyMeasurable b (Measure.map f μ) := by
    rw [hmap]
    simpa only [b] using hBeta.1.aestronglyMeasurable
  have hPullInt : Integrable (b ∘ f) μ := by
    apply (integrable_map_measure hbMap hf).1
    simpa only [hmap, b] using hBeta.1
  have hPullIntegral :
      (∫ A, (b ∘ f) A ∂μ) =
        ∫ u, b u ∂betaPrimeTraceFourLaw N K := by
    calc
      _ = ∫ u, b u ∂Measure.map f μ := (integral_map hf hbMap).symm
      _ = _ := by rw [hmap]
  have hfun : b ∘ f = h14ProjectiveCancellationEnvelope N K := by
    funext A
    exact h14_betaPrimeProjectiveCancellationEnvelope_comp_traceFour_internal
      N K A
  constructor
  · rw [← hfun]
    exact hPullInt
  · intro hdense
    rw [← hfun, hPullIntegral]
    simpa only [b] using hBeta.2 hdense

theorem h14ProjectiveCancellationEnvelope_momentPackage_ultra_A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h14ProjectiveCancellationEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h14ProjectiveCancellationEnvelope N K A
            ∂concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) ≤
          h14UltraProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  have hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K := by
    simpa only [betaPrimeTraceFourLaw] using
      (coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
        (r := 4) hN (by omega : 2 * N ≤ K))
  exact h14ProjectiveCancellationEnvelope_momentPackage_of_H6_ultra
    hN hgap hH6
      (h14FiniteGaussianFourthWickFormula_internal N K)
      (h14DenominatorFourthTracePolynomialBounds_internal N K)

/-- Literal centered-ell-two square package with the ultra-sharp H14
constant. -/
theorem centeredLogScore_twoSquare_momentPackage_ultra_A1A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h14UltraProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) :=
    concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K
  let sphere : Measure (ComplexUnitSphere N) :=
    complexUnitSphereProbabilityMeasure N
  let f : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 2 N K p ^ 2
  let envelope : ConcreteMatrixState N → ℝ :=
    h14ProjectiveCancellationEnvelope N K
  letI : IsProbabilityMeasure μ :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hfMeas : AEStronglyMeasurable f (μ.prod sphere) :=
    (measurable_concreteCenteredEll_two (N := N) (K := K) hN).pow_const 2
      |>.aestronglyMeasurable
  have hSupport : ∀ᵐ A ∂μ,
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
    simpa only [μ] using
      friedmanMello1985_scaledCOECorner_ae_support_from_density
        hN (by omega : 2 * N ≤ K)
  have hSlices : ∀ᵐ A ∂μ,
      Integrable (fun v ↦ f (A, v)) sphere ∧
        (∫ v, ‖f (A, v)‖ ∂sphere) ≤ envelope A := by
    filter_upwards [hSupport] with A hA
    have hPA := h14_fixedMatrix_projectiveCancellation_package_internal
      hN hgap A hA.1 hA.2
    have heq : (fun v ↦ f (A, v)) =
        h14CenteredSandwichSecondSquare N K A := by
      funext v
      simp only [f]
      exact
        concreteCenteredEll_two_square_eq_projectiveSandwichSquare_h14_internal
          hN hgap A v hA.1 hA.2
    constructor
    · rw [heq]
      exact hPA.1
    · rw [show (fun v ↦ ‖f (A, v)‖) =
          fun v ↦ ‖h14CenteredSandwichSecondSquare N K A v‖ by
        funext v
        exact congrArg norm (congrFun heq v)]
      simpa only [μ, sphere, envelope] using hPA.2
  have hEnvelope :=
    h14ProjectiveCancellationEnvelope_momentPackage_ultra_A2A3 hN hgap
  have hEnvelopeInt : Integrable envelope μ := by
    simpa only [envelope, μ] using hEnvelope.1
  have hInnerMeas : AEStronglyMeasurable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) μ :=
    hfMeas.norm.integral_prod_right'
  have hInnerInt : Integrable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) μ := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [hSlices] with A hA
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
      Real.norm_eq_abs,
      abs_of_nonneg (h14ProjectiveCancellationEnvelope_nonneg N K A)]
    exact hA.2
  have hfInt : Integrable f (μ.prod sphere) := by
    apply (integrable_prod_iff hfMeas).2
    exact ⟨hSlices.mono fun _ hA ↦ hA.1, hInnerInt⟩
  constructor
  · have hfMem : MemLp f 1 (μ.prod sphere) :=
      memLp_one_iff_integrable.mpr hfInt
    simpa only [f, μ, sphere, concreteCenteredScoreProductLaw] using hfMem
  · intro hdense
    have hbound : lpNorm f 1 (μ.prod sphere) ≤
        h14UltraProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
      calc
        lpNorm f 1 (μ.prod sphere) =
            ∫ A, ∫ v, ‖f (A, v)‖ ∂sphere ∂μ := by
          rw [lpNorm_one_eq_integral_norm hfMeas]
          exact integral_prod (fun p ↦ ‖f p‖) hfInt.norm
        _ ≤ ∫ A, envelope A ∂μ := by
          apply integral_mono_ae hInnerInt hEnvelopeInt
          filter_upwards [hSlices] with A hA
          exact hA.2
        _ ≤ h14UltraProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
          simpa only [envelope, μ] using hEnvelope.2 hdense
    simpa only [f, μ, sphere, concreteCenteredScoreProductLaw] using hbound

#print axioms integral_h14BetaPrimeNormalizedFourthRemainder_le_ultra
#print axioms centeredLogScore_twoSquare_momentPackage_ultra_A1A2A3

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
