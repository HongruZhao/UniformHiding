import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H14_DirectExactSharpEnvelopeRecurrence
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_RadialBetaPrimeClosureConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A2Prime_A1TraceTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteBetaPrimeTraceCoordinates
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLogScoreOneSquareTwoDerived
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Direct exact `9990` H14 envelope bound

The sharp fixed-matrix H14 cancellation envelope has four signed/raw trace
terms.  Instead of bounding those terms separately, this module transports
the single exact recurrence certificate from the Gaussian source to the
beta-prime law and then to the concrete COE score endpoint.

The dimension-at-least-two endpoint has constant `9990`.  Dimension one is
closed separately by the exact pointwise vanishing of every centered log
score, so the same public constant holds for every positive dimension.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration
open U08

set_option maxHeartbeats 7200000
set_option maxRecDepth 100000

def h14DirectExactSharpEnvelopeConstant : ℝ := 9990

theorem h14DirectExactSharpEnvelopeConstant_eq :
    h14DirectExactSharpEnvelopeConstant = 9990 := rfl

/-- The sharp H14 envelope written on the exposed beta-prime trace law. -/
def h14BetaPrimeProjectiveCancellationSharpEnvelope (N K : ℕ)
    (u : Fin 4 → ℝ) : ℝ :=
  1536 * (betaPrimeYTraceOne N K u ^ 2 / (N : ℝ) ^ 2) +
    1280 * (betaPrimeYTraceTwo N K u / (N : ℝ) ^ 2) +
    3072 * (betaPrimeYTraceOne N K u ^ 4 /
      ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)) +
    2560 * (betaPrimeYTraceTwo N K u ^ 2 /
      ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))

theorem measurable_h14BetaPrimeProjectiveCancellationSharpEnvelope
    (N K : ℕ) :
    Measurable (h14BetaPrimeProjectiveCancellationSharpEnvelope N K) := by
  unfold h14BetaPrimeProjectiveCancellationSharpEnvelope betaPrimeYTraceOne
    betaPrimeYTraceTwo
  fun_prop

theorem h14BetaPrimeProjectiveCancellationSharpEnvelope_comp_source
    (N K : ℕ) (source : U08.BetaPrimeGaussianSource N K) :
    h14BetaPrimeProjectiveCancellationSharpEnvelope N K
        (realBetaPrimeTracePowerVector 4 N K source) =
      1536 * (betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2) +
        1280 * (betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2) +
        3072 * (betaPrimeTraceOneSource N K source ^ 4 /
          ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)) +
        2560 * (betaPrimeTraceTwoSource N K source ^ 2 /
          ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)) := by
  rfl

theorem integrable_h14BetaPrimeProjectiveCancellationSharpEnvelope_source
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable
      (fun source : U08.BetaPrimeGaussianSource N K ↦
        h14BetaPrimeProjectiveCancellationSharpEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source))
      (realBetaPrimeGaussianSourceLaw N K) := by
  have hOneSq :=
    (U08.integrable_betaPrimeTraceOneSource_sq_internal hgap).div_const
      ((N : ℝ) ^ 2) |>.const_mul (1536 : ℝ)
  have hTwo :=
    (U08.integrable_betaPrimeTraceTwoSource_internal hgap).div_const
      ((N : ℝ) ^ 2) |>.const_mul (1280 : ℝ)
  have hOneFourth :=
    (U08.integrable_betaPrimeTraceOneSource_fourth_h14_low hgap).div_const
      ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) |>.const_mul (3072 : ℝ)
  have hTwoSq :=
    (U08.integrable_betaPrimeTraceTwoSource_square_h14_low hgap).div_const
      ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2) |>.const_mul (2560 : ℝ)
  change Integrable (fun source : U08.BetaPrimeGaussianSource N K ↦
    1536 * (betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2) +
      1280 * (betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2) +
      3072 * (betaPrimeTraceOneSource N K source ^ 4 /
        ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)) +
      2560 * (betaPrimeTraceTwoSource N K source ^ 2 /
        ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)))
    (realBetaPrimeGaussianSourceLaw N K)
  exact ((hOneSq.add hTwo).add hOneFourth).add hTwoSq

theorem integrable_h14BetaPrimeProjectiveCancellationSharpEnvelope
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (h14BetaPrimeProjectiveCancellationSharpEnvelope N K)
      (betaPrimeTraceFourLaw N K) := by
  unfold betaPrimeTraceFourLaw
  apply (integrable_map_measure
    (measurable_h14BetaPrimeProjectiveCancellationSharpEnvelope N K).aestronglyMeasurable
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable).2
  exact integrable_h14BetaPrimeProjectiveCancellationSharpEnvelope_source hgap

theorem integral_h14BetaPrimeProjectiveCancellationSharpEnvelope_source_eq
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    (∫ source,
        h14BetaPrimeProjectiveCancellationSharpEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source)
        ∂realBetaPrimeGaussianSourceLaw N K) =
      1536 *
          (∫ source, betaPrimeTraceOneSource N K source ^ 2
            ∂realBetaPrimeGaussianSourceLaw N K) / (N : ℝ) ^ 2 +
        1280 *
          (∫ source, betaPrimeTraceTwoSource N K source
            ∂realBetaPrimeGaussianSourceLaw N K) / (N : ℝ) ^ 2 +
        3072 *
          (∫ source, betaPrimeTraceOneSource N K source ^ 4
            ∂realBetaPrimeGaussianSourceLaw N K) /
          ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
        2560 *
          (∫ source, betaPrimeTraceTwoSource N K source ^ 2
            ∂realBetaPrimeGaussianSourceLaw N K) /
          ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2) := by
  have hOneBase := U08.integrable_betaPrimeTraceOneSource_sq_internal hgap
  have hTwoBase := U08.integrable_betaPrimeTraceTwoSource_internal hgap
  have hOneFourthBase := U08.integrable_betaPrimeTraceOneSource_fourth_h14_low hgap
  have hTwoSqBase := U08.integrable_betaPrimeTraceTwoSource_square_h14_low hgap
  have hOne := hOneBase.div_const ((N : ℝ) ^ 2) |>.const_mul (1536 : ℝ)
  have hTwo := hTwoBase.div_const ((N : ℝ) ^ 2) |>.const_mul (1280 : ℝ)
  have hOneFourth := hOneFourthBase.div_const
    ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) |>.const_mul (3072 : ℝ)
  have hTwoSq := hTwoSqBase.div_const
    ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2) |>.const_mul (2560 : ℝ)
  change (∫ source,
      1536 * (betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2) +
        1280 * (betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2) +
        3072 * (betaPrimeTraceOneSource N K source ^ 4 /
          ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)) +
        2560 * (betaPrimeTraceTwoSource N K source ^ 2 /
          ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))
      ∂realBetaPrimeGaussianSourceLaw N K) = _
  calc
    _ =
        (∫ source,
          1536 * (betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2) +
            1280 * (betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2) +
            3072 * (betaPrimeTraceOneSource N K source ^ 4 /
              ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2))
          ∂realBetaPrimeGaussianSourceLaw N K) +
        ∫ source, 2560 * (betaPrimeTraceTwoSource N K source ^ 2 /
          ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))
          ∂realBetaPrimeGaussianSourceLaw N K :=
      integral_add ((hOne.add hTwo).add hOneFourth) hTwoSq
    _ =
        ((∫ source,
            1536 * (betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2) +
              1280 * (betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2)
            ∂realBetaPrimeGaussianSourceLaw N K) +
          ∫ source, 3072 * (betaPrimeTraceOneSource N K source ^ 4 /
            ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2))
            ∂realBetaPrimeGaussianSourceLaw N K) +
        ∫ source, 2560 * (betaPrimeTraceTwoSource N K source ^ 2 /
          ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))
          ∂realBetaPrimeGaussianSourceLaw N K := by
      exact congrArg
        (fun x : ℝ ↦ x +
          ∫ source, 2560 * (betaPrimeTraceTwoSource N K source ^ 2 /
            ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))
            ∂realBetaPrimeGaussianSourceLaw N K)
        (integral_add (hOne.add hTwo) hOneFourth)
    _ =
        (((∫ source,
              1536 * (betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2)
              ∂realBetaPrimeGaussianSourceLaw N K) +
            ∫ source, 1280 * (betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2)
              ∂realBetaPrimeGaussianSourceLaw N K) +
          ∫ source, 3072 * (betaPrimeTraceOneSource N K source ^ 4 /
            ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2))
            ∂realBetaPrimeGaussianSourceLaw N K) +
        ∫ source, 2560 * (betaPrimeTraceTwoSource N K source ^ 2 /
          ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))
          ∂realBetaPrimeGaussianSourceLaw N K := by
      exact congrArg
        (fun x : ℝ ↦
          (x +
            ∫ source, 3072 * (betaPrimeTraceOneSource N K source ^ 4 /
              ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2))
              ∂realBetaPrimeGaussianSourceLaw N K) +
          ∫ source, 2560 * (betaPrimeTraceTwoSource N K source ^ 2 /
            ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))
            ∂realBetaPrimeGaussianSourceLaw N K)
        (integral_add hOne hTwo)
    _ = _ := by
      rw [integral_const_mul, integral_div,
        integral_const_mul, integral_div,
        integral_const_mul, integral_div,
        integral_const_mul, integral_div]
      ring

theorem integral_h14BetaPrimeProjectiveCancellationSharpEnvelope_le_directExact
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ u, h14BetaPrimeProjectiveCancellationSharpEnvelope N K u
      ∂betaPrimeTraceFourLaw N K) ≤
      h14DirectExactSharpEnvelopeConstant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hmapMeas : AEMeasurable (realBetaPrimeTracePowerVector 4 N K)
      (realBetaPrimeGaussianSourceLaw N K) :=
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  have hEnvelopeMeas : AEStronglyMeasurable
      (h14BetaPrimeProjectiveCancellationSharpEnvelope N K)
      (betaPrimeTraceFourLaw N K) :=
    (measurable_h14BetaPrimeProjectiveCancellationSharpEnvelope N K).aestronglyMeasurable
  have hpush :
      (∫ u, h14BetaPrimeProjectiveCancellationSharpEnvelope N K u
        ∂betaPrimeTraceFourLaw N K) =
      ∫ source,
        h14BetaPrimeProjectiveCancellationSharpEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source)
        ∂realBetaPrimeGaussianSourceLaw N K := by
    unfold betaPrimeTraceFourLaw
    exact integral_map hmapMeas hEnvelopeMeas
  rw [hpush,
    integral_h14BetaPrimeProjectiveCancellationSharpEnvelope_source_eq hgap]
  simpa only [h14DirectExactSharpEnvelopeConstant] using
    U08.h14DirectSharpGaussianSourceExpectation_le_9990_internal hN hdense

theorem h14_betaPrimeProjectiveCancellationSharpEnvelope_momentPackage_directExact
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h14BetaPrimeProjectiveCancellationSharpEnvelope N K)
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        (∫ u, h14BetaPrimeProjectiveCancellationSharpEnvelope N K u
          ∂betaPrimeTraceFourLaw N K) ≤
          h14DirectExactSharpEnvelopeConstant * (N : ℝ) ^ 2) := by
  exact ⟨integrable_h14BetaPrimeProjectiveCancellationSharpEnvelope hgap,
    fun hdense ↦
      integral_h14BetaPrimeProjectiveCancellationSharpEnvelope_le_directExact
        hN hdense⟩

theorem h14_betaPrimeProjectiveCancellationSharpEnvelope_comp_traceFour
    (N K : ℕ) (A : ConcreteMatrixState N) :
    h14BetaPrimeProjectiveCancellationSharpEnvelope N K
        (concreteCOETracePowerVector 4 N K A) =
      h14ProjectiveCancellationSharpEnvelope N K A := by
  change
    1536 * (concreteBetaPrimeYTraceOne N K A ^ 2 / (N : ℝ) ^ 2) +
        1280 * (concreteBetaPrimeYTraceTwo N K A / (N : ℝ) ^ 2) +
        3072 * (concreteBetaPrimeYTraceOne N K A ^ 4 /
          ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)) +
        2560 * (concreteBetaPrimeYTraceTwo N K A ^ 2 /
          ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)) = _
  rw [concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne,
    concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo]
  rfl

theorem h14ProjectiveCancellationSharpEnvelope_momentPackage_of_H6_directExact
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K) :
    Integrable (h14ProjectiveCancellationSharpEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h14ProjectiveCancellationSharpEnvelope N K A
            ∂concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) ≤
          h14DirectExactSharpEnvelopeConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) :=
    concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K
  let f : ConcreteMatrixState N → Fin 4 → ℝ :=
    concreteCOETracePowerVector 4 N K
  let b : (Fin 4 → ℝ) → ℝ :=
    h14BetaPrimeProjectiveCancellationSharpEnvelope N K
  have hBeta :=
    h14_betaPrimeProjectiveCancellationSharpEnvelope_momentPackage_directExact
      hN hgap
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
  have hfun : b ∘ f = h14ProjectiveCancellationSharpEnvelope N K := by
    funext A
    exact h14_betaPrimeProjectiveCancellationSharpEnvelope_comp_traceFour
      N K A
  constructor
  · rw [← hfun]
    exact hPullInt
  · intro hdense
    rw [← hfun, hPullIntegral]
    simpa only [b] using hBeta.2 hdense

theorem h14ProjectiveCancellationSharpEnvelope_momentPackage_directExact_A2A3
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h14ProjectiveCancellationSharpEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h14ProjectiveCancellationSharpEnvelope N K A
            ∂concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) ≤
          h14DirectExactSharpEnvelopeConstant * (N : ℝ) ^ 2) := by
  have hNOne : 1 ≤ N := by omega
  have hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K := by
    simpa only [betaPrimeTraceFourLaw] using
      (coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
        (r := 4) hNOne (by omega : 2 * N ≤ K))
  exact h14ProjectiveCancellationSharpEnvelope_momentPackage_of_H6_directExact
    hN hgap hH6

theorem centeredLogScore_twoSquare_momentPackage_directExact_NGeTwo_A1A2A3
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h14DirectExactSharpEnvelopeConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) :=
    concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K
  let sphere : Measure (ComplexUnitSphere N) :=
    complexUnitSphereProbabilityMeasure N
  let f : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 2 N K p ^ 2
  let envelope : ConcreteMatrixState N → ℝ :=
    h14ProjectiveCancellationSharpEnvelope N K
  have hNOne : 1 ≤ N := by omega
  letI : IsProbabilityMeasure μ :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hNOne
  have hfMeas : AEStronglyMeasurable f (μ.prod sphere) :=
    (measurable_concreteCenteredEll_two (N := N) (K := K) hNOne).pow_const 2
      |>.aestronglyMeasurable
  have hSupport : ∀ᵐ A ∂μ,
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
    simpa only [μ] using
      friedmanMello1985_scaledCOECorner_ae_support_from_density
        hNOne (by omega : 2 * N ≤ K)
  have hSlices : ∀ᵐ A ∂μ,
      Integrable (fun v ↦ f (A, v)) sphere ∧
        (∫ v, ‖f (A, v)‖ ∂sphere) ≤ envelope A := by
    filter_upwards [hSupport] with A hA
    have hPA := (h14_centeredEllTwoProjectiveContraction_internal N K)
      hNOne hgap A hA.1 hA.2
    have heq : (fun v ↦ f (A, v)) =
        h14CenteredSandwichSecondSquare N K A := by
      funext v
      simp only [f]
      exact
        concreteCenteredEll_two_square_eq_projectiveSandwichSquare_h14_internal
          hNOne hgap A v hA.1 hA.2
    constructor
    · rw [heq]
      exact hPA.1
    · rw [show (fun v ↦ ‖f (A, v)‖) =
          fun v ↦ ‖h14CenteredSandwichSecondSquare N K A v‖ by
        funext v
        exact congrArg norm (congrFun heq v)]
      simpa only [μ, sphere, envelope] using hPA.2
  have hEnvelope :=
    h14ProjectiveCancellationSharpEnvelope_momentPackage_directExact_A2A3
      hN hgap
  have hEnvelopeInt : Integrable envelope μ := by
    simpa only [envelope, μ] using hEnvelope.1
  have hInnerMeas : AEStronglyMeasurable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) μ :=
    hfMeas.norm.integral_prod_right'
  have hInnerInt : Integrable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) μ := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [hSlices] with A hA
    have hInnerNonneg : 0 ≤ ∫ v, ‖f (A, v)‖ ∂sphere :=
      integral_nonneg fun _ ↦ norm_nonneg _
    have hEnvelopeNonneg : 0 ≤ envelope A := hInnerNonneg.trans hA.2
    rw [Real.norm_eq_abs, abs_of_nonneg hInnerNonneg,
      Real.norm_eq_abs, abs_of_nonneg hEnvelopeNonneg]
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
        h14DirectExactSharpEnvelopeConstant * (N : ℝ) ^ 2 := by
      calc
        lpNorm f 1 (μ.prod sphere) =
            ∫ A, ∫ v, ‖f (A, v)‖ ∂sphere ∂μ := by
          rw [lpNorm_one_eq_integral_norm hfMeas]
          exact integral_prod (fun p ↦ ‖f p‖) hfInt.norm
        _ ≤ ∫ A, envelope A ∂μ := by
          apply integral_mono_ae hInnerInt hEnvelopeInt
          filter_upwards [hSlices] with A hA
          exact hA.2
        _ ≤ h14DirectExactSharpEnvelopeConstant * (N : ℝ) ^ 2 := by
          simpa only [envelope, μ] using hEnvelope.2 hdense
    simpa only [f, μ, sphere, concreteCenteredScoreProductLaw] using hbound

theorem centeredLogScore_twoSquare_momentPackage_directExact_A1A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h14DirectExactSharpEnvelopeConstant * (N : ℝ) ^ 2) := by
  by_cases hOne : N = 1
  · subst N
    have hzero : (fun p ↦ concreteCenteredEll 2 1 K p ^ 2) = 0 := by
      funext p
      rw [show concreteCenteredEll 2 1 K p = 0 by
        exact concreteCenteredLogScore_fin_one_eq_zero (by omega) p.2 p.1]
      simp
    rw [hzero]
    constructor
    · exact MemLp.zero'
    · intro _
      rw [lpNorm_zero]
      norm_num [h14DirectExactSharpEnvelopeConstant]
  · exact centeredLogScore_twoSquare_momentPackage_directExact_NGeTwo_A1A2A3
      (by omega) hgap

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
