import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H13_ScaleTwoExactEnvelopeRecurrence
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeRelaxedProjectiveClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A2Prime_A1TraceTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteBetaPrimeTraceCoordinates
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Scale-two exact H13 projective bound

The fixed-sphere H13 ledger costs exactly `8192` times its radial trace
basis, namely twice the H14 cancellation envelope.  A single exact recurrence
certificate bounds the expectation of those four monomials by `52204 N^2`
for `N >= 2`.  In dimension one every positive centered log score vanishes,
so the same public score bound holds in every positive dimension.
-/

open MeasureTheory
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL
open U08

set_option maxHeartbeats 7200000
set_option maxRecDepth 100000

def h13ScaleTwoProjectiveEnvelopeConstant : ℝ := 52204

theorem h13ScaleTwoProjectiveEnvelopeConstant_eq :
    h13ScaleTwoProjectiveEnvelopeConstant = 52204 := rfl

/-- The exact `8192` trace envelope on the concrete matrix state.  The
second trace is nonnegative on the almost-sure COE support. -/
def h13ScaleTwoProjectiveEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  8192 *
    (concreteCOETraceOne N K A ^ 2 / (N : ℝ) ^ 2 +
      concreteCOETraceTwo N K A / (N : ℝ) ^ 2 +
      concreteCOETraceOne N K A ^ 4 /
        ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
      concreteCOETraceTwo N K A ^ 2 /
        ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))

/-- The same envelope on the exposed beta-prime trace law. -/
def h13BetaPrimeScaleTwoProjectiveEnvelope (N K : ℕ)
    (u : Fin 4 → ℝ) : ℝ :=
  8192 *
    (betaPrimeYTraceOne N K u ^ 2 / (N : ℝ) ^ 2 +
      betaPrimeYTraceTwo N K u / (N : ℝ) ^ 2 +
      betaPrimeYTraceOne N K u ^ 4 /
        ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
      betaPrimeYTraceTwo N K u ^ 2 /
        ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))

theorem measurable_h13BetaPrimeScaleTwoProjectiveEnvelope (N K : ℕ) :
    Measurable (h13BetaPrimeScaleTwoProjectiveEnvelope N K) := by
  unfold h13BetaPrimeScaleTwoProjectiveEnvelope betaPrimeYTraceOne
    betaPrimeYTraceTwo
  fun_prop

theorem h13BetaPrimeScaleTwoProjectiveEnvelope_comp_source
    (N K : ℕ) (source : U08.BetaPrimeGaussianSource N K) :
    h13BetaPrimeScaleTwoProjectiveEnvelope N K
        (realBetaPrimeTracePowerVector 4 N K source) =
      8192 *
        (betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2 +
          betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2 +
          betaPrimeTraceOneSource N K source ^ 4 /
            ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
          betaPrimeTraceTwoSource N K source ^ 2 /
            ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)) := by
  rfl

theorem integrable_h13BetaPrimeScaleTwoProjectiveEnvelope_source
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable
      (fun source : U08.BetaPrimeGaussianSource N K ↦
        h13BetaPrimeScaleTwoProjectiveEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source))
      (realBetaPrimeGaussianSourceLaw N K) := by
  have hOneSq :=
    (U08.integrable_betaPrimeTraceOneSource_sq_internal hgap).div_const
      ((N : ℝ) ^ 2)
  have hTwo :=
    (U08.integrable_betaPrimeTraceTwoSource_internal hgap).div_const
      ((N : ℝ) ^ 2)
  have hOneFourth :=
    (U08.integrable_betaPrimeTraceOneSource_fourth_h14 hgap).div_const
      ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)
  have hTwoSq :=
    (U08.integrable_betaPrimeTraceTwoSource_square_h14 hgap).div_const
      ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)
  change Integrable (fun source : U08.BetaPrimeGaussianSource N K ↦
    8192 *
      (betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2 +
        betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2 +
        betaPrimeTraceOneSource N K source ^ 4 /
          ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
        betaPrimeTraceTwoSource N K source ^ 2 /
          ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)))
    (realBetaPrimeGaussianSourceLaw N K)
  exact (((hOneSq.add hTwo).add hOneFourth).add hTwoSq).const_mul 8192

theorem integrable_h13BetaPrimeScaleTwoProjectiveEnvelope
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    Integrable (h13BetaPrimeScaleTwoProjectiveEnvelope N K)
      (betaPrimeTraceFourLaw N K) := by
  unfold betaPrimeTraceFourLaw
  apply (integrable_map_measure
    (measurable_h13BetaPrimeScaleTwoProjectiveEnvelope N K).aestronglyMeasurable
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable).2
  exact integrable_h13BetaPrimeScaleTwoProjectiveEnvelope_source hgap

theorem integral_h13BetaPrimeScaleTwoProjectiveEnvelope_source_eq
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    (∫ source,
        h13BetaPrimeScaleTwoProjectiveEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source)
        ∂realBetaPrimeGaussianSourceLaw N K) =
      8192 *
        ((∫ source, betaPrimeTraceOneSource N K source ^ 2
            ∂realBetaPrimeGaussianSourceLaw N K) / (N : ℝ) ^ 2 +
          (∫ source, betaPrimeTraceTwoSource N K source
            ∂realBetaPrimeGaussianSourceLaw N K) / (N : ℝ) ^ 2 +
          (∫ source, betaPrimeTraceOneSource N K source ^ 4
            ∂realBetaPrimeGaussianSourceLaw N K) /
              ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
          (∫ source, betaPrimeTraceTwoSource N K source ^ 2
            ∂realBetaPrimeGaussianSourceLaw N K) /
              ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)) := by
  have hOne :=
    (U08.integrable_betaPrimeTraceOneSource_sq_internal hgap).div_const
      ((N : ℝ) ^ 2)
  have hTwo :=
    (U08.integrable_betaPrimeTraceTwoSource_internal hgap).div_const
      ((N : ℝ) ^ 2)
  have hOneFourth :=
    (U08.integrable_betaPrimeTraceOneSource_fourth_h14 hgap).div_const
      ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)
  have hTwoSq :=
    (U08.integrable_betaPrimeTraceTwoSource_square_h14 hgap).div_const
      ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)
  change (∫ source,
      8192 *
        (betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2 +
          betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2 +
          betaPrimeTraceOneSource N K source ^ 4 /
            ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
          betaPrimeTraceTwoSource N K source ^ 2 /
            ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))
      ∂realBetaPrimeGaussianSourceLaw N K) = _
  have hInner :
      (∫ source,
          betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2 +
            betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2 +
            betaPrimeTraceOneSource N K source ^ 4 /
              ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
            betaPrimeTraceTwoSource N K source ^ 2 /
              ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)
          ∂realBetaPrimeGaussianSourceLaw N K) =
        (∫ source, betaPrimeTraceOneSource N K source ^ 2
          ∂realBetaPrimeGaussianSourceLaw N K) / (N : ℝ) ^ 2 +
          (∫ source, betaPrimeTraceTwoSource N K source
            ∂realBetaPrimeGaussianSourceLaw N K) / (N : ℝ) ^ 2 +
          (∫ source, betaPrimeTraceOneSource N K source ^ 4
            ∂realBetaPrimeGaussianSourceLaw N K) /
              ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
          (∫ source, betaPrimeTraceTwoSource N K source ^ 2
            ∂realBetaPrimeGaussianSourceLaw N K) /
              ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2) := by
    calc
      _ =
          (∫ source,
              betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2 +
                betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2 +
                betaPrimeTraceOneSource N K source ^ 4 /
                  ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)
              ∂realBetaPrimeGaussianSourceLaw N K) +
            ∫ source, betaPrimeTraceTwoSource N K source ^ 2 /
              ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)
              ∂realBetaPrimeGaussianSourceLaw N K :=
        integral_add ((hOne.add hTwo).add hOneFourth) hTwoSq
      _ =
          ((∫ source,
              betaPrimeTraceOneSource N K source ^ 2 / (N : ℝ) ^ 2 +
                betaPrimeTraceTwoSource N K source / (N : ℝ) ^ 2
              ∂realBetaPrimeGaussianSourceLaw N K) +
            ∫ source, betaPrimeTraceOneSource N K source ^ 4 /
              ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)
              ∂realBetaPrimeGaussianSourceLaw N K) +
            ∫ source, betaPrimeTraceTwoSource N K source ^ 2 /
              ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)
              ∂realBetaPrimeGaussianSourceLaw N K := by
        exact congrArg
          (fun x : ℝ ↦ x +
            ∫ source, betaPrimeTraceTwoSource N K source ^ 2 /
              ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)
              ∂realBetaPrimeGaussianSourceLaw N K)
          (integral_add (hOne.add hTwo) hOneFourth)
      _ =
          (((∫ source, betaPrimeTraceOneSource N K source ^ 2 /
                (N : ℝ) ^ 2 ∂realBetaPrimeGaussianSourceLaw N K) +
              ∫ source, betaPrimeTraceTwoSource N K source /
                (N : ℝ) ^ 2 ∂realBetaPrimeGaussianSourceLaw N K) +
            ∫ source, betaPrimeTraceOneSource N K source ^ 4 /
              ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)
              ∂realBetaPrimeGaussianSourceLaw N K) +
            ∫ source, betaPrimeTraceTwoSource N K source ^ 2 /
              ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)
              ∂realBetaPrimeGaussianSourceLaw N K := by
        exact congrArg
          (fun x : ℝ ↦
            (x +
              ∫ source, betaPrimeTraceOneSource N K source ^ 4 /
                ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)
                ∂realBetaPrimeGaussianSourceLaw N K) +
              ∫ source, betaPrimeTraceTwoSource N K source ^ 2 /
                ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)
                ∂realBetaPrimeGaussianSourceLaw N K)
          (integral_add hOne hTwo)
      _ = _ := by
        rw [integral_div, integral_div, integral_div, integral_div]
  rw [integral_const_mul]
  exact congrArg (fun x : ℝ ↦ 8192 * x) hInner

theorem integral_h13BetaPrimeScaleTwoProjectiveEnvelope_le_exact
    {N K : ℕ} (hN : 2 ≤ N) (hdense : 16 * N ≤ K) :
    (∫ u, h13BetaPrimeScaleTwoProjectiveEnvelope N K u
      ∂betaPrimeTraceFourLaw N K) ≤
      h13ScaleTwoProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  have hmapMeas : AEMeasurable (realBetaPrimeTracePowerVector 4 N K)
      (realBetaPrimeGaussianSourceLaw N K) :=
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  have hEnvelopeMeas : AEStronglyMeasurable
      (h13BetaPrimeScaleTwoProjectiveEnvelope N K)
      (betaPrimeTraceFourLaw N K) :=
    (measurable_h13BetaPrimeScaleTwoProjectiveEnvelope N K).aestronglyMeasurable
  have hpush :
      (∫ u, h13BetaPrimeScaleTwoProjectiveEnvelope N K u
        ∂betaPrimeTraceFourLaw N K) =
      ∫ source,
        h13BetaPrimeScaleTwoProjectiveEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source)
        ∂realBetaPrimeGaussianSourceLaw N K := by
    unfold betaPrimeTraceFourLaw
    exact integral_map hmapMeas hEnvelopeMeas
  rw [hpush, integral_h13BetaPrimeScaleTwoProjectiveEnvelope_source_eq hgap]
  simpa only [h13ScaleTwoProjectiveEnvelopeConstant] using
    U08.h13ScaleTwoGaussianSourceExpectation_le_52204_internal hN hdense

theorem h13BetaPrimeScaleTwoProjectiveEnvelope_momentPackage_exact
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h13BetaPrimeScaleTwoProjectiveEnvelope N K)
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        (∫ u, h13BetaPrimeScaleTwoProjectiveEnvelope N K u
          ∂betaPrimeTraceFourLaw N K) ≤
          h13ScaleTwoProjectiveEnvelopeConstant * (N : ℝ) ^ 2) :=
  ⟨integrable_h13BetaPrimeScaleTwoProjectiveEnvelope hgap,
    fun hdense ↦ integral_h13BetaPrimeScaleTwoProjectiveEnvelope_le_exact
      hN hdense⟩

theorem h13BetaPrimeScaleTwoProjectiveEnvelope_comp_traceFour
    (N K : ℕ) (A : ConcreteMatrixState N) :
    h13BetaPrimeScaleTwoProjectiveEnvelope N K
        (concreteCOETracePowerVector 4 N K A) =
      h13ScaleTwoProjectiveEnvelope N K A := by
  change 8192 *
      (concreteBetaPrimeYTraceOne N K A ^ 2 / (N : ℝ) ^ 2 +
        concreteBetaPrimeYTraceTwo N K A / (N : ℝ) ^ 2 +
        concreteBetaPrimeYTraceOne N K A ^ 4 /
          ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
        concreteBetaPrimeYTraceTwo N K A ^ 2 /
          ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)) = _
  rw [concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne,
    concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo]
  rfl

theorem h13ScaleTwoProjectiveEnvelope_momentPackage_of_H6
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K) :
    Integrable (h13ScaleTwoProjectiveEnvelope N K)
        (higherScoreMatrixLaw N K) ∧
      (16 * N ≤ K →
        (∫ A, h13ScaleTwoProjectiveEnvelope N K A
            ∂higherScoreMatrixLaw N K) ≤
          h13ScaleTwoProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) := higherScoreMatrixLaw N K
  let f : ConcreteMatrixState N → Fin 4 → ℝ :=
    concreteCOETracePowerVector 4 N K
  let b : (Fin 4 → ℝ) → ℝ :=
    h13BetaPrimeScaleTwoProjectiveEnvelope N K
  have hBeta := h13BetaPrimeScaleTwoProjectiveEnvelope_momentPackage_exact
    hN hgap
  have hf : AEMeasurable f μ := by
    simpa only [f, μ, higherScoreMatrixLaw] using
      (measurable_concreteCOETracePowerVector_internal 4 N K).aemeasurable
  have hmap : Measure.map f μ = betaPrimeTraceFourLaw N K := by
    simpa only [f, μ, higherScoreMatrixLaw] using hH6
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
  have hfun : b ∘ f = h13ScaleTwoProjectiveEnvelope N K := by
    funext A
    exact h13BetaPrimeScaleTwoProjectiveEnvelope_comp_traceFour N K A
  constructor
  · rw [← hfun]
    exact hPullInt
  · intro hdense
    rw [← hfun, hPullIntegral]
    simpa only [b] using hBeta.2 hdense

theorem h13ScaleTwoProjectiveEnvelope_momentPackage_A2A3
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h13ScaleTwoProjectiveEnvelope N K)
        (higherScoreMatrixLaw N K) ∧
      (16 * N ≤ K →
        (∫ A, h13ScaleTwoProjectiveEnvelope N K A
            ∂higherScoreMatrixLaw N K) ≤
          h13ScaleTwoProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  have hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K := by
    simpa only [betaPrimeTraceFourLaw] using
      (coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
        (r := 4) (by omega : 1 ≤ N) (by omega : 2 * N ≤ K))
  exact h13ScaleTwoProjectiveEnvelope_momentPackage_of_H6 hN hgap hH6

/-! ## Exact deterministic scale-two contraction -/

theorem h13ScaleTwoProjectiveEnvelope_eq_supportBasis
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    let C := unscaleCOECorner K A
    let Z := h13LedgerZ C
    let c := concreteCOEExponent N K
    h13ScaleTwoProjectiveEnvelope N K A =
      8192 * c ^ 2 *
        (((Matrix.trace Z).re ^ 2 + (Matrix.trace (Z ^ 2)).re) /
            (N : ℝ) ^ 2 +
          (Matrix.trace Z).re ^ 4 / (N : ℝ) ^ 4 +
          (Matrix.trace (Z ^ 2)).re ^ 2 / (N : ℝ) ^ 2) := by
  let C := unscaleCOECorner K A
  let Z := h13LedgerZ C
  let c := concreteCOEExponent N K
  have hc : 0 < c := by
    simpa only [c] using concreteCOEExponent_pos_of_higherScoreGap hgap
  have hY : concreteCOEY N K A = ((c : ℝ) : ℂ) • Z := by rfl
  have ht1 : concreteCOETraceOne N K A = c * (Matrix.trace Z).re := by
    unfold concreteCOETraceOne concreteRealTrace
    rw [hY, Matrix.trace_smul]
    simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  have ht2 : concreteCOETraceTwo N K A =
      c ^ 2 * (Matrix.trace (Z ^ 2)).re := by
    unfold concreteCOETraceTwo concreteRealTrace
    rw [hY]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    rw [show Z * Z = Z ^ 2 by noncomm_ring]
    have hcim : (((c : ℂ) * (c : ℂ)).im) = 0 := by simp
    rw [hcim, zero_mul, sub_zero]
    ring
  unfold h13ScaleTwoProjectiveEnvelope
  rw [ht1, ht2]
  rw [show concreteCOEExponent N K = c by rfl]
  dsimp only
  field_simp [ne_of_gt hc]
  ring

/-- The literal fixed-sphere H13 contraction with its exact coefficient
`16 * 512 = 8192`. -/
theorem h13OneThreeScaleTwo_fixedMatrix_package
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    Integrable (fun v : ComplexUnitSphere N ↦
      concreteCenteredEll 1 N K (A, v) *
        concreteCenteredEll 3 N K (A, v))
        (higherScoreSphereLaw N) ∧
      (∫ v, ‖concreteCenteredEll 1 N K (A, v) *
          concreteCenteredEll 3 N K (A, v)‖
        ∂higherScoreSphereLaw N) ≤
          h13ScaleTwoProjectiveEnvelope N K A := by
  let C := unscaleCOECorner K A
  let Z := h13LedgerZ C
  let Y := concreteCOEY N K A
  let c := concreteCOEExponent N K
  let q : ComplexUnitSphere N → ℂ := fun v ↦
    complexCenteredProjectiveTracePair v Z
  let full : ComplexUnitSphere N → ℂ := fun v ↦
    h13FullSixWordProjectiveExpansion v C
  let realProduct : ComplexUnitSphere N → ℝ := fun v ↦
    (q v).re * (full v).re
  let ledger : ComplexUnitSphere N → ℝ := fun v ↦
    -8 * c * h13OneThreeTraceWordLedger
      (concreteCenteredOrbitalDirection N v) C Y
  let basis : ℝ :=
    (((Matrix.trace Z).re ^ 2 + (Matrix.trace (Z ^ 2)).re) /
        (N : ℝ) ^ 2 +
      (Matrix.trace Z).re ^ 4 / (N : ℝ) ^ 4 +
      (Matrix.trace (Z ^ 2)).re ^ 2 / (N : ℝ) ^ 2)
  have hc : 0 < c := by
    simpa only [c] using concreteCOEExponent_pos_of_higherScoreGap hgap
  have hZ : Z.PosSemidef := by
    simpa only [Z, C] using h13LedgerZ_posSemidef C hsupport
  have hfull := centeredPair_mul_h13Full_support_package_of_pureIntegrable
    hN C hsymm hsupport
      (integrable_centeredPair_mul_pureSixWord_h13 hN Z hZ)
  dsimp only at hfull
  have hfullInt : Integrable (fun v ↦ q v * full v)
      (higherScoreSphereLaw N) := by
    simpa only [q, full, Z, C] using hfull.1
  have hfullBound :
      (∫ v, ‖q v * full v‖ ∂higherScoreSphereLaw N) ≤
        512 * basis := by
    simpa only [q, full, Z, C, basis] using hfull.2
  have hqim (v : ComplexUnitSphere N) : (q v).im = 0 := by
    dsimp only [q]
    exact complexCenteredProjectiveTracePair_im_zero_internal v Z
      hZ.isHermitian
  have hrealInt : Integrable realProduct (higherScoreSphereLaw N) := by
    have H := hfullInt.re
    apply H.congr
    filter_upwards [] with v
    dsimp only [realProduct]
    change (q v * full v).re = (q v).re * (full v).re
    rw [Complex.mul_re, hqim v, zero_mul, sub_zero]
  have hY : Y = ((c : ℝ) : ℂ) • Z := by rfl
  have hledger (v : ComplexUnitSphere N) :
      ledger v = 16 * c ^ 2 * realProduct v := by
    dsimp only [ledger]
    rw [negEightExponent_mul_h13Ledger_eq_fullProjectivePolynomial
      v C Y hsupport]
    change 16 * concreteCOEExponent N K *
      ((complexCenteredProjectiveTracePair v Y).re * (full v).re) = _
    rw [show concreteCOEExponent N K = c by rfl]
    rw [hY, complexCenteredProjectiveTracePair_smul]
    dsimp only [realProduct, q]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    ring
  have hledgerInt : Integrable ledger (higherScoreSphereLaw N) := by
    have H := hrealInt.const_mul (16 * c ^ 2)
    apply H.congr
    filter_upwards [] with v
    exact (hledger v).symm
  have hscale : 0 ≤ 16 * c ^ 2 := by positivity
  have hpoint (v : ComplexUnitSphere N) :
      ‖ledger v‖ ≤ (16 * c ^ 2) * ‖q v * full v‖ := by
    rw [hledger v]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hscale, abs_mul,
      norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul (Complex.abs_re_le_norm (q v))
        (Complex.abs_re_le_norm (full v)) (abs_nonneg _) (norm_nonneg _))
      hscale
  have hmajorInt : Integrable
      (fun v ↦ (16 * c ^ 2) * ‖q v * full v‖)
      (higherScoreSphereLaw N) :=
    hfullInt.norm.const_mul (16 * c ^ 2)
  have hmono :
      (∫ v, ‖ledger v‖ ∂higherScoreSphereLaw N) ≤
        ∫ v, (16 * c ^ 2) * ‖q v * full v‖
          ∂higherScoreSphereLaw N :=
    integral_mono hledgerInt.norm hmajorInt hpoint
  have hEnvelope := h13ScaleTwoProjectiveEnvelope_eq_supportBasis
    hN hgap A hsupport
  dsimp only at hEnvelope
  have hscoreEq : (fun v : ComplexUnitSphere N ↦
      concreteCenteredEll 1 N K (A, v) *
        concreteCenteredEll 3 N K (A, v)) = ledger := by
    funext v
    simpa only [ledger, C, Y] using
      concreteCenteredEll_one_mul_three_eq_traceWordLedger_h13_internal
        hN hgap A v hsymm hsupport
  have hledgerBound :
      (∫ v, ‖ledger v‖ ∂higherScoreSphereLaw N) ≤
        h13ScaleTwoProjectiveEnvelope N K A := by
    calc
      _ ≤ ∫ v, (16 * c ^ 2) * ‖q v * full v‖
          ∂higherScoreSphereLaw N := hmono
      _ = (16 * c ^ 2) *
          (∫ v, ‖q v * full v‖ ∂higherScoreSphereLaw N) := by
        rw [integral_const_mul]
      _ ≤ (16 * c ^ 2) * (512 * basis) :=
        mul_le_mul_of_nonneg_left hfullBound hscale
      _ = 8192 * c ^ 2 * basis := by ring
      _ = h13ScaleTwoProjectiveEnvelope N K A := hEnvelope.symm
  constructor
  · rw [hscoreEq]
    exact hledgerInt
  · rw [show (fun v ↦ ‖concreteCenteredEll 1 N K (A, v) *
        concreteCenteredEll 3 N K (A, v)‖) = fun v ↦ ‖ledger v‖ by
      funext v
      exact congrArg norm (congrFun hscoreEq v)]
    exact hledgerBound

/-! ## Product-law endpoint -/

theorem centeredLogScore_oneThree_momentPackage_scaleTwo_NGeTwo_A1A2A3A4
    {N K : ℕ} (hN : 2 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h13ScaleTwoProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) := higherScoreMatrixLaw N K
  let sphere : Measure (ComplexUnitSphere N) := higherScoreSphereLaw N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ := fun p ↦
    concreteCenteredEll 1 N K p * concreteCenteredEll 3 N K p
  let envelope : ConcreteMatrixState N → ℝ :=
    h13ScaleTwoProjectiveEnvelope N K
  have hNOne : 1 ≤ N := by omega
  letI : IsProbabilityMeasure μ :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hNOne
  have hscoreMeas : AEStronglyMeasurable score (μ.prod sphere) :=
    ((measurable_concreteCenteredEll_one (N := N) (K := K) hNOne).mul
      (measurable_concreteCenteredEll_three (N := N) (K := K) hNOne))
      |>.aestronglyMeasurable
  have hSupport : ∀ᵐ A ∂μ,
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
    simpa only [μ, higherScoreMatrixLaw] using
      friedmanMello1985_scaledCOECorner_ae_support_from_density
        hNOne (by omega : 2 * N ≤ K)
  have hSlices : ∀ᵐ A ∂μ,
      Integrable (fun v ↦ score (A, v)) sphere ∧
        (∫ v, ‖score (A, v)‖ ∂sphere) ≤ envelope A := by
    filter_upwards [hSupport] with A hA
    simpa only [score, sphere, envelope] using
      h13OneThreeScaleTwo_fixedMatrix_package hNOne hgap A hA.1 hA.2
  have hEnvelope := h13ScaleTwoProjectiveEnvelope_momentPackage_A2A3 hN hgap
  have hEnvelopeInt : Integrable envelope μ := by
    simpa only [envelope, μ, higherScoreMatrixLaw] using hEnvelope.1
  have hInnerMeas : AEStronglyMeasurable
      (fun A ↦ ∫ v, ‖score (A, v)‖ ∂sphere) μ :=
    hscoreMeas.norm.integral_prod_right'
  have hInnerInt : Integrable
      (fun A ↦ ∫ v, ‖score (A, v)‖ ∂sphere) μ := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [hSlices] with A hA
    have hInnerNonneg : 0 ≤ ∫ v, ‖score (A, v)‖ ∂sphere :=
      integral_nonneg fun _ ↦ norm_nonneg _
    have hEnvelopeNonneg : 0 ≤ envelope A := hInnerNonneg.trans hA.2
    rw [Real.norm_eq_abs, abs_of_nonneg hInnerNonneg,
      Real.norm_eq_abs, abs_of_nonneg hEnvelopeNonneg]
    exact hA.2
  have hscoreInt : Integrable score (μ.prod sphere) := by
    apply (integrable_prod_iff hscoreMeas).2
    exact ⟨hSlices.mono fun _ hA ↦ hA.1, hInnerInt⟩
  constructor
  · have hmem : MemLp score 1 (μ.prod sphere) :=
      memLp_one_iff_integrable.mpr hscoreInt
    simpa only [score, μ, sphere, higherScoreMatrixLaw,
      higherScoreSphereLaw, concreteCenteredScoreProductLaw] using hmem
  · intro hdense
    have hbound : lpNorm score 1 (μ.prod sphere) ≤
        h13ScaleTwoProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
      calc
        lpNorm score 1 (μ.prod sphere) =
            ∫ A, ∫ v, ‖score (A, v)‖ ∂sphere ∂μ := by
          rw [lpNorm_one_eq_integral_norm hscoreMeas]
          exact integral_prod (fun p ↦ ‖score p‖) hscoreInt.norm
        _ ≤ ∫ A, envelope A ∂μ := by
          apply integral_mono_ae hInnerInt hEnvelopeInt
          filter_upwards [hSlices] with A hA
          exact hA.2
        _ ≤ h13ScaleTwoProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
          simpa only [envelope, μ, higherScoreMatrixLaw] using
            hEnvelope.2 hdense
    simpa only [score, μ, sphere, higherScoreMatrixLaw,
      higherScoreSphereLaw, concreteCenteredScoreProductLaw] using hbound

/-- All-positive-dimensional H13 package with exact constant `52204`. -/
theorem centeredLogScore_oneThree_momentPackage_scaleTwo_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h13ScaleTwoProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  by_cases hOne : N = 1
  · subst N
    have hzero : (fun p ↦ concreteCenteredEll 1 1 K p *
        concreteCenteredEll 3 1 K p) = 0 := by
      funext p
      rw [show concreteCenteredEll 1 1 K p = 0 by
        exact concreteCenteredLogScore_fin_one_eq_zero (by omega) p.2 p.1]
      simp
    rw [hzero]
    constructor
    · exact MemLp.zero'
    · intro _
      rw [lpNorm_zero]
      norm_num [h13ScaleTwoProjectiveEnvelopeConstant]
  · exact centeredLogScore_oneThree_momentPackage_scaleTwo_NGeTwo_A1A2A3A4
      (by omega) hgap

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
