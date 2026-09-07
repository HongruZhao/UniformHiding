import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_ExactMomentClosureA4
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreLowMeasurability

/-!
# Exact H12 centered-first-score moment endpoint

This downstream adapter completes the literal H12 endpoint.  The fixed-matrix
projective fourth-moment estimate is supplied by `H12_ExactMomentClosureA4`.
The checked H14 fourth-Wick producer and the A4 denominator contraction give
the two source moments needed for its radial envelope; exact H6 transports
that envelope to the scaled COE law, and approved A1 supplies the almost-
everywhere support used in the final Fubini argument.

No legacy H12 moment declaration is used.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration
open U08

set_option maxHeartbeats 3600000

/-! ## Radial envelope on the beta-prime trace law -/

/-- The beta-prime trace-vector version of the fixed-matrix H12 envelope. -/
def h12BetaPrimeProjectiveFourthEnvelope (N K : ℕ)
    (u : Fin 4 → ℝ) : ℝ :=
  1024 *
      (betaPrimeYTraceTwo N K u -
        (N : ℝ)⁻¹ * betaPrimeYTraceOne N K u ^ 2) ^ 2 /
    (N : ℝ) ^ 4

theorem h12BetaPrimeProjectiveFourthEnvelope_nonneg
    (N K : ℕ) (u : Fin 4 → ℝ) :
    0 ≤ h12BetaPrimeProjectiveFourthEnvelope N K u := by
  unfold h12BetaPrimeProjectiveFourthEnvelope
  positivity

private theorem betaPrimeYTraceOne_comp_concreteTraceFour_h12_low
    (N K : ℕ) (A : ConcreteMatrixState N) :
    betaPrimeYTraceOne N K (concreteCOETracePowerVector 4 N K A) =
      concreteCOETraceOne N K A := by
  unfold betaPrimeYTraceOne concreteCOETracePowerVector concreteCOETraceOne
    concreteCOEY concreteRealTrace
  simp [pow_succ, Complex.mul_re]

private theorem betaPrimeYTraceTwo_comp_concreteTraceFour_h12_low
    (N K : ℕ) (A : ConcreteMatrixState N) :
    betaPrimeYTraceTwo N K (concreteCOETracePowerVector 4 N K A) =
      concreteCOETraceTwo N K A := by
  unfold betaPrimeYTraceTwo concreteCOETracePowerVector concreteCOETraceTwo
    concreteCOEY concreteRealTrace
  simp [pow_succ, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_smul, Complex.mul_re]

/-- Pulling the beta-prime radial envelope back along the concrete four-trace
map gives the literal fixed-matrix envelope definitionally. -/
theorem h12_betaPrimeProjectiveFourthEnvelope_comp_traceFour_internal
    (N K : ℕ) (A : ConcreteMatrixState N) :
    h12BetaPrimeProjectiveFourthEnvelope N K
        (concreteCOETracePowerVector 4 N K A) =
      h12ProjectiveFourthEnvelope N K A := by
  unfold h12BetaPrimeProjectiveFourthEnvelope
    h12ProjectiveFourthEnvelope h12ConcreteTracelessBracket
  rw [betaPrimeYTraceOne_comp_concreteTraceFour_h12_low,
    betaPrimeYTraceTwo_comp_concreteTraceFour_h12_low]

private theorem measurable_h12BetaPrimeProjectiveFourthEnvelope
    (N K : ℕ) :
    Measurable (h12BetaPrimeProjectiveFourthEnvelope N K) := by
  unfold h12BetaPrimeProjectiveFourthEnvelope betaPrimeYTraceOne
    betaPrimeYTraceTwo
  fun_prop

/-- Elementary square domination used before integrating the radial
envelope.  Its right side involves exactly the two moments produced by the
checked fourth-Wick calculation. -/
private theorem h12BetaPrimeProjectiveFourthEnvelope_le_sourceMajorant
    {N K : ℕ} (hN : 1 ≤ N) (source : BetaPrimeGaussianSource N K) :
    h12BetaPrimeProjectiveFourthEnvelope N K
        (realBetaPrimeTracePowerVector 4 N K source) ≤
      (2048 / (N : ℝ) ^ 4) *
        (betaPrimeTraceTwoSource N K source ^ 2 +
          betaPrimeTraceOneSource N K source ^ 4 / (N : ℝ) ^ 2) := by
  let n : ℝ := N
  let x : ℝ := betaPrimeTraceTwoSource N K source
  let y : ℝ := betaPrimeTraceOneSource N K source
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < N by omega)
  have hsq : (x - n⁻¹ * y ^ 2) ^ 2 ≤
      2 * (x ^ 2 + y ^ 4 / n ^ 2) := by
    have hbase := sq_nonneg (x + n⁻¹ * y ^ 2)
    field_simp [ne_of_gt hn] at hbase ⊢
    nlinarith
  change 1024 * (x - n⁻¹ * y ^ 2) ^ 2 / n ^ 4 ≤
    (2048 / n ^ 4) * (x ^ 2 + y ^ 4 / n ^ 2)
  calc
    1024 * (x - n⁻¹ * y ^ 2) ^ 2 / n ^ 4 ≤
        1024 * (2 * (x ^ 2 + y ^ 4 / n ^ 2)) / n ^ 4 := by
      gcongr
    _ = (2048 / n ^ 4) * (x ^ 2 + y ^ 4 / n ^ 2) := by ring

/-- Qualitative integrability of the H12 radial envelope on the literal
independent Gaussian beta-prime source. -/
theorem integrable_h12BetaPrimeProjectiveFourthEnvelope_source_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable
      (h12BetaPrimeProjectiveFourthEnvelope N K ∘
        realBetaPrimeTracePowerVector 4 N K)
      (realBetaPrimeGaussianSourceLaw N K) := by
  let n : ℝ := N
  let sourceLaw := realBetaPrimeGaussianSourceLaw N K
  let tOne : BetaPrimeGaussianSource N K → ℝ :=
    betaPrimeTraceOneSource N K
  let tTwo : BetaPrimeGaussianSource N K → ℝ :=
    betaPrimeTraceTwoSource N K
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < N by omega)
  have hOne : Integrable (fun source ↦ tOne source ^ 4) sourceLaw := by
    simpa only [tOne, sourceLaw] using
      (integrable_betaPrimeTraceOneSource_fourth_h14_low
        (N := N) (K := K) hgap)
  have hTwo : Integrable (fun source ↦ tTwo source ^ 2) sourceLaw := by
    simpa only [tTwo, sourceLaw] using
      (integrable_betaPrimeTraceTwoSource_square_h14_low
        (N := N) (K := K) hgap)
  have hOneDiv : Integrable
      (fun source ↦ tOne source ^ 4 / n ^ 2) sourceLaw :=
    hOne.div_const (n ^ 2)
  have hMajor : Integrable
      (fun source ↦ (2048 / n ^ 4) *
        (tTwo source ^ 2 + tOne source ^ 4 / n ^ 2)) sourceLaw :=
    (hTwo.add hOneDiv).const_mul (2048 / n ^ 4)
  have hEnvelopeMeas : AEStronglyMeasurable
      (h12BetaPrimeProjectiveFourthEnvelope N K ∘
        realBetaPrimeTracePowerVector 4 N K) sourceLaw :=
    (measurable_h12BetaPrimeProjectiveFourthEnvelope N K).aestronglyMeasurable
      |>.comp_aemeasurable
        (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  apply Integrable.mono' hMajor hEnvelopeMeas
  filter_upwards [] with source
  change ‖h12BetaPrimeProjectiveFourthEnvelope N K
      (realBetaPrimeTracePowerVector 4 N K source)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (h12BetaPrimeProjectiveFourthEnvelope_nonneg N K _)]
  simpa only [n, tOne, tTwo] using
    h12BetaPrimeProjectiveFourthEnvelope_le_sourceMajorant hN source

/-- The source envelope has the sharp explicit bound produced by the radial
calculation, before relaxation to the common public fourth-moment constant. -/
theorem integral_h12BetaPrimeProjectiveFourthEnvelope_source_le_strong_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hdense : 16 * N ≤ K) :
    (∫ source,
        h12BetaPrimeProjectiveFourthEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source)
        ∂(realBetaPrimeGaussianSourceLaw N K)) ≤
      (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 := by
  let n : ℝ := N
  let sourceLaw := realBetaPrimeGaussianSourceLaw N K
  let tOne : BetaPrimeGaussianSource N K → ℝ :=
    betaPrimeTraceOneSource N K
  let tTwo : BetaPrimeGaussianSource N K → ℝ :=
    betaPrimeTraceTwoSource N K
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (show 0 < N by omega)
  have hOne : Integrable (fun source ↦ tOne source ^ 4) sourceLaw := by
    simpa only [tOne, sourceLaw] using
      (integrable_betaPrimeTraceOneSource_fourth_h14_low
        (N := N) (K := K) hgap)
  have hTwo : Integrable (fun source ↦ tTwo source ^ 2) sourceLaw := by
    simpa only [tTwo, sourceLaw] using
      (integrable_betaPrimeTraceTwoSource_square_h14_low
        (N := N) (K := K) hgap)
  have hOneDiv : Integrable
      (fun source ↦ tOne source ^ 4 / n ^ 2) sourceLaw :=
    hOne.div_const (n ^ 2)
  have hMajor : Integrable
      (fun source ↦ (2048 / n ^ 4) *
        (tTwo source ^ 2 + tOne source ^ 4 / n ^ 2)) sourceLaw :=
    (hTwo.add hOneDiv).const_mul (2048 / n ^ 4)
  have hEnvelopeInt : Integrable
      (fun source ↦ h12BetaPrimeProjectiveFourthEnvelope N K
        (realBetaPrimeTracePowerVector 4 N K source)) sourceLaw := by
    have h := integrable_h12BetaPrimeProjectiveFourthEnvelope_source_internal
      hN hgap
    change Integrable
      (fun source ↦ h12BetaPrimeProjectiveFourthEnvelope N K
        (realBetaPrimeTracePowerVector 4 N K source)) sourceLaw at h
    exact h
  have hPoint : ∀ source,
      h12BetaPrimeProjectiveFourthEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source) ≤
        (2048 / n ^ 4) *
          (tTwo source ^ 2 + tOne source ^ 4 / n ^ 2) := by
    intro source
    simpa only [n, tOne, tTwo] using
      h12BetaPrimeProjectiveFourthEnvelope_le_sourceMajorant hN source
  have hMono :
      (∫ source,
          h12BetaPrimeProjectiveFourthEnvelope N K
            (realBetaPrimeTracePowerVector 4 N K source) ∂sourceLaw) ≤
        ∫ source, (2048 / n ^ 4) *
          (tTwo source ^ 2 + tOne source ^ 4 / n ^ 2) ∂sourceLaw :=
    integral_mono hEnvelopeInt hMajor hPoint
  have hSource := h14_explicitGaussianFourthSourceBounds_conditional_low
    hgap (h14FiniteGaussianFourthWickFormula_internal N K)
      (h12DenominatorFourthTracePolynomialBounds_of_A4_internal N K)
  have hOneBound :
      (∫ source, tOne source ^ 4 ∂sourceLaw) ≤
        (2 : ℝ) ^ 16 * n ^ 8 := by
    simpa only [tOne, sourceLaw, n] using hSource.1 hdense
  have hTwoBound :
      (∫ source, tTwo source ^ 2 ∂sourceLaw) ≤
        (2 : ℝ) ^ 16 * n ^ 6 := by
    simpa only [tTwo, sourceLaw, n] using hSource.2 hdense
  have hOneDivBound :
      (∫ source, tOne source ^ 4 ∂sourceLaw) / n ^ 2 ≤
        ((2 : ℝ) ^ 16 * n ^ 8) / n ^ 2 := by
    exact div_le_div_of_nonneg_right hOneBound (sq_nonneg n)
  calc
    (∫ source,
        h12BetaPrimeProjectiveFourthEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source) ∂sourceLaw) ≤
        ∫ source, (2048 / n ^ 4) *
          (tTwo source ^ 2 + tOne source ^ 4 / n ^ 2) ∂sourceLaw := hMono
    _ = (2048 / n ^ 4) *
          ((∫ source, tTwo source ^ 2 ∂sourceLaw) +
            (∫ source, tOne source ^ 4 ∂sourceLaw) / n ^ 2) := by
      rw [integral_const_mul, integral_add hTwo hOneDiv, integral_div]
    _ ≤ (2048 / n ^ 4) *
          ((2 : ℝ) ^ 16 * n ^ 6 +
            ((2 : ℝ) ^ 16 * n ^ 8) / n ^ 2) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hTwoBound hOneDivBound) (by positivity)
    _ = (2 : ℝ) ^ 28 * n ^ 2 := by
      field_simp [ne_of_gt hn]
      ring

/-- Publicly relaxed form of the strong source estimate. -/
theorem integral_h12BetaPrimeProjectiveFourthEnvelope_source_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hdense : 16 * N ≤ K) :
    (∫ source,
        h12BetaPrimeProjectiveFourthEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source)
        ∂(realBetaPrimeGaussianSourceLaw N K)) ≤
      centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
  calc
    (∫ source,
        h12BetaPrimeProjectiveFourthEnvelope N K
          (realBetaPrimeTracePowerVector 4 N K source)
        ∂(realBetaPrimeGaussianSourceLaw N K)) ≤
        (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 :=
      integral_h12BetaPrimeProjectiveFourthEnvelope_source_le_strong_internal
        hN hgap hdense
    _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg (N : ℝ))
      norm_num [centeredLogScoreFourthMomentConstant,
        denseClassicalMomentConstant]

/-- Moment package for the radial H12 envelope on the exposed beta-prime
four-trace law. -/
theorem h12BetaPrimeProjectiveFourthEnvelope_momentPackage_strong_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h12BetaPrimeProjectiveFourthEnvelope N K)
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        (∫ u, h12BetaPrimeProjectiveFourthEnvelope N K u
          ∂(betaPrimeTraceFourLaw N K)) ≤
          (2 : ℝ) ^ 28 * (N : ℝ) ^ 2) := by
  have hMap : AEMeasurable (realBetaPrimeTracePowerVector 4 N K)
      (realBetaPrimeGaussianSourceLaw N K) :=
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
  have hEnvelopeMeas : AEStronglyMeasurable
      (h12BetaPrimeProjectiveFourthEnvelope N K)
      (betaPrimeTraceFourLaw N K) :=
    (measurable_h12BetaPrimeProjectiveFourthEnvelope N K).aestronglyMeasurable
  constructor
  · unfold betaPrimeTraceFourLaw
    apply (integrable_map_measure
      (measurable_h12BetaPrimeProjectiveFourthEnvelope N K).aestronglyMeasurable
      hMap).2
    exact integrable_h12BetaPrimeProjectiveFourthEnvelope_source_internal
      hN hgap
  · intro hdense
    have hPush :
        (∫ u, h12BetaPrimeProjectiveFourthEnvelope N K u
          ∂(betaPrimeTraceFourLaw N K)) =
        ∫ source,
          h12BetaPrimeProjectiveFourthEnvelope N K
            (realBetaPrimeTracePowerVector 4 N K source)
          ∂(realBetaPrimeGaussianSourceLaw N K) := by
      unfold betaPrimeTraceFourLaw
      exact integral_map hMap hEnvelopeMeas
    rw [hPush]
    exact integral_h12BetaPrimeProjectiveFourthEnvelope_source_le_strong_internal
      hN hgap hdense

/-- Publicly relaxed beta-prime envelope package. -/
theorem h12BetaPrimeProjectiveFourthEnvelope_momentPackage_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h12BetaPrimeProjectiveFourthEnvelope N K)
        (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        (∫ u, h12BetaPrimeProjectiveFourthEnvelope N K u
          ∂(betaPrimeTraceFourLaw N K)) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hStrong :=
    h12BetaPrimeProjectiveFourthEnvelope_momentPackage_strong_internal hN hgap
  refine ⟨hStrong.1, ?_⟩
  intro hdense
  calc
    (∫ u, h12BetaPrimeProjectiveFourthEnvelope N K u
        ∂(betaPrimeTraceFourLaw N K)) ≤
        (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 := hStrong.2 hdense
    _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg (N : ℝ))
      norm_num [centeredLogScoreFourthMomentConstant,
        denseClassicalMomentConstant]

/-! ## Exact H6 transport to the concrete matrix law -/

/-- Exact H6 transports the radial H12 package to the literal scaled-COE
matrix law. -/
theorem h12ProjectiveFourthEnvelope_momentPackage_of_H6_strong_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K) :
    Integrable (h12ProjectiveFourthEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h12ProjectiveFourthEnvelope N K A
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) ≤
          (2 : ℝ) ^ 28 * (N : ℝ) ^ 2) := by
  let mu : Measure (ConcreteMatrixState N) :=
    concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K
  let f : ConcreteMatrixState N → Fin 4 → ℝ :=
    concreteCOETracePowerVector 4 N K
  let b : (Fin 4 → ℝ) → ℝ :=
    h12BetaPrimeProjectiveFourthEnvelope N K
  have hBeta :=
    h12BetaPrimeProjectiveFourthEnvelope_momentPackage_strong_internal
    hN hgap
  have hf : AEMeasurable f mu := by
    simpa only [f, mu] using
      (measurable_concreteCOETracePowerVector_internal 4 N K).aemeasurable
  have hmap : Measure.map f mu = betaPrimeTraceFourLaw N K := by
    simpa only [f, mu] using hH6
  have hbMap : AEStronglyMeasurable b (Measure.map f mu) := by
    rw [hmap]
    simpa only [b] using hBeta.1.aestronglyMeasurable
  have hPullInt : Integrable (b ∘ f) mu := by
    apply (integrable_map_measure hbMap hf).1
    simpa only [hmap, b] using hBeta.1
  have hPullIntegral :
      (∫ A, (b ∘ f) A ∂mu) =
        ∫ u, b u ∂(betaPrimeTraceFourLaw N K) := by
    calc
      (∫ A, (b ∘ f) A ∂mu) =
          ∫ u, b u ∂(Measure.map f mu) :=
        (integral_map hf hbMap).symm
      _ = ∫ u, b u ∂(betaPrimeTraceFourLaw N K) := by rw [hmap]
  have hfun : b ∘ f = h12ProjectiveFourthEnvelope N K := by
    funext A
    exact h12_betaPrimeProjectiveFourthEnvelope_comp_traceFour_internal N K A
  constructor
  · rw [← hfun]
    exact hPullInt
  · intro hdense
    rw [← hfun, hPullIntegral]
    simpa only [b] using hBeta.2 hdense

/-- Publicly relaxed exact-H6 transport. -/
theorem h12ProjectiveFourthEnvelope_momentPackage_of_H6_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K) :
    Integrable (h12ProjectiveFourthEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h12ProjectiveFourthEnvelope N K A
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hStrong := h12ProjectiveFourthEnvelope_momentPackage_of_H6_strong_internal
    hN hgap hH6
  refine ⟨hStrong.1, ?_⟩
  intro hdense
  calc
    (∫ A, h12ProjectiveFourthEnvelope N K A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) ≤
        (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 := hStrong.2 hdense
    _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg (N : ℝ))
      norm_num [centeredLogScoreFourthMomentConstant,
        denseClassicalMomentConstant]

/-- The H12 radial envelope package under the concrete matrix law, proved
from exact H6 (A2--A3) and the A4 fourth-moment input. -/
theorem h12ProjectiveFourthEnvelope_momentPackage_strong_proved_A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h12ProjectiveFourthEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h12ProjectiveFourthEnvelope N K A
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) ≤
          (2 : ℝ) ^ 28 * (N : ℝ) ^ 2) := by
  have hH6 :
      Measure.map (concreteCOETracePowerVector 4 N K)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        betaPrimeTraceFourLaw N K := by
    simpa only [betaPrimeTraceFourLaw] using
      (coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
        (r := 4) hN (by omega : 2 * N ≤ K))
  exact h12ProjectiveFourthEnvelope_momentPackage_of_H6_strong_internal
    hN hgap hH6

/-- Publicly relaxed H12 radial package under the concrete matrix law. -/
theorem h12ProjectiveFourthEnvelope_momentPackage_proved_A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h12ProjectiveFourthEnvelope N K)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      (16 * N ≤ K →
        (∫ A, h12ProjectiveFourthEnvelope N K A
          ∂(concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hStrong :=
    h12ProjectiveFourthEnvelope_momentPackage_strong_proved_A2A3A4 hN hgap
  refine ⟨hStrong.1, ?_⟩
  intro hdense
  calc
    (∫ A, h12ProjectiveFourthEnvelope N K A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)) ≤
        (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 := hStrong.2 hdense
    _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg (N : ℝ))
      norm_num [centeredLogScoreFourthMomentConstant,
        denseClassicalMomentConstant]

/-! ## Product-law H12 endpoint -/

/-- Strong literal H12 endpoint, exposing the `2^28` constant produced by the
radial calculation before public relaxation. -/
theorem centeredLogScore_oneFourth_momentPackage_strong_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
            (concreteCenteredScoreProductLaw N K) ≤
          (2 : ℝ) ^ 28 * (N : ℝ) ^ 2) := by
  let mu : Measure (ConcreteMatrixState N) :=
    concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K
  let sphere : Measure (ComplexUnitSphere N) :=
    complexUnitSphereProbabilityMeasure N
  let f : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 1 N K p ^ 4
  let envelope : ConcreteMatrixState N → ℝ :=
    h12ProjectiveFourthEnvelope N K
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hSupport : ∀ᵐ A ∂mu,
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
    simpa only [mu] using
      (friedmanMello1985_scaledCOECorner_ae_support_from_density
        hN (by omega : 2 * N ≤ K))
  have hSupportProd : ∀ᵐ p ∂(mu.prod sphere),
      (unscaleCOECorner K p.1).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K p.1) :=
    Measure.quasiMeasurePreserving_fst.ae hSupport
  have hfEq : f =ᵐ[mu.prod sphere]
      (fun p : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredRankOneFirstDensityScore N K p.2 p.1 ^ 4) := by
    filter_upwards [hSupportProd] with p hp
    have hell : concreteCenteredEll 1 N K p =
        concreteCenteredRankOneFirstDensityScore N K p.2 p.1 := by
      unfold concreteCenteredEll
      calc
        concreteCenteredLogScore 1 N K p.2 p.1 =
            concreteCenteredDensityScore 1 N K p.2 p.1 :=
          (coeCorner_centeredDensityScore_one_eq_logScore
            hN p.2 p.1 hp.2).symm
        _ = concreteCenteredRankOneFirstDensityScore N K p.2 p.1 :=
          coeCorner_centeredDensityScore_one_eq_explicit_external_derived
            hN hgap p.2 p.1 hp.1 hp.2
    simp only [f, hell]
  have hfMeas : AEStronglyMeasurable f (mu.prod sphere) := by
    have hexplicit : AEStronglyMeasurable
        (fun p : ConcreteMatrixState N × ComplexUnitSphere N ↦
          concreteCenteredRankOneFirstDensityScore N K p.2 p.1 ^ 4)
        (mu.prod sphere) :=
      (measurable_concreteCenteredRankOneFirstDensityScore_product N K).pow_const 4
      |>.aestronglyMeasurable
    exact hexplicit.congr hfEq.symm
  have hSlices : ∀ᵐ A ∂mu,
      Integrable (fun v ↦ f (A, v)) sphere ∧
        (∫ v, ‖f (A, v)‖ ∂sphere) ≤ envelope A := by
    filter_upwards [hSupport] with A hA
    simpa only [f, sphere, envelope] using
      (h12_fixedMatrix_projectiveFourth_package_internal
        hN hgap A hA.1 hA.2)
  have hEnvelope :=
    h12ProjectiveFourthEnvelope_momentPackage_strong_proved_A2A3A4 hN hgap
  have hEnvelopeInt : Integrable envelope mu := by
    simpa only [envelope, mu] using hEnvelope.1
  have hInnerMeas : AEStronglyMeasurable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) mu :=
    hfMeas.norm.integral_prod_right'
  have hInnerInt : Integrable
      (fun A ↦ ∫ v, ‖f (A, v)‖ ∂sphere) mu := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [hSlices] with A hA
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hA.2
    · exact h12ProjectiveFourthEnvelope_nonneg N K A
  have hfInt : Integrable f (mu.prod sphere) := by
    apply (integrable_prod_iff hfMeas).2
    constructor
    · filter_upwards [hSlices] with A hA
      exact hA.1
    · exact hInnerInt
  constructor
  · have hfMem : MemLp f 1 (mu.prod sphere) :=
      memLp_one_iff_integrable.mpr hfInt
    simpa only [f, mu, sphere, concreteCenteredScoreProductLaw] using hfMem
  · intro hdense
    have hbound : lpNorm f 1 (mu.prod sphere) ≤
        (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 := by
      calc
        lpNorm f 1 (mu.prod sphere) =
            ∫ A, ∫ v, ‖f (A, v)‖ ∂sphere ∂mu := by
          rw [lpNorm_one_eq_integral_norm hfMeas]
          exact integral_prod (fun p ↦ ‖f p‖) hfInt.norm
        _ ≤ ∫ A, envelope A ∂mu := by
          apply integral_mono_ae hInnerInt hEnvelopeInt
          filter_upwards [hSlices] with A hA
          exact hA.2
        _ ≤ (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 := by
          simpa only [envelope, mu] using hEnvelope.2 hdense
    simpa only [f, mu, sphere, concreteCenteredScoreProductLaw] using hbound

/-- Literal H12 endpoint, relaxed to the paper-facing common constant. -/
theorem centeredLogScore_oneFourth_momentPackage_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hStrong :=
    centeredLogScore_oneFourth_momentPackage_strong_proved_A1A2A3A4 hN hgap
  refine ⟨hStrong.1, ?_⟩
  intro hdense
  calc
    lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
        (concreteCenteredScoreProductLaw N K) ≤
        (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 := hStrong.2 hdense
    _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg (N : ℝ))
      norm_num [centeredLogScoreFourthMomentConstant,
        denseClassicalMomentConstant]

theorem centeredLogScore_oneFourth_memLp_one_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
      (concreteCenteredScoreProductLaw N K) :=
  (centeredLogScore_oneFourth_momentPackage_proved_A1A2A3A4 hN hgap).1

theorem centeredLogScore_oneFourth_lpNorm_one_le_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
        (concreteCenteredScoreProductLaw N K) ≤
      centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 :=
  (centeredLogScore_oneFourth_momentPackage_proved_A1A2A3A4
    hN (by omega)).2 hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
