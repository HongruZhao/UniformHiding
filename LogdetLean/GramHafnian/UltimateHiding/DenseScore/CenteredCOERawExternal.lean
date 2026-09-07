import LogdetLean.GramHafnian.UltimateHiding.DenseScore.QuadraticCenteringFromMass
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveSecondMoment
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveContractions
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COESupportAlgebra
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredLikelihood
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredDensityScoreOneDerived
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredDensityScoreTwoExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreFubiniFinite
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthSecantIntegralVanishingFromPointwiseFTC
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import Mathlib.Tactic

/-!
# Raw centered COE calculus and the concrete quadratic identification

This file identifies the first two derivatives of the projectively averaged
centered COE flow.  The release routes both differentiation steps through the
proved A1-based H16/H18 theorems:

* fixed-direction differentiation of the literal centered
  determinant-density event path through order four, leaving
  `concreteCenteredDensityScore r`;
* separate projective differentiation and internally proved third-score
  product `L¹` integrability;
* the remaining pointwise-on-support second determinant derivative identifying
  the literal second score with its explicit trace formula;
* the exact Friedman--Mello support statement for the same literal variables.

All three projective contractions and the cancellation to the `R30` trace
bracket are proved internally from the low-order projective tensor moment.
The first pointwise score identity is proved from the literal determinant in
`CenteredDensityScoreOneDerived`.  The formerly external `R20` trace identities are derived in
`COESupportAlgebra` from symmetry and `I-CᴴC>0`.  No norm, total-variation,
local-step, telescoping, or hiding conclusion is an additional input.
-/

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The historical origin-only compact-parameter theorem is now a direct
specialization of the proved A1-based all-time H18 interchange theorem. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_external_derived
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 =
      ∫ v : ComplexUnitSphere N,
        iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0
          ∂(complexUnitSphereProbabilityMeasure N) := by
  exact coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_proved_from_A1
    hN hboundary hr event hevent 0

/-- Projective raw derivative formula derived from the fixed-direction
boundary calculus plus the two separate exact interchange steps. -/
theorem coeCorner_centeredProjective_eventPath_derivative_literal
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 =
      ∫ A, event.indicator (fun A ↦
        ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore r N K v A
          ∂(complexUnitSphereProbabilityMeasure N)) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) := by
  rw [coeCorner_centeredProjective_eventPath_derivative_interchange_external_derived
    hN hboundary hr event hevent]
  simp_rw [coeCorner_centeredFixedDirection_eventPath_derivative_H16_proved_from_A1
    hN hboundary hr _ event hevent]
  exact coeCorner_centeredDensityScore_fubini_external_derived
    hN hboundary hr event hevent

/-- Order-one specialization of the literal projective derivative formula.
Unlike the compatibility theorem above, its dependency closure contains only
the order-one Fubini proof and therefore no unused order-three premise. -/
theorem coeCorner_centeredProjective_eventPath_derivative_literal_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv 1
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 =
      ∫ A, event.indicator (fun A ↦
        ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 1 N K v A
          ∂(complexUnitSphereProbabilityMeasure N)) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) := by
  rw [coeCorner_centeredProjective_eventPath_derivative_interchange_external_derived
    (r := 1) hN hboundary (by omega) event hevent]
  simp_rw [coeCorner_centeredFixedDirection_eventPath_derivative_H16_proved_from_A1
    (r := 1) hN hboundary (by omega) _ event hevent]
  exact coeCorner_centeredDensityScore_one_fubini
    hN hboundary event hevent

/-- Order-two specialization of the literal projective derivative formula,
avoiding the unused order-three branch in the generic compatibility theorem. -/
theorem coeCorner_centeredProjective_eventPath_derivative_literal_two_internal
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv 2
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 =
      ∫ A, event.indicator (fun A ↦
        ∫ v : ComplexUnitSphere N, concreteCenteredDensityScore 2 N K v A
          ∂(complexUnitSphereProbabilityMeasure N)) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) := by
  rw [coeCorner_centeredProjective_eventPath_derivative_interchange_external_derived
    (r := 2) hN hboundary (by omega) event hevent]
  simp_rw [coeCorner_centeredFixedDirection_eventPath_derivative_H16_proved_from_A1
    (r := 2) hN hboundary (by omega) _ event hevent]
  exact coeCorner_centeredDensityScore_two_fubini
    hN hboundary event hevent

/-- Former aggregate order-two boundary statement, now an internally derived
theorem.  Its only external dependencies are fixed-direction literal
differentiation/interchange and the pointwise support formula above. -/
theorem coeCorner_centeredProjective_secondRaw_external_derived
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv 2
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 =
      ∫ A, event.indicator (fun A ↦
        ∫ v : ComplexUnitSphere N,
          concreteCenteredRankOneSecondDensityScore N K v A
            ∂(complexUnitSphereProbabilityMeasure N)) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) := by
  rw [coeCorner_centeredProjective_eventPath_derivative_literal_two_internal
    hN hboundary event hevent]
  apply integral_congr_ae
  filter_upwards
    [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
      with A hA
  rcases hA with ⟨hsymm, hsupport⟩
  by_cases hmem : A ∈ event
  · simp only [Set.indicator, hmem, if_true]
    apply integral_congr_ae
    filter_upwards [] with v
    exact coeCorner_centeredDensityScore_two_eq_explicit_external_derived
      hN hboundary v A hsymm hsupport
  · simp only [Set.indicator, hmem, if_false]

/-- Backward-compatible name.  This centered raw derivative identity is a
derived determinant-density/boundary-calculus consequence, not a verbatim
Friedman--Mello theorem. -/
@[deprecated coeCorner_centeredProjective_secondRaw_external_derived
  (since := "2026-08-21")]
theorem friedmanMello_centeredProjective_eventPath_second_raw_external
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K) :
    iteratedDeriv 2
        (concreteProjectiveAveragedCenteredCOEEventPath N K Set.univ) 0 =
      ∫ A, ∫ v : ComplexUnitSphere N,
        concreteCenteredRankOneSecondDensityScore N K v A
          ∂(complexUnitSphereProbabilityMeasure N)
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) :=
  by
    simpa using
      coeCorner_centeredProjective_secondRaw_external_derived
        hN hboundary Set.univ MeasurableSet.univ

/-- The centered first trace pairing has projective mean zero, derived from
the internal first projective moment and probability normalization. -/
theorem integral_complexCenteredProjectiveTracePair_eq_zero
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    (∫ v : ComplexUnitSphere N,
      complexCenteredProjectiveTracePair v A
        ∂(complexUnitSphereProbabilityMeasure N)) = 0 := by
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hpair := integrable_complexProjectiveTracePair hN A
  have hconst : Integrable (fun _ : ComplexUnitSphere N ↦
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace A)
      (complexUnitSphereProbabilityMeasure N) := integrable_const _
  unfold complexCenteredProjectiveTracePair
  rw [integral_sub hpair hconst, integral_complexProjectiveTracePair hN]
  simp

theorem integral_concreteCenteredRankOneFirstDensityScore
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    (∫ v : ComplexUnitSphere N,
      concreteCenteredRankOneFirstDensityScore N K v A
        ∂(complexUnitSphereProbabilityMeasure N)) = 0 := by
  have hint := integrable_complexCenteredProjectiveTracePair hN
    (concreteCOEY N K A)
  unfold concreteCenteredRankOneFirstDensityScore
    concreteCenteredRankOneFirstDensityScoreComplex
  change (∫ v : ComplexUnitSphere N,
    RCLike.re (2 * complexCenteredProjectiveTracePair v
      (concreteCOEY N K A))
      ∂(complexUnitSphereProbabilityMeasure N)) = 0
  have htwo : Integrable (fun v : ComplexUnitSphere N ↦
      (2 : ℂ) * complexCenteredProjectiveTracePair v
        (concreteCOEY N K A))
      (complexUnitSphereProbabilityMeasure N) := hint.const_mul 2
  rw [integral_re htwo, integral_const_mul,
    integral_complexCenteredProjectiveTracePair_eq_zero hN]
  norm_num

/-- The projectively averaged centered first event derivative is exactly
zero.  This is the internal cancellation `E_v Q_v=0`; it is marginal for
each measurable event and contains no estimate. -/
theorem concrete_projectiveAveraged_centered_first_derivative_eq_zero
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv 1
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 = 0 := by
  rw [coeCorner_centeredProjective_eventPath_derivative_literal_one_internal
    hN hboundary event hevent]
  -- Apply the pointwise cancellation only on the almost-sure COE support.
  apply integral_eq_zero_of_ae
  filter_upwards
    [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
      with A hA
  rcases hA with ⟨hsymm, hsupport⟩
  by_cases hmem : A ∈ event
  · simp only [Set.indicator, hmem, if_true]
    have hfun : (fun v : ComplexUnitSphere N ↦
        concreteCenteredDensityScore 1 N K v A) =
        (fun v ↦ concreteCenteredRankOneFirstDensityScore N K v A) := by
      funext v
      exact coeCorner_centeredDensityScore_one_eq_explicit_external_derived
        hN hboundary v A hsymm hsupport
    rw [hfun, integral_concreteCenteredRankOneFirstDensityScore hN A]
    simp
  · simp [Set.indicator, hmem]

theorem integrable_concreteCenteredRankOneSecondDensityScoreComplex
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      concreteCenteredRankOneSecondDensityScoreComplex N K v A)
      (complexUnitSphereProbabilityMeasure N) := by
  unfold concreteCenteredRankOneSecondDensityScoreComplex
  have hA := integrable_complexCenteredProjectiveTracePair hN
    (concreteCOEY N K A)
  have hAA := integrable_complexCenteredProjectiveTracePair_mul hN
    (concreteCOEY N K A) (concreteCOEY N K A)
  have hAApow : Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair v (concreteCOEY N K A) ^ 2)
      (complexUnitSphereProbabilityMeasure N) := by
    simpa only [pow_two] using hAA
  have hB := integrable_complexCenteredProjectiveSandwich hN
    (concreteCOEWMatrix N K A) (concreteCOEY N K A)
  have hC := integrable_complexCenteredProjectiveConjugateSandwich hN
    (concreteCOERMatrix N K A)
  have hinner : Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair v (concreteCOEY N K A) ^ 2 -
        complexCenteredProjectiveSandwich v
          (concreteCOEWMatrix N K A) (concreteCOEY N K A) -
        complexCenteredProjectiveConjugateSandwich v
          (concreteCOERMatrix N K A))
      (complexUnitSphereProbabilityMeasure N) := by
    have hfun : (fun v : ComplexUnitSphere N ↦
        complexCenteredProjectiveTracePair v (concreteCOEY N K A) ^ 2 -
          complexCenteredProjectiveSandwich v
            (concreteCOEWMatrix N K A) (concreteCOEY N K A) -
          complexCenteredProjectiveConjugateSandwich v
            (concreteCOERMatrix N K A)) =
        (((fun v : ComplexUnitSphere N ↦
              complexCenteredProjectiveTracePair v (concreteCOEY N K A) *
                complexCenteredProjectiveTracePair v (concreteCOEY N K A)) -
            fun v ↦ complexCenteredProjectiveSandwich v
              (concreteCOEWMatrix N K A) (concreteCOEY N K A)) -
          fun v ↦ complexCenteredProjectiveConjugateSandwich v
            (concreteCOERMatrix N K A)) := by
      funext v
      rw [Pi.sub_apply, Pi.sub_apply, pow_two]
    rw [hfun]
    exact (hAA.sub hB).sub hC
  exact hinner.const_mul 4

/-- The exact complex `R28` contraction, before taking the real part. -/
def concreteProjectiveAveragedSecondDensityComplex
    (N K : ℕ) (A : ConcreteMatrixState N) : ℂ :=
  let n : ℝ := N
  let d : ℝ := (n * (n + 1))⁻¹
  let e : ℝ := (n ^ 2 * (n + 1))⁻¹
  let f : ℝ := (n - 1) / (n ^ 2 * (n + 1))
  let a : ℂ := ((d : ℝ) : ℂ) *
    (Matrix.trace (concreteCOEY N K A * concreteCOEY N K A) -
      (((n⁻¹ : ℝ) : ℂ) * Matrix.trace (concreteCOEY N K A) *
        Matrix.trace (concreteCOEY N K A)))
  let b : ℂ := ((d : ℝ) : ℂ) *
      (Matrix.trace (concreteCOEWMatrix N K A) *
        Matrix.trace (concreteCOEY N K A)) -
    ((e : ℝ) : ℂ) *
      Matrix.trace (concreteCOEWMatrix N K A * concreteCOEY N K A)
  let g : ℂ := ((f : ℝ) : ℂ) *
    Matrix.trace
      (concreteCOERMatrix N K A *
        (concreteCOERMatrix N K A).conjTranspose)
  ((4 : ℝ) : ℂ) * (a - b - g)

/-- The explicit real projective average after the exact `R28` contraction.
It contains no estimate and is written only in terms of raw trace scalars. -/
def concreteProjectiveAveragedSecondDensity
    (N K : ℕ) (A : ConcreteMatrixState N) : ℝ :=
  let n : ℝ := N
  let d : ℝ := (n * (n + 1))⁻¹
  let e : ℝ := (n ^ 2 * (n + 1))⁻¹
  let f : ℝ := (n - 1) / (n ^ 2 * (n + 1))
  let a : ℝ := d * (concreteCOETraceTwo N K A -
    n⁻¹ * concreteCOETraceOne N K A ^ 2)
  let b : ℝ := d * (Matrix.trace (concreteCOEWMatrix N K A)).re *
      concreteCOETraceOne N K A -
    e * (Matrix.trace
      (concreteCOEWMatrix N K A * concreteCOEY N K A)).re
  let g : ℝ := f * (Matrix.trace
    (concreteCOERMatrix N K A *
      (concreteCOERMatrix N K A).conjTranspose)).re
  4 * (a - b - g)

/-- Taking real parts of the exact complex contraction introduces no further
probabilistic input. -/
theorem concreteProjectiveAveragedSecondDensityComplex_re
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hYone : (Matrix.trace (concreteCOEY N K A)).im = 0) :
    (concreteProjectiveAveragedSecondDensityComplex N K A).re =
      concreteProjectiveAveragedSecondDensity N K A := by
  have htOne : (Matrix.trace (concreteCOEY N K A)).re =
      concreteCOETraceOne N K A := rfl
  have htTwo :
      (Matrix.trace (concreteCOEY N K A * concreteCOEY N K A)).re =
        concreteCOETraceTwo N K A := rfl
  unfold concreteProjectiveAveragedSecondDensityComplex
  unfold concreteProjectiveAveragedSecondDensity
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, htOne, htTwo, hYone]
  ring

/-- Exact complex integral of the raw second density score. -/
theorem integral_concreteCenteredRankOneSecondDensityScoreComplex
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hR : (concreteCOERMatrix N K A).IsSymm) :
    (∫ v : ComplexUnitSphere N,
      concreteCenteredRankOneSecondDensityScoreComplex N K v A
      ∂(complexUnitSphereProbabilityMeasure N)) =
      concreteProjectiveAveragedSecondDensityComplex N K A := by
  have hAA := integrable_complexCenteredProjectiveTracePair_mul hN
    (concreteCOEY N K A) (concreteCOEY N K A)
  have hAApow : Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair v (concreteCOEY N K A) ^ 2)
      (complexUnitSphereProbabilityMeasure N) := by
    simpa only [pow_two] using hAA
  have hB := integrable_complexCenteredProjectiveSandwich hN
    (concreteCOEWMatrix N K A) (concreteCOEY N K A)
  have hC := integrable_complexCenteredProjectiveConjugateSandwich hN
    (concreteCOERMatrix N K A)
  unfold concreteCenteredRankOneSecondDensityScoreComplex
  unfold concreteProjectiveAveragedSecondDensityComplex
  rw [integral_const_mul]
  rw [integral_sub]
  · rw [integral_sub]
    · simp only [pow_two]
      rw [integral_complexCenteredProjectiveTracePair_mul hN]
      rw [integral_complexCenteredProjectiveSandwich hN]
      rw [integral_complexCenteredProjectiveConjugateSandwich hN _ hR]
      norm_num
      ring
    · exact hAApow
    · exact hB
  · exact hAApow.sub hB
  · exact hC

theorem integral_concreteCenteredRankOneSecondDensityScore
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N)
    (hR : (concreteCOERMatrix N K A).IsSymm)
    (hYone : (Matrix.trace (concreteCOEY N K A)).im = 0) :
    (∫ v : ComplexUnitSphere N,
      concreteCenteredRankOneSecondDensityScore N K v A
      ∂(complexUnitSphereProbabilityMeasure N)) =
      concreteProjectiveAveragedSecondDensity N K A := by
  have hint := integrable_concreteCenteredRankOneSecondDensityScoreComplex
    (K := K) hN A
  unfold concreteCenteredRankOneSecondDensityScore
  change (∫ v : ComplexUnitSphere N,
      RCLike.re (concreteCenteredRankOneSecondDensityScoreComplex N K v A)
      ∂(complexUnitSphereProbabilityMeasure N)) = _
  rw [integral_re hint]
  rw [integral_concreteCenteredRankOneSecondDensityScoreComplex hN A hR]
  exact concreteProjectiveAveragedSecondDensityComplex_re A hYone

/-- Internal `R28--R30` closure at one concrete matrix state. -/
theorem integral_concreteCenteredRankOneSecondDensityScore_eq_density
    {N K : ℕ} (hN : 1 ≤ N) (hc : concreteCOEExponent N K ≠ 0)
    (A : ConcreteMatrixState N)
    (hR : (concreteCOERMatrix N K A).IsSymm)
    (hYone : (Matrix.trace (concreteCOEY N K A)).im = 0)
    (hYtwo : (Matrix.trace
      (concreteCOEY N K A * concreteCOEY N K A)).im = 0)
    (hWone : (Matrix.trace (concreteCOEWMatrix N K A)).re =
      (N : ℝ) + concreteCOETraceOne N K A / concreteCOEExponent N K)
    (hWY : (Matrix.trace
      (concreteCOEWMatrix N K A * concreteCOEY N K A)).re =
      concreteCOETraceOne N K A +
        concreteCOETraceTwo N K A / concreteCOEExponent N K)
    (hRR : (Matrix.trace
      (concreteCOERMatrix N K A *
        (concreteCOERMatrix N K A).conjTranspose)).re =
      concreteCOETraceOne N K A +
        concreteCOETraceTwo N K A / concreteCOEExponent N K) :
    (∫ v : ComplexUnitSphere N,
      concreteCenteredRankOneSecondDensityScore N K v A
      ∂(complexUnitSphereProbabilityMeasure N)) =
      concreteCenteredQuadraticDensity N K A := by
  rw [integral_concreteCenteredRankOneSecondDensityScore hN A hR hYone]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hNp : (N : ℝ) + 1 ≠ 0 := by positivity
  have htOne : (Matrix.trace (concreteCOEY N K A)).re =
      concreteCOETraceOne N K A := rfl
  have htTwo :
      (Matrix.trace (concreteCOEY N K A * concreteCOEY N K A)).re =
        concreteCOETraceTwo N K A := rfl
  simp only [concreteProjectiveAveragedSecondDensity, htOne, htTwo,
    hWone, hWY, hRR,
    concreteCenteredQuadraticDensity, concreteCenteredQuadraticTraceBracket,
    centeredQuadraticTraceBracket]
  field_simp [hNr, hNp, hc]
  ring

/-- Actual dense-range identification for every measurable event, with no
supplied `hidentify` hypothesis.  The only non-foundational dependencies are
the raw E1 calculus and exact E1 support; all `R20` matrix/trace identities,
the projective contraction, and the `R30` cancellation are internal. -/
theorem concrete_projectiveAveraged_centered_second_derivative_eq_density_indicator_integral
    {N K : ℕ} (hN : 1 ≤ N) (h16 : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv 2
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 =
      ∫ A, event.indicator (concreteCenteredQuadraticDensity N K) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) := by
  have hboundary : 2 * N + 8 ≤ K := by omega
  have hc : concreteCOEExponent N K ≠ 0 := by
    unfold concreteCOEExponent
    have hpos : 0 < (K : ℝ) - 2 * (N : ℝ) - 1 := by
      have h16r : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast h16
      have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      nlinarith
    exact ne_of_gt hpos
  have hcpos : 0 < concreteCOEExponent N K := by
    unfold concreteCOEExponent
    have h16r : (16 : ℝ) * (N : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast h16
    have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  rw [coeCorner_centeredProjective_secondRaw_external_derived
    hN hboundary event hevent]
  apply integral_congr_ae
  filter_upwards
    [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
      with A hA
  rcases hA with ⟨hsymm, hsupport⟩
  by_cases hmem : A ∈ event
  · simp only [Set.indicator, hmem, if_true]
    exact integral_concreteCenteredRankOneSecondDensityScore_eq_density
      hN hc A
        (concreteCOERMatrix_isSymm_of_support A hsymm hsupport)
        (concreteCOEY_trace_im_eq_zero_of_support A hsupport)
        (concreteCOEY_sq_trace_im_eq_zero_of_support A hsupport)
        (concreteCOEWMatrix_trace_re A hc)
        (concreteCOEWMatrix_mul_Y_trace_re A hc)
        (concreteCOERMatrix_sq_trace_re A hcpos hsupport)
  · simp only [Set.indicator, hmem, if_false]

/-- Total-mass specialization of the eventwise exact identification. -/
theorem concrete_projectiveAveraged_centered_second_derivative_eq_density_integral
    {N K : ℕ} (hN : 1 ≤ N) (h16 : 16 * N ≤ K) :
    iteratedDeriv 2
        (concreteProjectiveAveragedCenteredCOEEventPath N K Set.univ) 0 =
      ∫ A, concreteCenteredQuadraticDensity N K A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
            N K) := by
  simpa using
    concrete_projectiveAveraged_centered_second_derivative_eq_density_indicator_integral
      hN h16 Set.univ MeasurableSet.univ

/-- The concrete `R30` bracket is centered, derived from total mass rather
than assumed as a moment atom. -/
theorem integral_concreteCenteredQuadraticTraceBracket_eq_zero_dense
    {N K : ℕ} (hN : 1 ≤ N) (h16 : 16 * N ≤ K) :
    (∫ A, concreteCenteredQuadraticTraceBracket N K A
      ∂(concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.LocalAnticoncentration.canonicalUnitaryHaarProbabilityFamily
          N K)) = 0 := by
  have hNK : N ≤ K := by omega
  exact integral_concreteCenteredQuadraticTraceBracket_eq_zero_of_eventPath
    hN hNK
      (concrete_projectiveAveraged_centered_second_derivative_eq_density_integral
        hN h16)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
