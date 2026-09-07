import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11H13_ExactIndependentReduction
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Projective-first reductions for H11 and H13

The operator-radius route bounds each projective direction before integrating
over the sphere.  This module exposes the complementary order of operations:
first integrate the absolute score over the projective direction at a fixed
supported matrix, and only then integrate a matrix-only trace envelope.

The generic reducer below is measure-theoretic.  It introduces no axiom and
does not use either legacy H11/H13 moment declaration.  The two specialized
reducers use only the already approved almost-everywhere support theorem to
place the concrete matrix law inside the open symmetric-ball support.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-- A fixed-matrix projective `L¹` envelope for a score on the concrete
matrix/projective product.  The decisive estimate is fibrewise: the absolute
score is integrated over the projective direction before it is compared with
the matrix-only envelope. -/
structure HigherScoreFixedMatrixProjectiveL1Envelope
    (N K : ℕ)
    (score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ)
    (envelope : ConcreteMatrixState N → ℝ) : Prop where
  measurable_score : Measurable score
  envelope_nonneg : ∀ A, 0 ≤ envelope A
  fixedMatrix_package :
    ∀ (A : ConcreteMatrixState N),
      (unscaleCOECorner K A).IsSymm →
      coeCornerSupport (unscaleCOECorner K A) →
        Integrable (fun v ↦ score (A, v)) (higherScoreSphereLaw N) ∧
          (∫ v, ‖score (A, v)‖ ∂(higherScoreSphereLaw N)) ≤
            envelope A

/-- The matrix-law half of the projective-first route.  Its intended
producers are trace-vector transport and order-at-most-four inverse-Wishart
moments, but the endpoint reducer depends only on this exact `L¹` contract. -/
structure HigherScoreTraceEnvelopeL1Package
    (N K : ℕ) (envelope : ConcreteMatrixState N → ℝ) : Prop where
  integrable : Integrable envelope (higherScoreMatrixLaw N K)
  integral_le : 16 * N ≤ K →
    (∫ A, envelope A ∂(higherScoreMatrixLaw N K)) ≤
      centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2

/-- The H11 fixed-matrix projective-first interface. -/
abbrev H11HigherScoreProjectiveFirstEnvelope
    (N K : ℕ) (envelope : ConcreteMatrixState N → ℝ) : Prop :=
  HigherScoreFixedMatrixProjectiveL1Envelope N K
    (concreteCenteredEll 4 N K) envelope

/-- The H13 fixed-matrix projective-first interface. -/
abbrev H13HigherScoreProjectiveFirstEnvelope
    (N K : ℕ) (envelope : ConcreteMatrixState N → ℝ) : Prop :=
  HigherScoreFixedMatrixProjectiveL1Envelope N K
    (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) envelope

/-- Generic product-law endpoint reducer for a projective-first envelope.
No scientific statement is used: support is an explicit premise. -/
theorem higherScore_momentPackage_of_projectiveFirst_and_aeSupport
    {N K : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K)
    (score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ)
    (envelope : ConcreteMatrixState N → ℝ)
    (Hprojective : HigherScoreFixedMatrixProjectiveL1Envelope
      N K score envelope)
    (Hmatrix : HigherScoreTraceEnvelopeL1Package N K envelope)
    (hSupport : ∀ᵐ A ∂(higherScoreMatrixLaw N K),
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A)) :
    MemLp score 1 (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm score 1 (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) := higherScoreMatrixLaw N K
  let sphere : Measure (ComplexUnitSphere N) := higherScoreSphereLaw N
  letI : IsProbabilityMeasure μ :=
    canonicalScaledCOECornerLaw_isProbability hNK
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hscoreMeas : AEStronglyMeasurable score (μ.prod sphere) := by
    exact Hprojective.measurable_score.aestronglyMeasurable
  have hSlices : ∀ᵐ A ∂μ,
      Integrable (fun v ↦ score (A, v)) sphere ∧
        (∫ v, ‖score (A, v)‖ ∂sphere) ≤ envelope A := by
    filter_upwards [show ∀ᵐ A ∂μ,
        (unscaleCOECorner K A).IsSymm ∧
          coeCornerSupport (unscaleCOECorner K A) by
      simpa only [μ] using hSupport] with A hA
    simpa only [sphere] using
      Hprojective.fixedMatrix_package A hA.1 hA.2
  have hEnvelopeInt : Integrable envelope μ := by
    simpa only [μ] using Hmatrix.integrable
  have hInnerMeas : AEStronglyMeasurable
      (fun A ↦ ∫ v, ‖score (A, v)‖ ∂sphere) μ :=
    hscoreMeas.norm.integral_prod_right'
  have hInnerInt : Integrable
      (fun A ↦ ∫ v, ‖score (A, v)‖ ∂sphere) μ := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [hSlices] with A hA
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Hprojective.envelope_nonneg A)]
    exact hA.2
  have hscoreInt : Integrable score (μ.prod sphere) := by
    apply (integrable_prod_iff hscoreMeas).2
    exact ⟨hSlices.mono fun _ hA ↦ hA.1, hInnerInt⟩
  constructor
  · change MemLp score 1 (μ.prod sphere)
    exact memLp_one_iff_integrable.mpr hscoreInt
  · intro hdense
    change lpNorm score 1 (μ.prod sphere) ≤ _
    calc
      lpNorm score 1 (μ.prod sphere) =
          ∫ A, ∫ v, ‖score (A, v)‖ ∂sphere ∂μ := by
        rw [lpNorm_one_eq_integral_norm hscoreMeas]
        exact integral_prod (fun p ↦ ‖score p‖) hscoreInt.norm
      _ ≤ ∫ A, envelope A ∂μ := by
        apply integral_mono_ae hInnerInt hEnvelopeInt
        filter_upwards [hSlices] with A hA
        exact hA.2
      _ ≤ centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 := by
        simpa only [μ] using Hmatrix.integral_le hdense

/-- H11 endpoint reducer with projective averaging performed first.  This
replaces both the pointwise H11 envelope and the common operator-radius
package by a fixed-matrix projective contract and a matrix trace envelope. -/
theorem centeredLogScore_four_momentPackage_of_projectiveFirst
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (envelope : ConcreteMatrixState N → ℝ)
    (Hprojective : H11HigherScoreProjectiveFirstEnvelope N K envelope)
    (Hmatrix : HigherScoreTraceEnvelopeL1Package N K envelope) :
    MemLp (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredEll 4 N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hSupport : ∀ᵐ A ∂(higherScoreMatrixLaw N K),
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) :=
    friedmanMello1985_scaledCOECorner_ae_support_from_density
      hN (by omega : 2 * N ≤ K)
  exact higherScore_momentPackage_of_projectiveFirst_and_aeSupport
    hN (by omega) (concreteCenteredEll 4 N K) envelope
    Hprojective Hmatrix hSupport

/-- H13 endpoint reducer with projective averaging performed first. -/
theorem centeredLogScore_oneThree_momentPackage_of_projectiveFirst
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (envelope : ConcreteMatrixState N → ℝ)
    (Hprojective : H13HigherScoreProjectiveFirstEnvelope N K envelope)
    (Hmatrix : HigherScoreTraceEnvelopeL1Package N K envelope) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  have hSupport : ∀ᵐ A ∂(higherScoreMatrixLaw N K),
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) :=
    friedmanMello1985_scaledCOECorner_ae_support_from_density
      hN (by omega : 2 * N ≤ K)
  exact higherScore_momentPackage_of_projectiveFirst_and_aeSupport
    hN (by omega)
    (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p)
    envelope Hprojective Hmatrix hSupport

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
