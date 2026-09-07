import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_StrongProjectiveEnvelopeBound
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# Strong product-law bound for the centered second-score square

This is the product/Fubini adapter for the sharpened H14 radial envelope.
It exposes the actual constant `h14StrongProjectiveEnvelopeConstant` instead
of relaxing immediately to the common `2^160` fourth-score constant.  The
strong statement is used only for numerical slack in the H11 lower-Bell
assembly; the existing H14 endpoint remains unchanged.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Literal centered-`ellTwo` square package with the unrelaxed constant
already produced by the H14 radial proof. -/
theorem centeredLogScore_twoSquare_momentPackage_strong_A1A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h14StrongProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
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
  have hfMeas : AEStronglyMeasurable f (μ.prod sphere) := by
    exact (measurable_concreteCenteredEll_two (N := N) (K := K) hN).pow_const 2
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
    have hnormeq : (fun v ↦ ‖f (A, v)‖) =
        fun v ↦ ‖h14CenteredSandwichSecondSquare N K A v‖ := by
      funext v
      exact congrArg norm (congrFun heq v)
    constructor
    · rw [heq]
      exact hPA.1
    · rw [hnormeq]
      simpa only [μ, sphere, envelope] using hPA.2
  have hEnvelope :=
    h14ProjectiveCancellationEnvelope_momentPackage_strong_A2A3 hN hgap
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
      abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    rw [Real.norm_eq_abs,
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
        h14StrongProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
      calc
        lpNorm f 1 (μ.prod sphere) =
            ∫ A, ∫ v, ‖f (A, v)‖ ∂sphere ∂μ := by
          rw [lpNorm_one_eq_integral_norm hfMeas]
          exact integral_prod (fun p ↦ ‖f p‖) hfInt.norm
        _ ≤ ∫ A, envelope A ∂μ := by
          apply integral_mono_ae hInnerInt hEnvelopeInt
          filter_upwards [hSlices] with A hA
          exact hA.2
        _ ≤ h14StrongProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
          simpa only [envelope, μ] using hEnvelope.2 hdense
    simpa only [f, μ, sphere, concreteCenteredScoreProductLaw] using hbound

theorem centeredLogScore_twoSquare_memLp_one_strong_A1A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
      (concreteCenteredScoreProductLaw N K) :=
  (centeredLogScore_twoSquare_momentPackage_strong_A1A2A3 hN hgap).1

theorem centeredLogScore_twoSquare_lpNorm_one_le_strong_A1A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
        (concreteCenteredScoreProductLaw N K) ≤
      h14StrongProjectiveEnvelopeConstant * (N : ℝ) ^ 2 :=
  (centeredLogScore_twoSquare_momentPackage_strong_A1A2A3
    hN (by omega)).2 hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
