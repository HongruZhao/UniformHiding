import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_FourthDensityNormalization
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLogScoreOneSquareTwoDerived
import Mathlib.Tactic

/-!
# Fourth-log-score `L¹` from Bell normalization and a support sign

This module isolates an acyclic route to H11.  For each fixed projective
direction, the fourth density score is integrable and has integral zero.
If the fourth logarithmic score is nonpositive on the COE support, the fourth
Bell identity therefore identifies its absolute integral with the signed
integral of the four lower Bell monomials.  Fubini then promotes the fixed-
direction identity to the product law.

The abstract reducer below records the measure-theoretic argument.  The
concrete endpoint reducer requires only a support sign and one aggregate
`L¹` package for the lower Bell polynomial.  It introduces no new axiom and
does not assume product integrability of the fourth density score.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Generic fixed-fibre normalization bootstrap.  The important feature is
that `density` is required to be integrable only in each `μ`-fibre; no
product-integrability hypothesis on `density` is used. -/
theorem integrable_and_lpNorm_one_le_of_fiber_normalization_nonpos
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    {μ : Measure Alpha} {ν : Measure Beta} [SFinite μ] [SFinite ν]
    {density score lower : Alpha × Beta → ℝ}
    (hscoreMeas : AEStronglyMeasurable score (μ.prod ν))
    (hlower : Integrable lower (μ.prod ν))
    (hdensityInt : ∀ b, Integrable (fun a ↦ density (a, b)) μ)
    (hdensityZero : ∀ b, (∫ a, density (a, b) ∂μ) = 0)
    (hBell : ∀ b, (fun a ↦ density (a, b)) =ᵐ[μ]
      (fun a ↦ lower (a, b) + score (a, b)))
    (hscoreNonpos : ∀ b, ∀ᵐ a ∂μ, score (a, b) ≤ 0) :
    Integrable score (μ.prod ν) ∧
      lpNorm score 1 (μ.prod ν) ≤ lpNorm lower 1 (μ.prod ν) := by
  have hscoreFiberInt : ∀ᵐ b ∂ν,
      Integrable (fun a ↦ score (a, b)) μ := by
    filter_upwards [hlower.prod_left_ae] with b hlowerB
    have hEq : (fun a ↦ score (a, b)) =ᵐ[μ]
        (fun a ↦ density (a, b) - lower (a, b)) := by
      filter_upwards [hBell b] with a ha
      linarith
    exact ((hdensityInt b).sub hlowerB).congr hEq.symm
  have hfiberLe : ∀ᵐ b ∂ν,
      (∫ a, ‖score (a, b)‖ ∂μ) ≤
        ∫ a, ‖lower (a, b)‖ ∂μ := by
    filter_upwards [hlower.prod_left_ae] with b hlowerB
    have hEq : (fun a ↦ score (a, b)) =ᵐ[μ]
        (fun a ↦ density (a, b) - lower (a, b)) := by
      filter_upwards [hBell b] with a ha
      linarith
    have hscoreB : Integrable (fun a ↦ score (a, b)) μ :=
      ((hdensityInt b).sub hlowerB).congr hEq.symm
    have hnormEq : (fun a ↦ ‖score (a, b)‖) =ᵐ[μ]
        (fun a ↦ -score (a, b)) := by
      filter_upwards [hscoreNonpos b] with a ha
      rw [Real.norm_eq_abs, abs_of_nonpos ha]
    calc
      (∫ a, ‖score (a, b)‖ ∂μ) = -(∫ a, score (a, b) ∂μ) := by
        rw [integral_congr_ae hnormEq, integral_neg]
      _ = ∫ a, lower (a, b) ∂μ := by
        rw [integral_congr_ae hEq, integral_sub (hdensityInt b) hlowerB,
          hdensityZero b]
        ring
      _ ≤ ‖∫ a, lower (a, b) ∂μ‖ := Real.le_norm_self _
      _ ≤ ∫ a, ‖lower (a, b)‖ ∂μ :=
        norm_integral_le_integral_norm _
  have hscoreFiberNormMeas : AEStronglyMeasurable
      (fun b ↦ ∫ a, ‖score (a, b)‖ ∂μ) ν := by
    simpa using hscoreMeas.norm.prod_swap.integral_prod_right'
  have hlowerFiberNormInt : Integrable
      (fun b ↦ ∫ a, ‖lower (a, b)‖ ∂μ) ν :=
    hlower.integral_norm_prod_right
  have hscoreFiberNormInt : Integrable
      (fun b ↦ ∫ a, ‖score (a, b)‖ ∂μ) ν := by
    apply hlowerFiberNormInt.mono' hscoreFiberNormMeas
    filter_upwards [hfiberLe] with b hb
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)]
    exact hb
  have hscoreInt : Integrable score (μ.prod ν) := by
    exact (integrable_prod_iff' hscoreMeas).2
      ⟨hscoreFiberInt, hscoreFiberNormInt⟩
  refine ⟨hscoreInt, ?_⟩
  rw [lpNorm_one_eq_integral_norm hscoreMeas,
    lpNorm_one_eq_integral_norm hlower.aestronglyMeasurable]
  calc
    (∫ z, ‖score z‖ ∂(μ.prod ν)) =
        ∫ b, ∫ a, ‖score (a, b)‖ ∂μ ∂ν := by
      exact integral_prod_symm (fun z ↦ ‖score z‖) hscoreInt.norm
    _ ≤ ∫ b, ∫ a, ‖lower (a, b)‖ ∂μ ∂ν := by
      exact integral_mono_ae hscoreFiberNormInt hlowerFiberNormInt hfiberLe
    _ = ∫ z, ‖lower z‖ ∂(μ.prod ν) := by
      exact (integral_prod_symm (fun z ↦ ‖lower z‖) hlower.norm).symm

/-- The four lower monomials in the fourth Bell polynomial. -/
def concreteCenteredBellFourLowerProduct (N K : ℕ) :
    ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
  fun p ↦ concreteCenteredEll 1 N K p ^ 4 +
    6 * concreteCenteredEll 1 N K p ^ 2 * concreteCenteredEll 2 N K p +
    3 * concreteCenteredEll 2 N K p ^ 2 +
    4 * concreteCenteredEll 1 N K p * concreteCenteredEll 3 N K p

/-- Aggregate lower-Bell input for the sign/normalization H11 route.  Keeping
the sharp bound at the aggregate level preserves all numerical slack; the
individual monomial packages need not each spend the full common constant. -/
structure H11BellFourLowerMomentPackage (N K : ℕ) : Prop where
  memLp_one : MemLp (concreteCenteredBellFourLowerProduct N K) 1
    (concreteCenteredScoreProductLaw N K)
  lpNorm_one_le : 16 * N ≤ K →
    lpNorm (concreteCenteredBellFourLowerProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ≤
      centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2

/-- Pointwise deterministic input isolated by the shortest H11 route. -/
structure H11FourthLogScoreNonpositiveOnSupport (N K : ℕ) : Prop where
  nonpos_on_support :
    ∀ (A : ConcreteMatrixState N) (v : ComplexUnitSphere N),
      (unscaleCOECorner K A).IsSymm →
      coeCornerSupport (unscaleCOECorner K A) →
      concreteCenteredEll 4 N K (A, v) ≤ 0

/-- Concrete H11 endpoint from fixed-direction density normalization, the
Bell identity, a support sign, and the aggregate lower-Bell moment package.
No product integrability of the fourth density score is assumed. -/
theorem centeredLogScore_four_momentPackage_of_BellNormalization_nonpos
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hsign : H11FourthLogScoreNonpositiveOnSupport N K)
    (Hlower : H11BellFourLowerMomentPackage N K) :
    MemLp (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredEll 4 N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) := by
  let μ := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let ν := complexUnitSphereProbabilityMeasure N
  let density : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 4 N K Av.2 Av.1
  let score := concreteCenteredEll 4 N K
  let lower := concreteCenteredBellFourLowerProduct N K
  letI : IsProbabilityMeasure μ :=
    canonicalScaledCOECornerLaw_isProbability (by omega : N ≤ K)
  letI : IsProbabilityMeasure ν :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hsupport : ∀ᵐ A ∂μ,
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
    simpa only [μ] using
      friedmanMello1985_scaledCOECorner_ae_support_from_density
        hN (by omega : 2 * N ≤ K)
  have hBell : ∀ v, (fun A ↦ density (A, v)) =ᵐ[μ]
      (fun A ↦ lower (A, v) + score (A, v)) := by
    intro v
    filter_upwards [hsupport] with A hA
    rcases hA with ⟨hSymm, hSupp⟩
    have h := coeCorner_centeredDensityScore_four_eq_Bell_external_derived
      hN hgap v A hSymm hSupp
    simpa only [density, lower, score, concreteCenteredBellFourLowerProduct,
      concreteCenteredEll, densityBellFour] using h
  have hnonpos : ∀ v, ∀ᵐ A ∂μ, score (A, v) ≤ 0 := by
    intro v
    filter_upwards [hsupport] with A hA
    exact Hsign.nonpos_on_support A v hA.1 hA.2
  have hlowerInt : Integrable lower (μ.prod ν) := by
    rw [← memLp_one_iff_integrable]
    simpa only [lower, μ, ν, concreteCenteredScoreProductLaw] using
      Hlower.memLp_one
  have H := integrable_and_lpNorm_one_le_of_fiber_normalization_nonpos
    (density := density) (score := score) (lower := lower)
    ((measurable_concreteCenteredEll_four (N := N) (K := K) hN)
      |>.aestronglyMeasurable)
    hlowerInt
    (fun v ↦ by
      simpa only [density, μ] using
        integrable_concreteCenteredDensityScore_four_fixedDirection_literal_from_A1
          hN hgap v)
    (fun v ↦ by
      simpa only [density, μ] using
        integral_concreteCenteredDensityScore_four_fixedDirection_eq_zero_from_A1
          hN hgap v)
    hBell hnonpos
  constructor
  · rw [memLp_one_iff_integrable]
    simpa only [score, μ, ν, concreteCenteredScoreProductLaw] using H.1
  · intro hdense
    have hle := H.2.trans (Hlower.lpNorm_one_le hdense)
    simpa only [score, lower, μ, ν, concreteCenteredScoreProductLaw] using hle

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
