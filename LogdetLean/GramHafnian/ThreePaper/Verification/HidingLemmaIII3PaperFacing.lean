import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.CombinedSharperCanonicalScoreCertificate
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.COEBaseRadialPropagation
import Mathlib.Tactic

/-!
# Paper-facing verification of Lemma III.3 and its one-column components

The manuscript writes the four score estimates as variation norms of signed
derivative measures.  The executable hiding proof uses the operational
event-path interface needed by `ProbabilityTVLE`: every displayed derivative
bound is uniform over measurable events.  This file packages that exact
kernel-checked interface, with the printed constants exposed literally.  It
does not claim that the signed derivative measures themselves have already
been constructed in Mathlib.

It also separates the correlated one-column comparison into the three
paper-facing pieces: scalar Taylor, good-orbital Taylor, and bad-event
coupling.  Their constants are respectively `240`, `614826`, and `72`.
-/

open MeasureTheory Set
open scoped ProbabilityTheory

namespace LogdetLean.GramHafnian.ThreePaper.Verification

noncomputable section

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.CurrentPRL
open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

/-- Paper Eq. `hide-congruence-action`: if the matrix state and factor are
sampled independently, the factor-law action is the pushforward of their
product law by literal transpose congruence `G * X * G.transpose`. -/
theorem eq_hide_congruence_action
    {N : ℕ} (xi : Measure (ComplexMatrixGL N))
    (eta : Measure (ConcreteMatrixState N)) :
    congruenceMeasureAction N xi eta =
      (eta.prod xi).map
        (fun XG ↦ complexGLTransposeCongruence N XG.2 XG.1) := by
  rfl

/-- Paper Eq. `hide-radial-one-column-commute`, with `ambient = m` and
`step = r`: the actual one-column kernel at the ambient Haar law is the
preceding radial chain applied to the same update at the square COE base. -/
theorem eq_hide_radial_one_column_commute
    (H : CurrentPRL.UnitaryHaarProbabilityFamily)
    {N K ambient step : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKambient : K ≤ ambient)
    (hNstep : N ≤ step) :
    concreteOneColumnMatrixKernel step N ∘ₘ
        concreteHaarAmbientLaw H N K ambient =
      radialConvolution
        (concreteRadialKernelChain N K (ambient - K))
        (concreteOneColumnMatrixKernel step N ∘ₘ
          concreteScaledCOECornerLaw H N K) :=
  concreteOneColumn_radial_commutation_at_scaledCOE
    H hN hNK hKambient hNstep

/-- Paper Eq. `hide-radial-TV` in the eventwise probability-TV convention:
every square-base bound with constant `delta` is transported to the ambient
law with exactly the same constant. -/
theorem eq_hide_radial_TV
    (H : CurrentPRL.UnitaryHaarProbabilityFamily)
    {N K ambient step : ℕ}
    (hN : 1 ≤ N) (hNK : N ≤ K) (hKambient : K ≤ ambient)
    (hNstep : N ≤ step) {delta : ℝ}
    (hbase : ProbabilityTVLE
      (concreteScaledCOECornerLaw H N K)
      (concreteOneColumnMatrixKernel step N ∘ₘ
        concreteScaledCOECornerLaw H N K)
      delta) :
    ProbabilityTVLE
      (concreteHaarAmbientLaw H N K ambient)
      (concreteOneColumnMatrixKernel step N ∘ₘ
        concreteHaarAmbientLaw H N K ambient)
      delta :=
  probabilityTVLE_concreteHaarAmbient_oneColumn_of_scaledCOE
    H hN hNK hKambient hNstep hbase

/-- Exact eventwise form of the regularity and five identities/inequalities
printed in Lemma III.3.

The first two fields are the central path at the canonical square COE law.
The remaining fields are the projectively averaged centered orbital path. -/
structure HidingLemmaIII3EventwiseScores (N K : ℕ) : Prop where
  centralSmooth :
    ∀ event : Set (ConcreteMatrixState N), MeasurableSet event →
      ContDiff ℝ 2
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event)
  orbitalSmooth :
    ∀ event : Set (ConcreteMatrixState N), MeasurableSet event →
      ContDiff ℝ 4
        (concreteProjectiveAveragedCenteredCOEEventPath N K event)
  scalarFirst :
    ∀ event : Set (ConcreteMatrixState N), MeasurableSet event →
      |iteratedDeriv 1
          (concreteCentralEventPath N
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) event) 0| ≤
        5 * (N : ℝ)
  scalarSecond :
    ∀ event : Set (ConcreteMatrixState N), MeasurableSet event → ∀ s : ℝ,
      |iteratedDeriv 2
          (concreteCentralEventPath N
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K) event) s| ≤
        44 * (N : ℝ) ^ 2
  orbitalFirst :
    ∀ event : Set (ConcreteMatrixState N), MeasurableSet event →
      iteratedDeriv 1
          (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0 = 0
  orbitalSecond :
    ∀ event : Set (ConcreteMatrixState N), MeasurableSet event →
      |iteratedDeriv 2
          (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0| ≤
        573
  orbitalThird :
    ∀ event : Set (ConcreteMatrixState N), MeasurableSet event → ∀ s : ℝ,
      |s| ≤ 1 / (N : ℝ) →
      |iteratedDeriv 3
          (concreteProjectiveAveragedCenteredCOEEventPath N K event) s| ≤
        306840 * (N : ℝ)

/-- The projectively averaged centered third derivative at the origin has
the exact paper constant `3934 N`. -/
theorem hidingLemmaIII3_orbitalThird_zero
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    |iteratedDeriv 3
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) 0| ≤
      3934 * (N : ℝ) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  rw [coeCorner_centeredProjective_eventPath_derivative_literal_three_internal
    hN (by omega) event hevent]
  rcases hN.eq_or_lt with hNone | hNlt
  · subst N
    have hpoint : (fun A : ConcreteMatrixState 1 ↦
        event.indicator (fun A ↦
          ∫ v : ComplexUnitSphere 1,
            concreteCenteredDensityScore 3 1 K v A
              ∂(complexUnitSphereProbabilityMeasure 1)) A) = 0 := by
      funext A
      simp only [Pi.zero_apply]
      by_cases hmem : A ∈ event
      · simp only [Set.indicator, hmem, if_true]
        exact integral_concreteCenteredDensityScoreThree_fin_one_eq_zero A
      · simp only [Set.indicator, hmem, if_false]
    rw [hpoint]
    change |(∫ _A : ConcreteMatrixState 1, (0 : ℝ) ∂mu)| ≤ _
    simp
  · have hNtwo : 2 ≤ N := by omega
    have hclosed : (fun A ↦ event.indicator (fun A ↦
          ∫ v : ComplexUnitSphere N,
            concreteCenteredDensityScore 3 N K v A
              ∂(complexUnitSphereProbabilityMeasure N)) A) =ᵐ[mu]
        event.indicator (concreteAveragedCenteredCubicDensity N K) := by
      filter_upwards
        [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
          with A hA
      rcases hA with ⟨hsymm, hsupport⟩
      by_cases hmem : A ∈ event
      · simp only [Set.indicator, hmem, if_true]
        exact integral_concreteCenteredDensityScoreThree_eq_density_of_H7Exact
          hN hdense A hsymm hsupport
      · simp only [Set.indicator, hmem, if_false]
    rw [integral_congr_ae hclosed]
    exact (abs_integral_indicator_le_lpNorm_one
        (concreteAveragedCenteredCubicDensity_memLp_one_optimized hN hdense)
        hevent).trans <| by
      simpa [ultraNGeTwoAveragedCenteredCubicNormalizationConstant] using
        concreteAveragedCenteredCubicDensity_lpNorm_one_le_ultraNGeTwo
          hN hdense

/-- Propagation of the exact origin cubic and fourth-score estimates across
the complete paper window `|s| <= 1/N`. -/
theorem hidingLemmaIII3_orbitalThird
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (s : ℝ) (hs : |s| ≤ 1 / (N : ℝ)) :
    |iteratedDeriv 3
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) s| ≤
      306840 * (N : ℝ) := by
  let path := concreteProjectiveAveragedCenteredCOEEventPath N K event
  have hsmooth : ContDiff ℝ 4 path :=
    coeCorner_centeredProjective_eventPath_contDiff_four_H17_proved_from_A1
      hN (by omega) event hevent
  have hzero : |iteratedDeriv 3 path 0| ≤ 3934 * (N : ℝ) :=
    hidingLemmaIII3_orbitalThird_zero hN hdense event hevent
  have hfour : ∀ y ∈ uIcc 0 s,
      |iteratedDeriv 4 path y| ≤ 302906 * (N : ℝ) ^ 2 := by
    intro y _hy
    simpa [combinedSharperFullFourthDensityScoreConstant] using
      abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_combinedSharper
        hN hdense event hevent y
  simpa only [show (3934 : ℝ) + 302906 = 306840 by norm_num] using
    abs_iteratedDeriv_three_le_at_inverse_dimension_of_fourth
      hN (by norm_num : (0 : ℝ) ≤ 302906) hsmooth hzero hfour hs

/-- Lemma III.3, including the two printed smoothness assertions, the exact
first-order orbital cancellation, and all four printed numerical constants. -/
theorem hidingLemmaIII3_eventwise_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    HidingLemmaIII3EventwiseScores N K := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro event hevent
    exact concreteBaseCentralEventPath_smooth hN hdense event hevent
  · intro event hevent
    exact coeCorner_centeredProjective_eventPath_contDiff_four_H17_proved_from_A1
      hN (by omega) event hevent
  · intro event hevent
    simpa [exactVarianceCentralScoreOneConstant] using
      abs_iteratedDeriv_one_concreteBaseCentralEventPath_le_exactVariance
        hN hdense event hevent
  · intro event hevent s
    simpa [exactVarianceCentralScoreTwoConstant] using
      abs_iteratedDeriv_two_concreteBaseCentralEventPath_le_exactVariance
        hN hdense event hevent s
  · intro event hevent
    exact concrete_projectiveAveraged_centered_first_derivative_eq_zero
      hN (by omega) event hevent
  · intro event hevent
    let mu := concreteScaledCOECornerLaw
      canonicalUnitaryHaarProbabilityFamily N K
    rw [concrete_projectiveAveraged_centered_second_derivative_eq_density_indicator_integral_H14Rewire
      hN hdense event hevent]
    letI : IsProbabilityMeasure mu :=
      canonicalScaledCOECornerLaw_isProbability (by omega)
    have hmemOne : MemLp (concreteCenteredQuadraticDensity N K) 1 mu :=
      (concreteCenteredQuadraticDensity_memLp_two_H14Rewire
        hN hdense).mono_exponent (by norm_num)
    exact (abs_integral_indicator_le_lpNorm_one hmemOne hevent).trans <| by
      simpa [exactVarianceOrbitalScoreTwoConstant] using
        concreteCenteredQuadraticDensity_lpNorm_one_le_exactVariance hN hdense
  · intro event hevent s hs
    exact hidingLemmaIII3_orbitalThird hN hdense event hevent s hs

/-- Exact scalar, good-orbital, and bad-event pieces of the one-column step.
The three measures retain the common beta draw used by the actual recursion. -/
structure HidingOneColumnComponentTVBounds (m N : ℕ)
    (mu : Measure (ConcreteMatrixState N)) : Prop where
  scalar : ProbabilityTVLE mu (concreteCentralMixtureLaw m N mu)
    (240 * (N : ℝ) ^ 2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)))
  orbital : ProbabilityTVLE (concreteCentralMixtureLaw m N mu)
    (concreteSharedBetaGoodLaw m N 1 mu)
    (614826 * (N : ℝ) ^ 2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)))
  bad : ProbabilityTVLE (concreteSharedBetaGoodLaw m N 1 mu)
    (concreteSharedBetaFullLaw m N mu)
    (72 * (N : ℝ) ^ 2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)))

/-- Exact componentwise conclusions behind the paper labels
`eq:hide-proposition-four-scalar-use`,
`eq:hide-proposition-four-orbital-use`, and `eq:hide-tail-telescoping`. -/
theorem hidingOneColumnComponentTVBounds_A1A2A3A4
    {N K m : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m)
    (hlarge : 24 * N ^ 2 ≤ m) (hdense : 16 * N ≤ K) :
    HidingOneColumnComponentTVBounds m N
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability hNK
  letI : IsProbabilityMeasure (oneColumnBetaLaw m N) :=
    oneColumnBetaLaw_isProbability hN (hNK.trans hKm)
  have hscore :=
    uniformCanonicalScaledCOESharedBetaScoreCertificate_combinedSharper
      N K m hN hNK hKm hlarge hdense
  have hmom : OneColumnLogMomentBoundsAt 4 5 4 12 m N :=
    oneColumnLogMomentBoundsAt_concrete_of_twentyFour_sq_le hN hlarge
  have hscalarRaw : ProbabilityTVLE mu (concreteCentralMixtureLaw m N mu)
      (oneColumnScalarTaylorBudget 5 44 m N) := by
    have hraw := probabilityTVLE_of_random_scalar_eventPath
      mu (concreteCentralMixtureLaw m N mu) (oneColumnBetaLaw m N)
      (oneColumnCenteredScalarLog m N) (concreteCentralEventPath N mu)
      (5 * (N : ℝ)) (44 * (N : ℝ) ^ 2)
      (by positivity) (by positivity)
      (fun A hA ↦ concreteCentralEventPath_zero mu A hA)
      (fun A hA ↦ concreteCentralMixture_endpoint hN (hNK.trans hKm) mu A hA)
      hscore.scalarSmooth hscore.scalarFirst
      (fun A hA q y hy ↦ hscore.scalarSecond A hA q y hy)
      (fun A hA ↦ concreteCentralMixture_path_integrable
        hN (hNK.trans hKm) mu A hA)
      hmom.centeredScalar_integrable hmom.centeredScalar_sq_integrable
    simpa [oneColumnScalarTaylorBudget,
      exactVarianceCentralScoreOneConstant,
      exactVarianceCentralScoreTwoConstant] using hraw
  have hscalar : ProbabilityTVLE mu (concreteCentralMixtureLaw m N mu)
      (240 * (N : ℝ) ^ 2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) :=
    hscalarRaw.mono <| by
      have hbudget := oneColumnScalarTaylorBudget_le hmom
        (show (0 : ℝ) ≤ 5 by norm_num) (show (0 : ℝ) ≤ 44 by norm_num)
      norm_num at hbudget ⊢
      exact hbudget
  have horbitalBase : ∀ A, MeasurableSet A →
      ∫ q, concreteSharedBetaOrbitalEventPath m N mu q A 0
          ∂(oneColumnBetaLaw m N) =
        (concreteCentralMixtureLaw m N mu).real A := by
    intro A hA
    calc
      ∫ q, concreteSharedBetaOrbitalEventPath m N mu q A 0
          ∂(oneColumnBetaLaw m N) =
          ∫ q, concreteCentralEventPath N mu A
            (oneColumnCenteredScalarLog m N q) ∂(oneColumnBetaLaw m N) := by
              apply integral_congr_ae
              filter_upwards [] with q
              exact concreteSharedBetaOrbitalEventPath_zero_sameBeta hN mu q A hA
      _ = (concreteCentralMixtureLaw m N mu).real A :=
        concreteCentralMixture_endpoint hN (hNK.trans hKm) mu A hA
  have horbitalRaw : ProbabilityTVLE
      (concreteCentralMixtureLaw m N mu)
      (concreteSharedBetaGoodLaw m N 1 mu)
      (573 * (∫ q, concreteGoodOrbitalAmplitude N 1 q ^ 2
          ∂(oneColumnBetaLaw m N)) / 2 +
        (306840 * (N : ℝ)) *
          (∫ q, |concreteGoodOrbitalAmplitude N 1 q| ^ 3
            ∂(oneColumnBetaLaw m N)) / 6) := by
    have hraw := probabilityTVLE_of_correlated_centered_eventPath
      (concreteCentralMixtureLaw m N mu)
      (concreteSharedBetaGoodLaw m N 1 mu) (oneColumnBetaLaw m N)
      (concreteGoodOrbitalAmplitude N 1)
      (concreteSharedBetaOrbitalEventPath m N mu)
      573 (306840 * (N : ℝ))
      (by norm_num) (by positivity)
      horbitalBase
      (fun A hA ↦ concreteSharedBetaGood_endpoint hN (hNK.trans hKm) mu 1 A hA)
      hscore.orbitalSmooth hscore.orbitalFirst hscore.orbitalSecond
      (fun q A hA y hy ↦ by
        simpa [combinedSharperCanonicalOrbitalThirdConstant_eq] using
          hscore.orbitalThird q A hA y hy)
      (fun A hA ↦ concreteSharedBetaZero_path_integrable
        hN (hNK.trans hKm) mu A hA)
      (fun A hA ↦ concreteSharedBetaGood_path_integrable
        hN (hNK.trans hKm) mu 1 A hA)
      (concreteGoodOrbitalAmplitude_sq_integrable hmom 1)
      (concreteGoodOrbitalAmplitude_cube_integrable hmom 1)
    simpa [exactVarianceOrbitalScoreTwoConstant] using hraw
  have horbitalMomentLe :
      573 * (∫ q, concreteGoodOrbitalAmplitude N 1 q ^ 2
        ∂(oneColumnBetaLaw m N)) / 2 +
      (306840 * (N : ℝ)) *
        (∫ q, |concreteGoodOrbitalAmplitude N 1 q| ^ 3
          ∂(oneColumnBetaLaw m N)) / 6 ≤
      oneColumnOrbitalTaylorBudget 573 306840 m N := by
    unfold oneColumnOrbitalTaylorBudget
    exact add_le_add
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (integral_concreteGoodOrbitalAmplitude_sq_le hmom 1)
          (by norm_num)) (by norm_num))
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (integral_abs_concreteGoodOrbitalAmplitude_cube_le hmom 1)
          (by positivity)) (by norm_num))
  have horbitalBudget : oneColumnOrbitalTaylorBudget 573 306840 m N ≤
      614826 * (N : ℝ) ^ 2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
    have hbudget := oneColumnOrbitalTaylorBudget_le hmom
      (show (0 : ℝ) ≤ 573 by norm_num)
      (show (0 : ℝ) ≤ 306840 by norm_num)
    norm_num at hbudget ⊢
    exact hbudget
  have horbital : ProbabilityTVLE
      (concreteCentralMixtureLaw m N mu)
      (concreteSharedBetaGoodLaw m N 1 mu)
      (614826 * (N : ℝ) ^ 2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) :=
    horbitalRaw.mono (horbitalMomentLe.trans horbitalBudget)
  have hbadRaw := probabilityTVLE_concreteSharedBetaGood_full
    hN (hNK.trans hKm) mu 1 (by norm_num)
  have hlargeR : 24 * (N : ℝ) ^ 2 ≤ (m : ℝ) := by
    exact_mod_cast hlarge
  have htail := oneColumnLogBadProbability_le_telescopingRate_concrete
    hN (hNK.trans hKm) hlargeR
  have hbad : ProbabilityTVLE (concreteSharedBetaGoodLaw m N 1 mu)
      (concreteSharedBetaFullLaw m N mu)
      (72 * (N : ℝ) ^ 2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) :=
    hbadRaw.mono <| by
      simpa [denseTelescopingRate] using htail
  exact ⟨hscalar, horbital, hbad⟩

/-- Exact evaluated one-column total-variation bound, before radial
propagation.  The arithmetic is `240 + 614826 + 72 = 615138`. -/
theorem hidingOneColumnTVLE_615138_A1A2A3A4
    {N K m : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m)
    (hlarge : 24 * N ^ 2 ≤ m) (hdense : 16 * N ≤ K) :
    ProbabilityTVLE
      (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K)
      (concreteSharedBetaFullLaw m N
        (concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K))
      (615138 * (N : ℝ) ^ 2 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  have h := hidingOneColumnComponentTVBounds_A1A2A3A4
    hN hNK hKm hlarge hdense
  exact (probabilityTVLE_triangle
    (probabilityTVLE_triangle h.scalar h.orbital) h.bad).mono <| by
    ring_nf
    exact le_rfl

/-- Paper Eq. `eq:hide-one-step-taylor-decomposition`: the exact scalar,
correlated orbital, and exceptional event pieces, together with their sharp
square base total.  The two Taylor formulas themselves are supplied by
`probabilityTVLE_of_random_scalar_eventPath` and
`probabilityTVLE_of_correlated_centered_eventPath`. -/
theorem eq_hide_one_step_taylor_decomposition_A1A2A3A4
    {N K m : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K) (hKm : K ≤ m)
    (hlarge : 24 * N ^ 2 ≤ m) (hdense : 16 * N ≤ K) :
    HidingOneColumnComponentTVBounds m N
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) ∧
      ProbabilityTVLE
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K)
        (concreteSharedBetaFullLaw m N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K))
        (615138 * (N : ℝ) ^ 2 /
          ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) := by
  exact ⟨hidingOneColumnComponentTVBounds_A1A2A3A4
      hN hNK hKm hlarge hdense,
    hidingOneColumnTVLE_615138_A1A2A3A4
      hN hNK hKm hlarge hdense⟩

/-! ## Primitive fourth-score moment ledger printed in Appendix D -/

/-- Paper Eq. `hide-fourth-ell-one-fourth-moment`: the literal product-law
fourth moment of the first centered logarithmic score. -/
theorem eq_hide_fourth_ell_one_fourth_moment_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 4) 1
        (concreteCenteredScoreProductLaw N K) ≤
      3151 * (N : ℝ) ^ 2 := by
  simpa [h12SharpProjectiveFourthMomentConstant] using
    centeredLogScore_oneFourth_lpNorm_one_le_sharp_proved_A1A2A3A4
      hN hdense

/-- Paper Eq. `hide-fourth-ell-two-square-moment`: the literal product-law
second moment of the second centered logarithmic score. -/
theorem eq_hide_fourth_ell_two_square_moment_A1A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun p ↦ concreteCenteredEll 2 N K p ^ 2) 1
        (concreteCenteredScoreProductLaw N K) ≤
      9990 * (N : ℝ) ^ 2 := by
  simpa [h14DirectExactSharpEnvelopeConstant] using
    (centeredLogScore_twoSquare_momentPackage_directExact_A1A2A3
      hN (by omega)).2 hdense

/-- Paper Eq. `hide-fourth-ell-one-three-moment`: the literal product-law
absolute mixed first/third centered logarithmic-score moment. -/
theorem eq_hide_fourth_ell_one_three_moment_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
        concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ≤
      (6773469 / 320 : ℝ) * (N : ℝ) ^ 2 := by
  have h :=
    (centeredLogScore_oneThree_momentPackage_combinedSharp_A1A2A3A4
      hN (by omega)).2 hdense
  rw [h13CombinedSharpProjectiveEnvelopeConstant_eq] at h
  exact h

#print axioms hidingLemmaIII3_eventwise_A1A2A3A4
#print axioms hidingOneColumnComponentTVBounds_A1A2A3A4
#print axioms hidingOneColumnTVLE_615138_A1A2A3A4
#print axioms eq_hide_one_step_taylor_decomposition_A1A2A3A4
#print axioms eq_hide_fourth_ell_one_fourth_moment_A1A2A3A4
#print axioms eq_hide_fourth_ell_two_square_moment_A1A2A3
#print axioms eq_hide_fourth_ell_one_three_moment_A1A2A3A4
#print axioms eq_hide_congruence_action
#print axioms eq_hide_radial_one_column_commute
#print axioms eq_hide_radial_TV

end

end LogdetLean.GramHafnian.ThreePaper.Verification
