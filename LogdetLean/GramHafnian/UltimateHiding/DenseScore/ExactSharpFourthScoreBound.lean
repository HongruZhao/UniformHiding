import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_SharpProjectiveFourthBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_DirectExactSharpEnvelopeBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_ScaleTwoProjectiveBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.HyperSharpFourthScoreBound
import Mathlib.Tactic

/-!
# Exact sharp fourth-score bound

This assembly uses the separately checked sharp packages

* H12: `3151`,
* H14: `9990`,
* H13: `52204`.

Thus the lower Bell polynomial costs
`4*3151 + 6*9990 + 4*52204 = 281360`, and fixed-fibre normalization gives
the complete fourth density-score constant `562720`.
-/

open MeasureTheory Filter Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
open LogdetLean.GramHafnian.LocalAnticoncentration

def exactSharpLowerBellFourthConstant : ℝ :=
  4 * h12SharpProjectiveFourthMomentConstant +
    6 * h14DirectExactSharpEnvelopeConstant +
    4 * h13ScaleTwoProjectiveEnvelopeConstant

def exactSharpFullFourthDensityScoreConstant : ℝ :=
  2 * exactSharpLowerBellFourthConstant

theorem exactSharpLowerBellFourthConstant_eq :
    exactSharpLowerBellFourthConstant = 281360 := by
  norm_num [exactSharpLowerBellFourthConstant,
    h12SharpProjectiveFourthMomentConstant,
    h14DirectExactSharpEnvelopeConstant,
    h13ScaleTwoProjectiveEnvelopeConstant]

theorem exactSharpFullFourthDensityScoreConstant_eq :
    exactSharpFullFourthDensityScoreConstant = 562720 := by
  rw [exactSharpFullFourthDensityScoreConstant,
    exactSharpLowerBellFourthConstant_eq]
  norm_num

theorem concreteCenteredBellFourLowerProduct_momentPackage_exactSharp
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredBellFourLowerProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredBellFourLowerProduct N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          exactSharpLowerBellFourthConstant * (N : ℝ) ^ 2) := by
  let law := concreteCenteredScoreProductLaw N K
  let f1 : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 1 N K p ^ 4
  let f2 : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 2 N K p ^ 2
  let f13 : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 1 N K p * concreteCenteredEll 3 N K p
  let envelope : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    (4 : ℝ) • f1 + (6 : ℝ) • f2 +
      (4 : ℝ) • (fun p ↦ ‖f13 p‖)
  have hOne :=
    centeredLogScore_oneFourth_momentPackage_sharp_proved_A1A2A3A4
      hN hgap
  have hTwo :=
    centeredLogScore_twoSquare_momentPackage_directExact_A1A2A3 hN hgap
  have hOneThree :=
    centeredLogScore_oneThree_momentPackage_scaleTwo_A1A2A3A4 hN hgap
  have hf1 : MemLp f1 1 law := by simpa only [f1, law] using hOne.1
  have hf2 : MemLp f2 1 law := by simpa only [f2, law] using hTwo.1
  have hf13 : MemLp f13 1 law := by
    simpa only [f13, law] using hOneThree.1
  have he1 : MemLp ((4 : ℝ) • f1) 1 law := hf1.const_smul 4
  have he2 : MemLp ((6 : ℝ) • f2) 1 law := hf2.const_smul 6
  have he13 : MemLp ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law :=
    hf13.norm.const_smul 4
  have hEnvelope : MemLp envelope 1 law := (he1.add he2).add he13
  have hdom : ∀ p, ‖concreteCenteredBellFourLowerProduct N K p‖ ≤
      envelope p := by
    intro p
    simpa only [envelope, f1, f2, f13, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.norm_eq_abs] using
      concreteCenteredBellFourLowerProduct_norm_le_sharpEnvelope
        (N := N) (K := K) p
  have hLower : MemLp (concreteCenteredBellFourLowerProduct N K) 1 law := by
    simpa only [law] using
      (concreteCenteredBellFourLowerProduct_momentPackage_hyper hN hgap).1
  refine ⟨by simpa only [law] using hLower, ?_⟩
  intro hdense
  have hf1Bound : lpNorm f1 1 law ≤
      h12SharpProjectiveFourthMomentConstant * (N : ℝ) ^ 2 := by
    simpa only [f1, law] using hOne.2 hdense
  have hf2Bound : lpNorm f2 1 law ≤
      h14DirectExactSharpEnvelopeConstant * (N : ℝ) ^ 2 := by
    simpa only [f2, law] using hTwo.2 hdense
  have hf13Bound : lpNorm f13 1 law ≤
      h13ScaleTwoProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
    simpa only [f13, law] using hOneThree.2 hdense
  have hmono : lpNorm (concreteCenteredBellFourLowerProduct N K) 1 law ≤
      lpNorm envelope 1 law := lpNorm_mono_real hEnvelope hdom
  have hsum1 : lpNorm (((4 : ℝ) • f1) + (6 : ℝ) • f2) 1 law ≤
      lpNorm ((4 : ℝ) • f1) 1 law + lpNorm ((6 : ℝ) • f2) 1 law :=
    lpNorm_add_le he1 (by norm_num)
  have hsum2 : lpNorm envelope 1 law ≤
      lpNorm (((4 : ℝ) • f1) + (6 : ℝ) • f2) 1 law +
        lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law :=
    lpNorm_add_le (he1.add he2) (by norm_num)
  have hsum : lpNorm envelope 1 law ≤
      lpNorm ((4 : ℝ) • f1) 1 law + lpNorm ((6 : ℝ) • f2) 1 law +
        lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := by
    calc
      _ ≤ lpNorm (((4 : ℝ) • f1) + (6 : ℝ) • f2) 1 law +
          lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := hsum2
      _ ≤ (lpNorm ((4 : ℝ) • f1) 1 law +
            lpNorm ((6 : ℝ) • f2) 1 law) +
          lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := by gcongr
  have hscaled :
      lpNorm ((4 : ℝ) • f1) 1 law + lpNorm ((6 : ℝ) • f2) 1 law +
          lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law =
        4 * lpNorm f1 1 law + 6 * lpNorm f2 1 law +
          4 * lpNorm f13 1 law := by
    rw [lpNorm_const_smul, lpNorm_const_smul, lpNorm_const_smul,
      lpNorm_norm hf13.aestronglyMeasurable]
    norm_num
  have hcoeff :
      4 * lpNorm f1 1 law + 6 * lpNorm f2 1 law +
          4 * lpNorm f13 1 law ≤
        exactSharpLowerBellFourthConstant * (N : ℝ) ^ 2 := by
    unfold exactSharpLowerBellFourthConstant
    nlinarith [hf1Bound, hf2Bound, hf13Bound]
  change lpNorm (concreteCenteredBellFourLowerProduct N K) 1 law ≤ _
  exact hmono.trans (hsum.trans_eq hscaled) |>.trans hcoeff

theorem centeredLogScore_four_momentPackage_exactSharp
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredEll 4 N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          exactSharpLowerBellFourthConstant * (N : ℝ) ^ 2) := by
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
    exact (h11FourthLogScoreNonpositiveOnSupport_proved hN hgap).nonpos_on_support
      A v hA.1 hA.2
  have hlowerMem : MemLp lower 1 (μ.prod ν) := by
    simpa only [lower, μ, ν, concreteCenteredScoreProductLaw] using
      (concreteCenteredBellFourLowerProduct_momentPackage_exactSharp
        hN hgap).1
  have hlowerInt : Integrable lower (μ.prod ν) :=
    memLp_one_iff_integrable.mp hlowerMem
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
    have hle := H.2.trans
      ((concreteCenteredBellFourLowerProduct_momentPackage_exactSharp
        hN hgap).2 hdense)
    simpa only [score, lower, μ, ν, concreteCenteredScoreProductLaw] using hle

theorem concreteCenteredBellFourProduct_memLp_one_exactSharp
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCenteredBellFourProduct N K) 1
      (concreteCenteredScoreProductLaw N K) :=
  concreteCenteredBellFourProduct_memLp_one_hyper hN hdense

theorem concreteCenteredBellFourProduct_lpNorm_one_le_exactSharp
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredBellFourProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ≤
      exactSharpFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let lower := concreteCenteredBellFourLowerProduct N K
  let fourth := concreteCenteredEll 4 N K
  let law := concreteCenteredScoreProductLaw N K
  have hpoint : concreteCenteredBellFourProduct N K = lower + fourth := by
    funext p
    simp only [lower, fourth, concreteCenteredBellFourProduct,
      concreteCenteredBellFourLowerProduct, densityBellFour, Pi.add_apply]
  have hlower :=
    (concreteCenteredBellFourLowerProduct_momentPackage_exactSharp
      (N := N) (K := K) hN hgap).1
  have hlowerBound :=
    (concreteCenteredBellFourLowerProduct_momentPackage_exactSharp
      (N := N) (K := K) hN hgap).2 hdense
  have hfourth := (centeredLogScore_four_momentPackage_exactSharp
    (N := N) (K := K) hN hgap).1
  have hfourthBound := (centeredLogScore_four_momentPackage_exactSharp
    (N := N) (K := K) hN hgap).2 hdense
  rw [hpoint]
  calc
    lpNorm (lower + fourth) 1 law ≤
        lpNorm lower 1 law + lpNorm fourth 1 law :=
      lpNorm_add_le hlower (by norm_num)
    _ ≤ exactSharpFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
      unfold exactSharpFullFourthDensityScoreConstant
      nlinarith

theorem concreteCenteredDensityScoreFourProduct_memLp_one_exactSharp
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) :=
  concreteCenteredDensityScoreFourProduct_memLp_one_hyper hN hdense

theorem concreteCenteredDensityScoreFourProduct_lpNorm_one_le_exactSharp
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm
        (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
          concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
        (concreteCenteredScoreProductLaw N K) ≤
      exactSharpFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 4 N K Av.2 Av.1
  let bell := concreteCenteredBellFourProduct N K
  let law := concreteCenteredScoreProductLaw N K
  have heq : score =ᵐ[law] bell :=
    concreteCenteredDensityScoreFourProduct_ae_eq_Bell hN hdense
  have hscore : MemLp score 1 law :=
    concreteCenteredDensityScoreFourProduct_memLp_one_exactSharp hN hdense
  have hbell : MemLp bell 1 law :=
    concreteCenteredBellFourProduct_memLp_one_exactSharp hN hdense
  have hnorm : lpNorm score 1 law = lpNorm bell 1 law := by
    rw [lpNorm_one_eq_integral_norm hscore.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hbell.aestronglyMeasurable]
    exact integral_congr_ae <| heq.mono fun Av hAv ↦ congrArg norm hAv
  rw [hnorm]
  exact concreteCenteredBellFourProduct_lpNorm_one_le_exactSharp hN hdense

theorem abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_exactSharp
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    |iteratedDeriv 4
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y| ≤
      exactSharpFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  have hraw :=
    abs_coeCorner_centeredProjective_eventPath_derivative_at_le_lpNorm_one
      hN (by omega) (by omega) event hevent y
      (concreteCenteredDensityScoreFourProduct_memLp_one_exactSharp hN hdense)
  exact hraw.trans
    (concreteCenteredDensityScoreFourProduct_lpNorm_one_le_exactSharp
      hN hdense)

theorem abs_iteratedDeriv_four_concreteSharedBetaOrbitalEventPath_le_exactSharp
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    |iteratedDeriv 4
        (concreteSharedBetaOrbitalEventPath m N
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K)
            q event) y| ≤
      exactSharpFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  let preevent := concreteCentralMatrixUpdate N
    (oneColumnCenteredScalarLog m N q) ⁻¹' event
  have hpre : MeasurableSet preevent :=
    (measurable_concreteCentralMatrixUpdate N _) hevent
  have hfun :
      concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)
          q event =
        concreteProjectiveAveragedCenteredCOEEventPath N K preevent := by
    funext t
    exact concreteSharedBetaOrbitalEventPath_eq_projectiveCenteredCOE
      hN (by omega) q event hevent t
  rw [hfun]
  exact
    abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_exactSharp
      hN hdense preevent hpre y

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
