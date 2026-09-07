import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_OneSidedFourthBellNormalizationReducer
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ExactSharpFourthScoreBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_CombinedSharpProjectiveBound
import Mathlib.Tactic

/-!
# Combined sharper fourth-score bound

The exact SOS envelope

`(19/3) ellOne^4 + (75/16) ellTwo^2 + 4 |ellOne ellThree|`

uses the combined-sharp H13 coefficient `6773469/320`.  Its positive-part
budget is `36348677/240`; doubling gives `36348677/120 < 302906`, so the
complete fourth density score is bounded by the integer constant `302906`.
-/

open MeasureTheory Filter Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
open LogdetLean.GramHafnian.CurrentPRL

def combinedSharperLowerBellPositiveConstant : ℝ := 36348677 / 240

def combinedSharperFullFourthDensityScoreConstant : ℝ := 302906

theorem combinedSharperLowerBellPositiveConstant_eq :
    combinedSharperLowerBellPositiveConstant = 36348677 / 240 := rfl

theorem combinedSharperFullFourthDensityScoreConstant_eq :
    combinedSharperFullFourthDensityScoreConstant = 302906 := rfl

theorem two_mul_combinedSharperLowerBellPositiveConstant_le_full :
    2 * combinedSharperLowerBellPositiveConstant ≤
      combinedSharperFullFourthDensityScoreConstant := by
  norm_num [combinedSharperLowerBellPositiveConstant,
    combinedSharperFullFourthDensityScoreConstant]

/-- The SOS envelope is integrable and spends exactly the rational
positive-part budget before the final integer ceiling. -/
theorem concreteCenteredBellFourPositiveSOSEnvelope_momentPackage_combinedSharper
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredBellFourPositiveSOSEnvelope N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredBellFourPositiveSOSEnvelope N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          combinedSharperLowerBellPositiveConstant * (N : ℝ) ^ 2) := by
  let law := concreteCenteredScoreProductLaw N K
  let f1 : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 1 N K p ^ 4
  let f2 : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 2 N K p ^ 2
  let f13 : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun p ↦ concreteCenteredEll 1 N K p * concreteCenteredEll 3 N K p
  let envelope : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    (19 / 3 : ℝ) • f1 + (75 / 16 : ℝ) • f2 +
      (4 : ℝ) • (fun p ↦ ‖f13 p‖)
  have hOne :=
    centeredLogScore_oneFourth_momentPackage_sharp_proved_A1A2A3A4
      hN hgap
  have hTwo :=
    centeredLogScore_twoSquare_momentPackage_directExact_A1A2A3 hN hgap
  have hOneThree :=
    centeredLogScore_oneThree_momentPackage_combinedSharp_A1A2A3A4 hN hgap
  have hf1 : MemLp f1 1 law := by simpa only [f1, law] using hOne.1
  have hf2 : MemLp f2 1 law := by simpa only [f2, law] using hTwo.1
  have hf13 : MemLp f13 1 law := by
    simpa only [f13, law] using hOneThree.1
  have he1 : MemLp ((19 / 3 : ℝ) • f1) 1 law :=
    hf1.const_smul (19 / 3)
  have he2 : MemLp ((75 / 16 : ℝ) • f2) 1 law :=
    hf2.const_smul (75 / 16)
  have he13 : MemLp ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law :=
    hf13.norm.const_smul 4
  have hEnvelope : MemLp envelope 1 law := (he1.add he2).add he13
  have hEnvelopeEq :
      concreteCenteredBellFourPositiveSOSEnvelope N K = envelope := by
    funext p
    simp only [concreteCenteredBellFourPositiveSOSEnvelope, envelope,
      f1, f2, f13, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Real.norm_eq_abs]
  constructor
  · rw [hEnvelopeEq]
    exact hEnvelope
  · intro hdense
    have hf1Bound : lpNorm f1 1 law ≤
        h12SharpProjectiveFourthMomentConstant * (N : ℝ) ^ 2 := by
      simpa only [f1, law] using hOne.2 hdense
    have hf2Bound : lpNorm f2 1 law ≤
        h14DirectExactSharpEnvelopeConstant * (N : ℝ) ^ 2 := by
      simpa only [f2, law] using hTwo.2 hdense
    have hf13Bound : lpNorm f13 1 law ≤
        h13CombinedSharpProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
      simpa only [f13, law] using hOneThree.2 hdense
    have hsum1 :
        lpNorm (((19 / 3 : ℝ) • f1) + (75 / 16 : ℝ) • f2) 1 law ≤
          lpNorm ((19 / 3 : ℝ) • f1) 1 law +
            lpNorm ((75 / 16 : ℝ) • f2) 1 law :=
      lpNorm_add_le he1 (by norm_num)
    have hsum2 : lpNorm envelope 1 law ≤
        lpNorm (((19 / 3 : ℝ) • f1) + (75 / 16 : ℝ) • f2) 1 law +
          lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law :=
      lpNorm_add_le (he1.add he2) (by norm_num)
    have hsum : lpNorm envelope 1 law ≤
        lpNorm ((19 / 3 : ℝ) • f1) 1 law +
          lpNorm ((75 / 16 : ℝ) • f2) 1 law +
          lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := by
      calc
        _ ≤ lpNorm (((19 / 3 : ℝ) • f1) + (75 / 16 : ℝ) • f2) 1 law +
            lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := hsum2
        _ ≤ (lpNorm ((19 / 3 : ℝ) • f1) 1 law +
              lpNorm ((75 / 16 : ℝ) • f2) 1 law) +
            lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := by
          gcongr
    have hscaled :
        lpNorm ((19 / 3 : ℝ) • f1) 1 law +
            lpNorm ((75 / 16 : ℝ) • f2) 1 law +
            lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law =
          (19 / 3 : ℝ) * lpNorm f1 1 law +
            (75 / 16 : ℝ) * lpNorm f2 1 law +
            4 * lpNorm f13 1 law := by
      rw [lpNorm_const_smul, lpNorm_const_smul, lpNorm_const_smul,
        lpNorm_norm hf13.aestronglyMeasurable]
      norm_num
    have hcoeff :
        (19 / 3 : ℝ) * lpNorm f1 1 law +
            (75 / 16 : ℝ) * lpNorm f2 1 law +
            4 * lpNorm f13 1 law ≤
          combinedSharperLowerBellPositiveConstant * (N : ℝ) ^ 2 := by
      rw [h13CombinedSharpProjectiveEnvelopeConstant_eq] at hf13Bound
      norm_num [combinedSharperLowerBellPositiveConstant,
        h12SharpProjectiveFourthMomentConstant,
        h14DirectExactSharpEnvelopeConstant] at hf1Bound hf2Bound hf13Bound ⊢
      nlinarith
    rw [hEnvelopeEq]
    simpa only [law] using hsum.trans_eq hscaled |>.trans hcoeff

/-- The complete fourth Bell score, using only the positive-part budget and
the fixed-fibre zero-mean identity. -/
theorem concreteCenteredBellFourProduct_lpNorm_one_le_combinedSharper
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredBellFourProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ≤
      combinedSharperFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let nu := complexUnitSphereProbabilityMeasure N
  let density : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 4 N K Av.2 Av.1
  let score := concreteCenteredEll 4 N K
  let lower := concreteCenteredBellFourLowerProduct N K
  let envelope := concreteCenteredBellFourPositiveSOSEnvelope N K
  let law := concreteCenteredScoreProductLaw N K
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega : N ≤ K)
  letI : IsProbabilityMeasure nu :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hsupport : ∀ᵐ A ∂mu,
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
    simpa only [mu] using
      friedmanMello1985_scaledCOECorner_ae_support_from_density
        hN (by omega : 2 * N ≤ K)
  have hBell : ∀ v, (fun A ↦ density (A, v)) =ᵐ[mu]
      (fun A ↦ lower (A, v) + score (A, v)) := by
    intro v
    filter_upwards [hsupport] with A hA
    rcases hA with ⟨hSymm, hSupp⟩
    have h := coeCorner_centeredDensityScore_four_eq_Bell_external_derived
      hN hgap v A hSymm hSupp
    simpa only [density, lower, score, concreteCenteredBellFourLowerProduct,
      concreteCenteredEll, densityBellFour] using h
  have hnonpos : ∀ v, ∀ᵐ A ∂mu, score (A, v) ≤ 0 := by
    intro v
    filter_upwards [hsupport] with A hA
    exact (h11FourthLogScoreNonpositiveOnSupport_proved hN hgap).nonpos_on_support
      A v hA.1 hA.2
  have hlowerMem : MemLp lower 1 (mu.prod nu) := by
    simpa only [lower, mu, nu, concreteCenteredScoreProductLaw] using
      (concreteCenteredBellFourLowerProduct_momentPackage_exactSharp
        hN hgap).1
  have hlowerInt : Integrable lower (mu.prod nu) :=
    memLp_one_iff_integrable.mp hlowerMem
  have henvelopeMem : MemLp envelope 1 (mu.prod nu) := by
    simpa only [envelope, mu, nu, concreteCenteredScoreProductLaw] using
      (concreteCenteredBellFourPositiveSOSEnvelope_momentPackage_combinedSharper
        hN hgap).1
  have henvelopeInt : Integrable envelope (mu.prod nu) :=
    memLp_one_iff_integrable.mp henvelopeMem
  have Hone :=
    integrable_and_lpNorm_one_le_two_mul_integral_envelope_of_fiber_normalization_nonpos
      (mu := mu) (nu := nu) (density := density) (score := score)
      (lower := lower) (envelope := envelope)
      ((measurable_concreteCenteredEll_four (N := N) (K := K) hN)
        |>.aestronglyMeasurable)
      hlowerInt henvelopeInt
      (fun v ↦ by
        simpa only [density, mu] using
          integrable_concreteCenteredDensityScore_four_fixedDirection_literal_from_A1
            hN hgap v)
      (fun v ↦ by
        simpa only [density, mu] using
          integral_concreteCenteredDensityScore_four_fixedDirection_eq_zero_from_A1
            hN hgap v)
      hBell hnonpos
      (fun v ↦ Filter.Eventually.of_forall fun A ↦ by
        simpa only [lower, envelope] using
          concreteCenteredBellFourLowerProduct_posPart_le_sosEnvelope
            (N := N) (K := K) (A, v))
  have henvelopeIntegralLe :
      (∫ z, envelope z ∂(mu.prod nu)) ≤ lpNorm envelope 1 (mu.prod nu) := by
    rw [lpNorm_one_eq_integral_norm henvelopeMem.aestronglyMeasurable]
    exact integral_mono henvelopeInt henvelopeInt.norm fun z ↦ Real.le_norm_self _
  have henvelopeBound : lpNorm envelope 1 (mu.prod nu) ≤
      combinedSharperLowerBellPositiveConstant * (N : ℝ) ^ 2 := by
    simpa only [envelope, mu, nu, concreteCenteredScoreProductLaw] using
      (concreteCenteredBellFourPositiveSOSEnvelope_momentPackage_combinedSharper
        hN hgap).2 hdense
  have hpoint : concreteCenteredBellFourProduct N K = lower + score := by
    funext p
    simp only [lower, score, concreteCenteredBellFourProduct,
      concreteCenteredBellFourLowerProduct, densityBellFour, Pi.add_apply]
  rw [hpoint]
  change lpNorm (lower + score) 1 (mu.prod nu) ≤ _
  calc
    lpNorm (lower + score) 1 (mu.prod nu) ≤
        2 * ∫ z, envelope z ∂(mu.prod nu) := Hone.2
    _ ≤ 2 * lpNorm envelope 1 (mu.prod nu) := by
      gcongr
    _ ≤ 2 * combinedSharperLowerBellPositiveConstant * (N : ℝ) ^ 2 := by
      nlinarith
    _ ≤ combinedSharperFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
      have hN2 : 0 ≤ (N : ℝ) ^ 2 := sq_nonneg _
      nlinarith [two_mul_combinedSharperLowerBellPositiveConstant_le_full]

theorem concreteCenteredBellFourProduct_memLp_one_combinedSharper
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCenteredBellFourProduct N K) 1
      (concreteCenteredScoreProductLaw N K) :=
  concreteCenteredBellFourProduct_memLp_one_exactSharp hN hdense

theorem concreteCenteredDensityScoreFourProduct_memLp_one_combinedSharper
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) :=
  concreteCenteredDensityScoreFourProduct_memLp_one_exactSharp hN hdense

theorem concreteCenteredDensityScoreFourProduct_lpNorm_one_le_combinedSharper
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm
        (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
          concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
        (concreteCenteredScoreProductLaw N K) ≤
      combinedSharperFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  let density : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 4 N K Av.2 Av.1
  let bell := concreteCenteredBellFourProduct N K
  let law := concreteCenteredScoreProductLaw N K
  have heq : density =ᵐ[law] bell :=
    concreteCenteredDensityScoreFourProduct_ae_eq_Bell hN hdense
  have hdensity : MemLp density 1 law :=
    concreteCenteredDensityScoreFourProduct_memLp_one_combinedSharper hN hdense
  have hbell : MemLp bell 1 law :=
    concreteCenteredBellFourProduct_memLp_one_combinedSharper hN hdense
  have hnorm : lpNorm density 1 law = lpNorm bell 1 law := by
    rw [lpNorm_one_eq_integral_norm hdensity.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hbell.aestronglyMeasurable]
    exact integral_congr_ae <| heq.mono fun Av hAv ↦ congrArg norm hAv
  rw [hnorm]
  exact concreteCenteredBellFourProduct_lpNorm_one_le_combinedSharper hN hdense

theorem abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_combinedSharper
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    |iteratedDeriv 4
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y| ≤
      combinedSharperFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  have hraw :=
    abs_coeCorner_centeredProjective_eventPath_derivative_at_le_lpNorm_one
      hN (by omega) (by omega) event hevent y
      (concreteCenteredDensityScoreFourProduct_memLp_one_combinedSharper hN hdense)
  exact hraw.trans
    (concreteCenteredDensityScoreFourProduct_lpNorm_one_le_combinedSharper
      hN hdense)

theorem abs_iteratedDeriv_four_concreteSharedBetaOrbitalEventPath_le_combinedSharper
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    |iteratedDeriv 4
        (concreteSharedBetaOrbitalEventPath m N
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K)
            q event) y| ≤
      combinedSharperFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
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
    abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_combinedSharper
      hN hdense preevent hpre y

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
