import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_UltraSharpProjectiveEnvelopeBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.OptimizedFourthScoreBound
import Mathlib.Tactic

/-!
# Ultra-sharp fourth-score bound

This module retains the pre-relaxation H14 radial constant `2^17`, transports
the corresponding `16`-scaled H13 envelope, and reassembles the complete
fourth Bell polynomial.  The final fourth-score constant is `77346111488`.
-/

open MeasureTheory Filter Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
open LogdetLean.GramHafnian.CurrentPRL

def h13UltraRelaxedProjectiveEnvelopeConstant : ℝ :=
  16 * h14UltraProjectiveEnvelopeConstant

def ultraSharpLowerBellFourthConstant : ℝ :=
  4 * (2 : ℝ) ^ 28 +
    6 * h14UltraProjectiveEnvelopeConstant +
    4 * h13UltraRelaxedProjectiveEnvelopeConstant

def ultraSharpFullFourthDensityScoreConstant : ℝ :=
  2 * ultraSharpLowerBellFourthConstant

theorem h13UltraRelaxedProjectiveEnvelopeConstant_eq :
    h13UltraRelaxedProjectiveEnvelopeConstant = 8594128896 := by
  norm_num [h13UltraRelaxedProjectiveEnvelopeConstant,
    h14UltraProjectiveEnvelopeConstant,
    h14UltraNormalizedFourthRemainderConstant,
    h14BetaPrimeProjectiveLowerMomentConstant]

theorem ultraSharpLowerBellFourthConstant_eq :
    ultraSharpLowerBellFourthConstant = 38673055744 := by
  norm_num [ultraSharpLowerBellFourthConstant,
    h13UltraRelaxedProjectiveEnvelopeConstant,
    h14UltraProjectiveEnvelopeConstant,
    h14UltraNormalizedFourthRemainderConstant,
    h14BetaPrimeProjectiveLowerMomentConstant]

theorem ultraSharpFullFourthDensityScoreConstant_eq :
    ultraSharpFullFourthDensityScoreConstant = 77346111488 := by
  rw [ultraSharpFullFourthDensityScoreConstant,
    ultraSharpLowerBellFourthConstant_eq]
  norm_num

/-! ## H13 ultra-sharp expectation and product transport -/

theorem h13RelaxedProjectiveEnvelope_momentPackage_ultra_A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h13RelaxedProjectiveEnvelope N K)
        (higherScoreMatrixLaw N K) ∧
      (16 * N ≤ K →
        (∫ A, h13RelaxedProjectiveEnvelope N K A
            ∂higherScoreMatrixLaw N K) ≤
          h13UltraRelaxedProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  have H := h14ProjectiveCancellationEnvelope_momentPackage_ultra_A2A3
    hN hgap
  have hInt : Integrable
      (fun A : ConcreteMatrixState N ↦
        16 * h14ProjectiveCancellationEnvelope N K A)
      (higherScoreMatrixLaw N K) := H.1.const_mul 16
  constructor
  · change Integrable
      (fun A : ConcreteMatrixState N ↦
        16 * h14ProjectiveCancellationEnvelope N K A)
      (higherScoreMatrixLaw N K)
    exact hInt
  · intro hdense
    have hbound := mul_le_mul_of_nonneg_left (H.2 hdense)
      (show (0 : ℝ) ≤ 16 by norm_num)
    change
      (∫ A, 16 * h14ProjectiveCancellationEnvelope N K A
        ∂higherScoreMatrixLaw N K) ≤ _
    rw [integral_const_mul]
    calc
      16 * (∫ A, h14ProjectiveCancellationEnvelope N K A
          ∂higherScoreMatrixLaw N K) ≤
        16 * (h14UltraProjectiveEnvelopeConstant * (N : ℝ) ^ 2) :=
          hbound
      _ = h13UltraRelaxedProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
        unfold h13UltraRelaxedProjectiveEnvelopeConstant
        ring

theorem centeredLogScore_oneThree_momentPackage_relaxed_ultra_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p *
      concreteCenteredEll 3 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p *
          concreteCenteredEll 3 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          h13UltraRelaxedProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := by
  let μ : Measure (ConcreteMatrixState N) := higherScoreMatrixLaw N K
  let sphere : Measure (ComplexUnitSphere N) := higherScoreSphereLaw N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ := fun p ↦
    concreteCenteredEll 1 N K p * concreteCenteredEll 3 N K p
  let envelope : ConcreteMatrixState N → ℝ :=
    h13RelaxedProjectiveEnvelope N K
  letI : IsProbabilityMeasure μ :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have Hprojective :=
    h13HigherScoreProjectiveFirstEnvelope_of_relaxedTraceWordContract
      hN hgap (h13OneThreeRelaxedTraceWordProjectiveContraction_proved N K)
  have hscoreMeas : AEStronglyMeasurable score (μ.prod sphere) :=
    Hprojective.measurable_score.aestronglyMeasurable
  have hSupport : ∀ᵐ A ∂μ,
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
    simpa only [μ, higherScoreMatrixLaw] using
      friedmanMello1985_scaledCOECorner_ae_support_from_density
        hN (by omega : 2 * N ≤ K)
  have hSlices : ∀ᵐ A ∂μ,
      Integrable (fun v ↦ score (A, v)) sphere ∧
        (∫ v, ‖score (A, v)‖ ∂sphere) ≤ envelope A := by
    filter_upwards [hSupport] with A hA
    simpa only [score, sphere, envelope] using
      Hprojective.fixedMatrix_package A hA.1 hA.2
  have hEnvelope :=
    h13RelaxedProjectiveEnvelope_momentPackage_ultra_A2A3 hN hgap
  have hEnvelopeInt : Integrable envelope μ := by
    simpa only [envelope, μ, higherScoreMatrixLaw] using hEnvelope.1
  have hInnerMeas : AEStronglyMeasurable
      (fun A ↦ ∫ v, ‖score (A, v)‖ ∂sphere) μ :=
    hscoreMeas.norm.integral_prod_right'
  have hInnerInt : Integrable
      (fun A ↦ ∫ v, ‖score (A, v)‖ ∂sphere) μ := by
    apply hEnvelopeInt.mono hInnerMeas
    filter_upwards [hSlices] with A hA
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
      Real.norm_eq_abs,
      abs_of_nonneg (h13RelaxedProjectiveEnvelope_nonneg N K A)]
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
        h13UltraRelaxedProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
      calc
        lpNorm score 1 (μ.prod sphere) =
            ∫ A, ∫ v, ‖score (A, v)‖ ∂sphere ∂μ := by
          rw [lpNorm_one_eq_integral_norm hscoreMeas]
          exact integral_prod (fun p ↦ ‖score p‖) hscoreInt.norm
        _ ≤ ∫ A, envelope A ∂μ := by
          apply integral_mono_ae hInnerInt hEnvelopeInt
          filter_upwards [hSlices] with A hA
          exact hA.2
        _ ≤ h13UltraRelaxedProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
          simpa only [envelope, μ, higherScoreMatrixLaw] using
            hEnvelope.2 hdense
    simpa only [score, μ, sphere, higherScoreMatrixLaw,
      higherScoreSphereLaw, concreteCenteredScoreProductLaw] using hbound

/-! ## Ultra-sharp lower Bell and fourth score -/

theorem concreteCenteredBellFourLowerProduct_momentPackage_ultra
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredBellFourLowerProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredBellFourLowerProduct N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          ultraSharpLowerBellFourthConstant * (N : ℝ) ^ 2) := by
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
    centeredLogScore_oneFourth_momentPackage_strong_proved_A1A2A3A4
      hN hgap
  have hTwo := centeredLogScore_twoSquare_momentPackage_ultra_A1A2A3
    hN hgap
  have hOneThree :=
    centeredLogScore_oneThree_momentPackage_relaxed_ultra_A1A2A3A4 hN hgap
  have hf1 : MemLp f1 1 law := by simpa only [f1, law] using hOne.1
  have hf2 : MemLp f2 1 law := by simpa only [f2, law] using hTwo.1
  have hf13 : MemLp f13 1 law := by
    simpa only [f13, law] using hOneThree.1
  have he1 : MemLp ((4 : ℝ) • f1) 1 law := hf1.const_smul 4
  have he2 : MemLp ((6 : ℝ) • f2) 1 law := hf2.const_smul 6
  have he13 : MemLp ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law :=
    hf13.norm.const_smul 4
  have hEnvelope : MemLp envelope 1 law := (he1.add he2).add he13
  have hLowerMeas : AEStronglyMeasurable
      (concreteCenteredBellFourLowerProduct N K) law := by
    have h1 := measurable_concreteCenteredEll_one (N := N) (K := K) hN
    have h2 := measurable_concreteCenteredEll_two (N := N) (K := K) hN
    have h3 := measurable_concreteCenteredEll_three (N := N) (K := K) hN
    exact (((((h1.pow_const 4).add
      (((h1.pow_const 2).const_mul 6).mul h2)).add
      ((h2.pow_const 2).const_mul 3)).add
      ((h1.const_mul 4).mul h3))).aestronglyMeasurable
  have hdom : ∀ p, ‖concreteCenteredBellFourLowerProduct N K p‖ ≤
      envelope p := by
    intro p
    simpa only [envelope, f1, f2, f13, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Real.norm_eq_abs] using
      concreteCenteredBellFourLowerProduct_norm_le_sharpEnvelope
        (N := N) (K := K) p
  have hLower : MemLp (concreteCenteredBellFourLowerProduct N K) 1 law := by
    apply hEnvelope.of_le hLowerMeas
    exact Eventually.of_forall fun p ↦ by
      have hp := hdom p
      have hnonneg : 0 ≤ envelope p := by
        simp only [envelope, f1, f2, f13, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]
        positivity
      simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hp
  refine ⟨by simpa only [law] using hLower, ?_⟩
  intro hdense
  have hf1Bound : lpNorm f1 1 law ≤ (2 : ℝ) ^ 28 * (N : ℝ) ^ 2 := by
    simpa only [f1, law] using hOne.2 hdense
  have hf2Bound : lpNorm f2 1 law ≤
      h14UltraProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
    simpa only [f2, law] using hTwo.2 hdense
  have hf13Bound : lpNorm f13 1 law ≤
      h13UltraRelaxedProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
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
        ultraSharpLowerBellFourthConstant * (N : ℝ) ^ 2 := by
    unfold ultraSharpLowerBellFourthConstant
    nlinarith [hf1Bound, hf2Bound, hf13Bound]
  change lpNorm (concreteCenteredBellFourLowerProduct N K) 1 law ≤ _
  exact hmono.trans (hsum.trans_eq hscaled) |>.trans hcoeff

theorem centeredLogScore_four_momentPackage_ultra
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredEll 4 N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          ultraSharpLowerBellFourthConstant * (N : ℝ) ^ 2) := by
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
      (concreteCenteredBellFourLowerProduct_momentPackage_ultra hN hgap).1
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
      ((concreteCenteredBellFourLowerProduct_momentPackage_ultra
        hN hgap).2 hdense)
    simpa only [score, lower, μ, ν, concreteCenteredScoreProductLaw] using hle

theorem concreteCenteredBellFourProduct_memLp_one_ultra
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCenteredBellFourProduct N K) 1
      (concreteCenteredScoreProductLaw N K) := by
  have hpoint : concreteCenteredBellFourProduct N K =
      concreteCenteredBellFourLowerProduct N K + concreteCenteredEll 4 N K := by
    funext p
    simp only [concreteCenteredBellFourProduct,
      concreteCenteredBellFourLowerProduct, densityBellFour, Pi.add_apply]
  rw [hpoint]
  exact
    ((concreteCenteredBellFourLowerProduct_momentPackage_ultra
      hN (by omega)).1).add
      ((centeredLogScore_four_momentPackage_ultra hN (by omega)).1)

theorem concreteCenteredBellFourProduct_lpNorm_one_le_ultra
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredBellFourProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ≤
      ultraSharpFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  have hgap : 2 * N + 8 ≤ K := by omega
  let lower := concreteCenteredBellFourLowerProduct N K
  let fourth := concreteCenteredEll 4 N K
  let law := concreteCenteredScoreProductLaw N K
  have hpoint : concreteCenteredBellFourProduct N K = lower + fourth := by
    funext p
    simp only [lower, fourth, concreteCenteredBellFourProduct,
      concreteCenteredBellFourLowerProduct, densityBellFour, Pi.add_apply]
  have hlower :=
    (concreteCenteredBellFourLowerProduct_momentPackage_ultra
      (N := N) (K := K) hN hgap).1
  have hfourth := (centeredLogScore_four_momentPackage_ultra
    (N := N) (K := K) hN hgap).1
  have hlowerBound :=
    (concreteCenteredBellFourLowerProduct_momentPackage_ultra
      (N := N) (K := K) hN hgap).2 hdense
  have hfourthBound := (centeredLogScore_four_momentPackage_ultra
    (N := N) (K := K) hN hgap).2 hdense
  rw [hpoint]
  calc
    lpNorm (lower + fourth) 1 law ≤
        lpNorm lower 1 law + lpNorm fourth 1 law :=
      lpNorm_add_le hlower (by norm_num)
    _ ≤ ultraSharpFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
      unfold ultraSharpFullFourthDensityScoreConstant
      nlinarith

theorem concreteCenteredDensityScoreFourProduct_memLp_one_ultra
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) :=
  (memLp_congr_ae
    (concreteCenteredDensityScoreFourProduct_ae_eq_Bell hN hdense)).2
      (concreteCenteredBellFourProduct_memLp_one_ultra hN hdense)

theorem concreteCenteredDensityScoreFourProduct_lpNorm_one_le_ultra
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm
        (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
          concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
        (concreteCenteredScoreProductLaw N K) ≤
      ultraSharpFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 4 N K Av.2 Av.1
  let bell := concreteCenteredBellFourProduct N K
  let law := concreteCenteredScoreProductLaw N K
  have heq : score =ᵐ[law] bell :=
    concreteCenteredDensityScoreFourProduct_ae_eq_Bell hN hdense
  have hscore : MemLp score 1 law :=
    concreteCenteredDensityScoreFourProduct_memLp_one_ultra hN hdense
  have hbell : MemLp bell 1 law :=
    concreteCenteredBellFourProduct_memLp_one_ultra hN hdense
  have hnorm : lpNorm score 1 law = lpNorm bell 1 law := by
    rw [lpNorm_one_eq_integral_norm hscore.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hbell.aestronglyMeasurable]
    exact integral_congr_ae <| heq.mono fun Av hAv ↦ congrArg norm hAv
  rw [hnorm]
  exact concreteCenteredBellFourProduct_lpNorm_one_le_ultra hN hdense

theorem abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_ultra
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    |iteratedDeriv 4
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y| ≤
      ultraSharpFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  have hraw :=
    abs_coeCorner_centeredProjective_eventPath_derivative_at_le_lpNorm_one
      hN (by omega) (by omega) event hevent y
      (concreteCenteredDensityScoreFourProduct_memLp_one_ultra hN hdense)
  exact hraw.trans
    (concreteCenteredDensityScoreFourProduct_lpNorm_one_le_ultra hN hdense)

theorem abs_iteratedDeriv_four_concreteSharedBetaOrbitalEventPath_le_ultra
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    |iteratedDeriv 4
        (concreteSharedBetaOrbitalEventPath m N
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K)
            q event) y| ≤
      ultraSharpFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
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
  exact abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_ultra
    hN hdense preevent hpre y

#print axioms centeredLogScore_oneThree_momentPackage_relaxed_ultra_A1A2A3A4
#print axioms concreteCenteredDensityScoreFourProduct_lpNorm_one_le_ultra
#print axioms abs_iteratedDeriv_four_concreteSharedBetaOrbitalEventPath_le_ultra

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
