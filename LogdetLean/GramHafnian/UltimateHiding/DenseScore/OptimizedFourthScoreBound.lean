import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_BellLowerMomentAssembly
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_COEBlockLiteralSign
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H12_ExactMomentEndpointA4
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeRelaxedProjectiveClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_StrongTwoSquareProductBound
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ProjectiveCenteredPathAt
import Mathlib.Tactic

/-!
# Optimized fourth-score bound

The historical fourth-score route relaxed every monomial to the common
budget `2^160`.  This module keeps the already proved strong constants:

* H12: `2^28` for `ellOne^4`;
* H14: `h14StrongProjectiveEnvelopeConstant` for `ellTwo^2`;
* H13: `h13RelaxedProjectiveEnvelopeStrongConstant` for
  `ellOne * ellThree`.

Young's inequality then bounds the complete lower Bell polynomial by

`4 * 2^28 + 6 * h14StrongProjectiveEnvelopeConstant +
  4 * h13RelaxedProjectiveEnvelopeStrongConstant`.

The H11 support sign and fixed-fibre density normalization give the same
bound for `ellFour`.  Consequently the full Bell polynomial, the literal
fourth density score, and both event-path fourth derivatives cost only twice
that number.  No new scientific input is introduced.
-/

open MeasureTheory Filter Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
open LogdetLean.GramHafnian.CurrentPRL

/-- Exact optimized budget for the four lower Bell monomials. -/
def optimizedLowerBellFourthConstant : ℝ :=
  4 * (2 : ℝ) ^ 28 +
    6 * h14StrongProjectiveEnvelopeConstant +
    4 * h13RelaxedProjectiveEnvelopeStrongConstant

/-- Exact optimized budget for the full fourth density score. -/
def optimizedFullFourthDensityScoreConstant : ℝ :=
  2 * optimizedLowerBellFourthConstant

/-- Decimal value of the optimized lower-Bell budget. -/
theorem optimizedLowerBellFourthConstant_eq :
    optimizedLowerBellFourthConstant = 315251975008026624 := by
  norm_num [optimizedLowerBellFourthConstant,
    h13RelaxedProjectiveEnvelopeStrongConstant,
    h14StrongProjectiveEnvelopeConstant,
    h14BetaPrimeProjectiveLowerMomentConstant,
    denseClassicalMomentConstant]

/-- Decimal value of the optimized full fourth-score budget. -/
theorem optimizedFullFourthDensityScoreConstant_eq :
    optimizedFullFourthDensityScoreConstant = 630503950016053248 := by
  rw [optimizedFullFourthDensityScoreConstant,
    optimizedLowerBellFourthConstant_eq]
  norm_num

/-- The sharp H12, H14, and relaxed-strong H13 packages assemble the lower
Bell polynomial without first inflating any monomial to `2^160`. -/
theorem concreteCenteredBellFourLowerProduct_momentPackage_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredBellFourLowerProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredBellFourLowerProduct N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          optimizedLowerBellFourthConstant * (N : ℝ) ^ 2) := by
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
  have hTwo :=
    centeredLogScore_twoSquare_momentPackage_strong_A1A2A3 hN hgap
  have hOneThree :=
    centeredLogScore_oneThree_momentPackage_relaxed_strong_proved_A1A2A3A4
      hN hgap
  have hf1 : MemLp f1 1 law := by
    simpa only [f1, law] using hOne.1
  have hf2 : MemLp f2 1 law := by
    simpa only [f2, law] using hTwo.1
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
      h14StrongProjectiveEnvelopeConstant * (N : ℝ) ^ 2 := by
    simpa only [f2, law] using hTwo.2 hdense
  have hf13Bound : lpNorm f13 1 law ≤
      h13RelaxedProjectiveEnvelopeStrongConstant * (N : ℝ) ^ 2 := by
    simpa only [f13, law] using hOneThree.2 hdense
  have hmono : lpNorm (concreteCenteredBellFourLowerProduct N K) 1 law ≤
      lpNorm envelope 1 law := lpNorm_mono_real hEnvelope hdom
  have hsum1 : lpNorm (((4 : ℝ) • f1) + (6 : ℝ) • f2) 1 law ≤
      lpNorm ((4 : ℝ) • f1) 1 law + lpNorm ((6 : ℝ) • f2) 1 law :=
    lpNorm_add_le he1 (by norm_num)
  have hsum2 : lpNorm envelope 1 law ≤
      lpNorm (((4 : ℝ) • f1) + (6 : ℝ) • f2) 1 law +
        lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := by
    exact lpNorm_add_le (he1.add he2) (by norm_num)
  have hsum : lpNorm envelope 1 law ≤
      lpNorm ((4 : ℝ) • f1) 1 law + lpNorm ((6 : ℝ) • f2) 1 law +
        lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := by
    calc
      lpNorm envelope 1 law ≤
          lpNorm (((4 : ℝ) • f1) + (6 : ℝ) • f2) 1 law +
            lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := hsum2
      _ ≤ (lpNorm ((4 : ℝ) • f1) 1 law +
            lpNorm ((6 : ℝ) • f2) 1 law) +
            lpNorm ((4 : ℝ) • (fun p ↦ ‖f13 p‖)) 1 law := by
        gcongr
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
        optimizedLowerBellFourthConstant * (N : ℝ) ^ 2 := by
    unfold optimizedLowerBellFourthConstant
    nlinarith [hf1Bound, hf2Bound, hf13Bound]
  change lpNorm (concreteCenteredBellFourLowerProduct N K) 1 law ≤ _
  exact hmono.trans (hsum.trans_eq hscaled) |>.trans hcoeff

theorem concreteCenteredBellFourLowerProduct_memLp_one_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCenteredBellFourLowerProduct N K) 1
      (concreteCenteredScoreProductLaw N K) :=
  (concreteCenteredBellFourLowerProduct_momentPackage_optimized
    hN (by omega)).1

theorem concreteCenteredBellFourLowerProduct_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredBellFourLowerProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ≤
      optimizedLowerBellFourthConstant * (N : ℝ) ^ 2 :=
  (concreteCenteredBellFourLowerProduct_momentPackage_optimized
    hN (by omega)).2 hdense

/-- The fixed-fibre normalization and H11 nonpositive-support argument
transfer the optimized lower-Bell budget verbatim to `ellFour`. -/
theorem centeredLogScore_four_momentPackage_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredEll 4 N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          optimizedLowerBellFourthConstant * (N : ℝ) ^ 2) := by
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
      (concreteCenteredBellFourLowerProduct_momentPackage_optimized
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
    have hlowerBound :=
      (concreteCenteredBellFourLowerProduct_momentPackage_optimized
        hN hgap).2 hdense
    have hle := H.2.trans hlowerBound
    simpa only [score, lower, μ, ν, concreteCenteredScoreProductLaw] using hle

theorem centeredLogScore_four_memLp_one_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCenteredEll 4 N K) 1
      (concreteCenteredScoreProductLaw N K) :=
  (centeredLogScore_four_momentPackage_optimized hN (by omega)).1

theorem centeredLogScore_four_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ≤
      optimizedLowerBellFourthConstant * (N : ℝ) ^ 2 :=
  (centeredLogScore_four_momentPackage_optimized hN (by omega)).2 hdense

/-- The full Bell polynomial is the lower polynomial plus `ellFour`, so its
optimized budget is exactly twice the lower-Bell budget. -/
theorem concreteCenteredBellFourProduct_memLp_one_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp (concreteCenteredBellFourProduct N K) 1
      (concreteCenteredScoreProductLaw N K) := by
  have hpoint : concreteCenteredBellFourProduct N K =
      concreteCenteredBellFourLowerProduct N K +
        concreteCenteredEll 4 N K := by
    funext p
    simp only [concreteCenteredBellFourProduct,
      concreteCenteredBellFourLowerProduct, densityBellFour,
      Pi.add_apply]
  rw [hpoint]
  exact (concreteCenteredBellFourLowerProduct_memLp_one_optimized hN hdense).add
    (centeredLogScore_four_memLp_one_optimized hN hdense)

theorem concreteCenteredBellFourProduct_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (concreteCenteredBellFourProduct N K) 1
        (concreteCenteredScoreProductLaw N K) ≤
      optimizedFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  let lower := concreteCenteredBellFourLowerProduct N K
  let fourth := concreteCenteredEll 4 N K
  let law := concreteCenteredScoreProductLaw N K
  have hpoint : concreteCenteredBellFourProduct N K = lower + fourth := by
    funext p
    simp only [lower, fourth, concreteCenteredBellFourProduct,
      concreteCenteredBellFourLowerProduct, densityBellFour,
      Pi.add_apply]
  have hlower :=
    concreteCenteredBellFourLowerProduct_memLp_one_optimized hN hdense
  have hfourth := centeredLogScore_four_memLp_one_optimized hN hdense
  have hlowerBound :=
    concreteCenteredBellFourLowerProduct_lpNorm_one_le_optimized hN hdense
  have hfourthBound := centeredLogScore_four_lpNorm_one_le_optimized hN hdense
  rw [hpoint]
  calc
    lpNorm (lower + fourth) 1 law ≤
        lpNorm lower 1 law + lpNorm fourth 1 law :=
      lpNorm_add_le hlower (by norm_num)
    _ ≤ optimizedFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
      unfold optimizedFullFourthDensityScoreConstant
      nlinarith

/-- Optimized product-`L¹` closure for the literal fourth density score. -/
theorem concreteCenteredDensityScoreFourProduct_memLp_one_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) := by
  exact (memLp_congr_ae
    (concreteCenteredDensityScoreFourProduct_ae_eq_Bell hN hdense)).2
      (concreteCenteredBellFourProduct_memLp_one_optimized hN hdense)

/-- Optimized `L¹` bound for the literal fourth density score. -/
theorem concreteCenteredDensityScoreFourProduct_lpNorm_one_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm
        (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
          concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
        (concreteCenteredScoreProductLaw N K) ≤
      optimizedFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 4 N K Av.2 Av.1
  let bell := concreteCenteredBellFourProduct N K
  let law := concreteCenteredScoreProductLaw N K
  have heq : score =ᵐ[law] bell :=
    concreteCenteredDensityScoreFourProduct_ae_eq_Bell hN hdense
  have hscore : MemLp score 1 law :=
    concreteCenteredDensityScoreFourProduct_memLp_one_optimized hN hdense
  have hbell : MemLp bell 1 law :=
    concreteCenteredBellFourProduct_memLp_one_optimized hN hdense
  have hnorm : lpNorm score 1 law = lpNorm bell 1 law := by
    rw [lpNorm_one_eq_integral_norm hscore.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hbell.aestronglyMeasurable]
    exact integral_congr_ae <| heq.mono fun Av hAv ↦ congrArg norm hAv
  rw [hnorm]
  exact concreteCenteredBellFourProduct_lpNorm_one_le_optimized hN hdense

/-- Optimized uniform fourth derivative bound for the projectively averaged
centered COE event path. -/
theorem abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    |iteratedDeriv 4
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y| ≤
      optimizedFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
  have hraw :=
    abs_coeCorner_centeredProjective_eventPath_derivative_at_le_lpNorm_one
      hN (by omega) (by omega) event hevent y
      (concreteCenteredDensityScoreFourProduct_memLp_one_optimized hN hdense)
  exact hraw.trans
    (concreteCenteredDensityScoreFourProduct_lpNorm_one_le_optimized
      hN hdense)

/-- Optimized uniform fourth derivative bound for the same-beta orbital
event path. -/
theorem abs_iteratedDeriv_four_concreteSharedBetaOrbitalEventPath_le_optimized
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    |iteratedDeriv 4
        (concreteSharedBetaOrbitalEventPath m N
            (concreteScaledCOECornerLaw
              canonicalUnitaryHaarProbabilityFamily N K)
            q event) y| ≤
      optimizedFullFourthDensityScoreConstant * (N : ℝ) ^ 2 := by
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
    abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_optimized
      hN hdense preevent hpre y

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
