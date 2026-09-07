import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLikelihoodBellCalculus
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# H16 fixed-direction event derivatives: conditional reduction

This module does **not** use
`coeCorner_centeredFixedDirection_eventPath_derivative_external_derived`, nor
the analogous uncentered event-derivative axiom.  It proves the exact H16
endpoint from an explicit exact-H5 parameter and the event-independent
ambient `W^{4,1}`/`L1` transport contract which remains to be formalized.

The generic functional-analytic part is complete: restriction to an event
followed by Bochner integration is a continuous linear functional on `L1`,
and therefore commutes with every iterated derivative through order four.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal ContDiff Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-! ## Exact upstream H5 contract -/

/-- The universally closed, exact H5 determinant-density theorem.  It has no
event, direction, derivative, score, or H16 conclusion in its type. -/
abbrev H16ExactH5Family : Prop :=
  ∀ {n k : ℕ}, 1 ≤ n → 2 * n ≤ k →
    concreteUnscaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily n k =
      coeCornerDeterminantDensityProbabilityMeasure n k

/-- Exact H5, supplied as a theorem parameter rather than the project's H5
axiom, implies the almost-sure open-support statement for the scaled law. -/
theorem h16_scaledCOECorner_ae_support_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    ∀ᵐ A ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K),
      (unscaleCOECorner K A).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K A) := by
  have hunscaled :
      ∀ᵐ C ∂(concreteUnscaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K),
        C.IsSymm ∧ coeCornerSupport C := by
    have heq := hH5 (n := N) (k := K) hN h2NK
    exact heq.symm ▸
      coeCornerDeterminantDensityProbabilityMeasure_ae_support N K
  exact ae_of_ae_map (measurable_unscaleCOECorner N K).aemeasurable hunscaled

/-- Conditional on exact H5, the literal centered likelihood has pointwise
derivatives through order four at the origin on an almost-everywhere set.
This is the correct pointwise statement: boundary points themselves need not
be pointwise `C^4`. -/
theorem h16_centeredLikelihoodCore_contDiffAt_four_ae_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    (v : ComplexUnitSphere N) :
    ∀ᵐ A ∂(concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K),
      ContDiffAt ℝ 4 (fun t ↦ concreteCenteredLikelihoodCore K v t A) 0 := by
  filter_upwards [h16_scaledCOECorner_ae_support_of_exactH5 hH5 hN h2NK]
    with A hA
  exact concreteCenteredLikelihoodCore_contDiffAt_four hN v A hA.2

/-- At every point of the open COE support, every requested order `r ≤ 4`
exists pointwise.  The score in H16 is definitionally that iterated
derivative.  Boundary points are deliberately excluded. -/
theorem h16_centeredDensityScore_pointwise_of_support
    {N K r : ℕ} (hN : 1 ≤ N) (hr : r ≤ 4)
    (v : ComplexUnitSphere N) (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    ContDiffAt ℝ r (fun t ↦ concreteCenteredLikelihoodCore K v t A) 0 ∧
      concreteCenteredDensityScore r N K v A =
        iteratedDeriv r (fun t ↦ concreteCenteredLikelihoodCore K v t A) 0 := by
  constructor
  · exact (concreteCenteredLikelihoodCore_contDiffAt_four hN v A hsupport).of_le
      (by exact_mod_cast hr)
  · rfl

/-! ## Kernel-proved `L1` differentiation layer -/

/-- A continuous linear map commutes with iterated derivatives of a `C^4`
Banach-valued curve. -/
theorem h16_iteratedDeriv_clm_comp_of_contDiff_four
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {f : ℝ → E} {r : ℕ}
    (hf : ContDiff ℝ 4 f) (hr : r ≤ 4) (x : ℝ) :
    iteratedDeriv r (fun t ↦ L (f t)) x = L (iteratedDeriv r f x) := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv ℝ r (L ∘ f) x) (fun _ ↦ 1) =
    L ((iteratedFDeriv ℝ r f x) (fun _ ↦ 1))
  rw [L.iteratedFDeriv_comp_left hf.contDiffAt (mod_cast hr)]
  rfl

/-- Restrict an `L1` function to a set and then Bochner-integrate it. -/
noncomputable def h16SetIntegralL1CLM
    {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (s : Set X) : (X →₁[μ] E) →L[ℝ] E := by
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  exact (L1.integralCLM (α := X) (E := E) (μ := μ.restrict s)).comp
    (LpToLpRestrictCLM X E ℝ μ 1 s)

/-- The preceding continuous linear map is exactly the ordinary set
integral. -/
theorem h16SetIntegralL1CLM_apply
    {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (s : Set X) (f : X →₁[μ] E) :
    h16SetIntegralL1CLM μ s f = ∫ x in s, f x ∂μ := by
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  rw [h16SetIntegralL1CLM, ContinuousLinearMap.comp_apply]
  rw [← L1.integral_eq]
  rw [L1.integral_eq_integral]
  exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s f)

/-- Differentiation under an arbitrary set integral once the integrand is a
`C^4` curve in ambient `L1`. -/
theorem h16_iteratedDeriv_setIntegral_of_contDiff_L1
    {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure X) (s : Set X) {f : ℝ → (X →₁[μ] E)} {r : ℕ}
    (hf : ContDiff ℝ 4 f) (hr : r ≤ 4) (x : ℝ) :
    iteratedDeriv r (fun t ↦ ∫ y in s, f t y ∂μ) x =
      ∫ y in s, iteratedDeriv r f x y ∂μ := by
  have hfun : (fun t ↦ ∫ y in s, f t y ∂μ) =
      fun t ↦ h16SetIntegralL1CLM μ s (f t) := by
    funext t
    exact (h16SetIntegralL1CLM_apply μ s (f t)).symm
  rw [hfun]
  rw [h16_iteratedDeriv_clm_comp_of_contDiff_four
    (h16SetIntegralL1CLM μ s) hf hr x]
  exact h16SetIntegralL1CLM_apply μ s (iteratedDeriv r f x)

/-! ## The irreducible event-independent analytic transport contract -/

/-- `CONDITIONAL`: the narrow global analytic contract still missing from
the project.  It asserts one ambient density curve, independent of the event,
which is `C^4` in `L1`; its origin jets agree almost everywhere with the
literal determinant scores.  This is strictly stronger and structurally
different from the eventwise H16 conclusion.

Mathematically this follows from exact H5 plus: zero extension of the COE
determinant weight in `W^{4,1}`, the complex-symmetric congruence Jacobian,
and smooth linear transport in `L1`.  Its measure identity is event-free;
in particular, no event derivative or event integral is assumed here. -/
structure H16FixedDirectionW41Transport
    (_hH5 : H16ExactH5Family) {N K : ℕ}
    (_hN : 1 ≤ N) (_hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) where
  ambient : Measure (ConcreteMatrixState N)
  weight : ConcreteMatrixState N → ℝ≥0
  weight_measurable : Measurable weight
  scaledLaw_eq_withDensity :
    concreteScaledCOECornerLaw canonicalUnitaryHaarProbabilityFamily N K =
      ambient.withDensity (fun A ↦ (weight A : ℝ≥0∞))
  densityPath : ℝ → (ConcreteMatrixState N →₁[ambient] ℝ)
  densityPath_nonnegative :
    ∀ t : ℝ, ∀ᵐ A ∂ambient, 0 ≤ densityPath t A
  pushforward_eq_withDensity :
    ∀ t : ℝ,
      Measure.map
          (transposeCongruenceFlow (concreteCenteredOrbitalDirection N v) t)
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        ambient.withDensity
          (fun A ↦ ENNReal.ofReal (densityPath t A))
  densityPath_contDiff_four : ContDiff ℝ 4 densityPath
  jet_ae :
    ∀ (r : ℕ), r ≤ 4 →
      (fun A ↦ iteratedDeriv r densityPath 0 A) =ᵐ[ambient]
        fun A ↦ (weight A : ℝ) * concreteCenteredDensityScore r N K v A

namespace H16FixedDirectionW41Transport

/-- The event-probability path is the set integral of the single ambient
`L1` density curve.  This is derived from the event-free measure identity in
the transport contract. -/
theorem eventPath_eq_setIntegral
    {N K : ℕ} {hH5 : H16ExactH5Family}
    {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    {v : ComplexUnitSphere N}
    (T : H16FixedDirectionW41Transport hH5 hN hboundary v)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (t : ℝ) :
    concreteCenteredRankOneCOEEventPath K v event t =
      ∫ A in event, T.densityPath t A ∂T.ambient := by
  unfold concreteCenteredRankOneCOEEventPath
  rw [T.pushforward_eq_withDensity t]
  rw [← setIntegral_one_eq_measureReal]
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    ((Lp.aestronglyMeasurable (T.densityPath t)).aemeasurable.ennreal_ofReal.restrict)
    (by simp) (fun _ ↦ (1 : ℝ)) hevent]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (T.densityPath_nonnegative t)] with A hA
  simp only [ENNReal.toReal_ofReal hA, smul_eq_mul, mul_one]

/-- The transport contract yields the requested a.e. measurability of every
literal score through order four under the actual scaled COE law. -/
theorem score_aestronglyMeasurable
    {N K r : ℕ} {hH5 : H16ExactH5Family}
    {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    {v : ComplexUnitSphere N}
    (T : H16FixedDirectionW41Transport hH5 hN hboundary v)
    (hr : r ≤ 4) :
    AEStronglyMeasurable (concreteCenteredDensityScore r N K v)
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  rw [T.scaledLaw_eq_withDensity]
  apply (aestronglyMeasurable_withDensity_iff T.weight_measurable).2
  have hjet : AEStronglyMeasurable
      (fun A ↦ iteratedDeriv r T.densityPath 0 A) T.ambient :=
    Lp.aestronglyMeasurable _
  exact hjet.congr (T.jet_ae r hr)

/-- Every literal score through order four is integrable under the actual
scaled COE law. -/
theorem score_integrable
    {N K r : ℕ} {hH5 : H16ExactH5Family}
    {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    {v : ComplexUnitSphere N}
    (T : H16FixedDirectionW41Transport hH5 hN hboundary v)
    (hr : r ≤ 4) :
    Integrable (concreteCenteredDensityScore r N K v)
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K) := by
  rw [T.scaledLaw_eq_withDensity]
  rw [integrable_withDensity_iff_integrable_coe_smul₀
    T.weight_measurable.aemeasurable]
  have hjet : Integrable
      (fun A ↦ iteratedDeriv r T.densityPath 0 A) T.ambient :=
    memLp_one_iff_integrable.1 (Lp.memLp _)
  exact hjet.congr (T.jet_ae r hr)

/-- On every compact time interval, every density jet through order four has
a common finite `L1`-norm bound.  This is the correct locally uniform `L1`
control; a common pointwise envelope for fourth derivatives is false at the
sharp threshold. -/
theorem exists_uniform_L1_bound_on_uIcc
    {N K r : ℕ} {hH5 : H16ExactH5Family}
    {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    {v : ComplexUnitSphere N}
    (T : H16FixedDirectionW41Transport hH5 hN hboundary v)
    (hr : r ≤ 4) (a b : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Set.uIcc a b,
      ‖iteratedDeriv r T.densityPath t‖ ≤ C := by
  have hcont : Continuous (iteratedDeriv r T.densityPath) :=
    T.densityPath_contDiff_four.continuous_iteratedDeriv r (mod_cast hr)
  rcases isCompact_uIcc.bddAbove_image hcont.norm.continuousOn with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro t ht
  exact hC (Set.mem_image_of_mem _ ht)

end H16FixedDirectionW41Transport

/-! ## Exact H16 endpoint under the narrow transport contract -/

/-- `CONDITIONAL / REDUCED`: exact H16, with every original quantifier and
the original conclusion unchanged, derived without H16 or any equivalent
external declaration.  The two additional parameters are exact H5 and the
event-independent `W^{4,1}` transport contract above. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_H16_conditional
    (hH5 : H16ExactH5Family)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (T : H16FixedDirectionW41Transport hH5 hN hboundary v)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
  have hpath : concreteCenteredRankOneCOEEventPath K v event =
      fun t ↦ ∫ A in event, T.densityPath t A ∂T.ambient := by
    funext t
    exact T.eventPath_eq_setIntegral event hevent t
  rw [hpath]
  calc
    iteratedDeriv r (fun t ↦ ∫ A in event, T.densityPath t A ∂T.ambient) 0 =
        ∫ A in event, iteratedDeriv r T.densityPath 0 A ∂T.ambient :=
      h16_iteratedDeriv_setIntegral_of_contDiff_L1
        T.ambient event T.densityPath_contDiff_four hr 0
    _ = ∫ A in event,
        (T.weight A : ℝ) * concreteCenteredDensityScore r N K v A
        ∂T.ambient := by
      exact integral_congr_ae (ae_restrict_of_ae (T.jet_ae r hr))
    _ = ∫ A in event, concreteCenteredDensityScore r N K v A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) := by
      rw [T.scaledLaw_eq_withDensity]
      simpa only [NNReal.smul_def, smul_eq_mul] using
        (setIntegral_withDensity_eq_setIntegral_smul T.weight_measurable
          (concreteCenteredDensityScore r N K v) hevent).symm
    _ = ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) :=
      (integral_indicator hevent).symm

namespace Conditional

/-- `CONDITIONAL / REDUCED`: the exact original H16 declaration, under the
explicit exact-H5 and event-free `W^{4,1}` transport parameters.  The original
quantifiers and conclusion are unchanged. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_external_derived
    (hH5 : H16ExactH5Family)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (T : H16FixedDirectionW41Transport hH5 hN hboundary v)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) :=
  coeCorner_centeredFixedDirection_eventPath_derivative_H16_conditional
    hH5 hN hboundary hr v T event hevent

end Conditional

/-! ## Why a pointwise time-uniform fourth-derivative envelope is impossible -/

/-- The normal fourth-derivative boundary kernel at exponent `7/2` is
unbounded as the inward distance tends to zero. -/
theorem h16_fourthBoundaryKernel_tendsto_atTop :
    Tendsto (fun s : ℝ ↦ s ^ (-(1 / 2 : ℝ))) (𝓝[>] 0) atTop := by
  exact tendsto_rpow_neg_nhdsGT_zero (by norm_num)

/-- Consequently, no finite pointwise bound can dominate that kernel on a
punctured right neighborhood of the moving boundary. -/
theorem h16_fourthBoundaryKernel_not_eventually_bounded (M : ℝ) :
    ¬ ∀ᶠ s in 𝓝[>] 0, s ^ (-(1 / 2 : ℝ)) ≤ M := by
  intro hle
  have hgt : ∀ᶠ s in 𝓝[>] 0, M < s ^ (-(1 / 2 : ℝ)) :=
    h16_fourthBoundaryKernel_tendsto_atTop (eventually_gt_atTop M)
  obtain ⟨s, hsle, hsgt⟩ := (hle.and hgt).exists
  exact (not_lt_of_ge hsle) hsgt

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
