import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFixedDirectionPathShift
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreFubini
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# CONDITIONAL H18: projective differentiation interchange

This module does not import either projective external declaration.  It starts
from the exact H16 fixed-direction statement as an explicit theorem parameter.
The two remaining analytic inputs are stated separately: fixed-direction
`C^4` regularity and product-`L^1` integrability of the positive-order literal
scores.  Neither input mentions a projective average.
-/

open TopologicalSpace MeasureTheory Set Filter
open scoped Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- CONDITIONAL input, copied quantifier-for-quantifier from the original H16
fixed-direction declaration. -/
def CoeCornerCenteredFixedDirectionH16Contract : Prop :=
  ∀ {N K r : ℕ}, (1 ≤ N) → (2 * N + 8 ≤ K) → (r ≤ 4) →
    (v : ComplexUnitSphere N) →
    (event : Set (ConcreteMatrixState N)) → MeasurableSet event →
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) 0 =
      ∫ A, event.indicator
        (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K)

/-- Smallest regularity input not carried by the totalized derivatives in
H16: every fixed-direction path is genuinely `C^4`.  This contract mentions
no projective average. -/
def CoeCornerCenteredFixedDirectionC4Contract : Prop :=
  ∀ {N K : ℕ}, (1 ≤ N) → (2 * N + 8 ≤ K) →
    (v : ComplexUnitSphere N) →
    (event : Set (ConcreteMatrixState N)) → MeasurableSet event →
    ContDiff ℝ 4 (concreteCenteredRankOneCOEEventPath K v event)

/-- CONDITIONAL positive-order product-`L^1` input.  Order zero is proved
internally and is deliberately absent from this contract. -/
def CoeCornerCenteredPositiveScoreL1ThroughFourContract : Prop :=
  ∀ {N K r : ℕ}, (1 ≤ N) → (2 * N + 8 ≤ K) →
    (1 ≤ r) → (r ≤ 4) →
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore r N K Av.2 Av.1) 1
      ((concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K).prod (complexUnitSphereProbabilityMeasure N))

/-- The direction-wise absolute score integral.  It is independent of time
and therefore serves as a global, rather than merely local, majorant. -/
def concreteCenteredDensityScoreDirectionMajorant
    (r N K : ℕ) (v : ComplexUnitSphere N) : ℝ :=
  ∫ A, |concreteCenteredDensityScore r N K v A|
    ∂(concreteScaledCOECornerLaw
      LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
        N K)

/-- Product `L^1` for all orders through four, combining the internal order
zero theorem with the explicit positive-order contract. -/
theorem concreteCenteredDensityScoreProduct_memLp_one_conditional
    (hscore : CoeCornerCenteredPositiveScoreL1ThroughFourContract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore r N K Av.2 Av.1) 1
      ((concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K).prod (complexUnitSphereProbabilityMeasure N)) := by
  rcases r with _ | r
  · simpa only using
      concreteCenteredDensityScoreZeroProduct_memLp_one hN (by omega : N ≤ K)
  · exact hscore hN hboundary (Nat.succ_le_succ (Nat.zero_le r)) hr

/-- The majorant is integrable over the projective sphere. -/
theorem integrable_concreteCenteredDensityScoreDirectionMajorant_conditional
    (hscore : CoeCornerCenteredPositiveScoreL1ThroughFourContract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) :
    Integrable (concreteCenteredDensityScoreDirectionMajorant r N K)
      (complexUnitSphereProbabilityMeasure N) := by
  let mu := concreteScaledCOECornerLaw
    LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore r N K Av.2 Av.1
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega : N ≤ K)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hscoreInt : Integrable score (mu.prod sphere) := by
    exact memLp_one_iff_integrable.mp
      (concreteCenteredDensityScoreProduct_memLp_one_conditional
        hscore hN hboundary hr)
  change Integrable
    (fun v : ComplexUnitSphere N ↦
      ∫ A, |concreteCenteredDensityScore r N K v A| ∂mu) sphere
  simpa only [score, Real.norm_eq_abs] using
    hscoreInt.integral_norm_prod_right

/-- Almost every fixed direction has an integrable score section. -/
theorem ae_integrable_concreteCenteredDensityScore_section_conditional
    (hscore : CoeCornerCenteredPositiveScoreL1ThroughFourContract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) :
    ∀ᵐ v ∂(complexUnitSphereProbabilityMeasure N),
      Integrable (concreteCenteredDensityScore r N K v)
        (concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K) := by
  let mu := concreteScaledCOECornerLaw
    LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore r N K Av.2 Av.1
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega : N ≤ K)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hscoreInt : Integrable score (mu.prod sphere) := by
    exact memLp_one_iff_integrable.mp
      (concreteCenteredDensityScoreProduct_memLp_one_conditional
        hscore hN hboundary hr)
  simpa only [mu, sphere, score] using hscoreInt.prod_left_ae

/-- Product-space event obtained by shifting in the direction stored in the
second coordinate.  This duplicates no original declaration and avoids
importing either projective external module. -/
def concreteCenteredConditionalShiftedProjectiveEvent
    (N : ℕ) (y : ℝ) (event : Set (ConcreteMatrixState N)) :
    Set (ConcreteMatrixState N × ComplexUnitSphere N) :=
  (fun Av ↦ concreteOrbitalMatrixUpdate N y Av.2 Av.1) ⁻¹' event

theorem measurableSet_concreteCenteredConditionalShiftedProjectiveEvent
    {N : ℕ} (y : ℝ) {event : Set (ConcreteMatrixState N)}
    (hevent : MeasurableSet event) :
    MeasurableSet
      (concreteCenteredConditionalShiftedProjectiveEvent N y event) := by
  exact (measurable_concreteOrbitalMatrixUpdate N y) hevent

/-- Exact all-time fixed-direction score representation.  This is H16 plus
the already kernel-checked additive-flow shift, with no projective input. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_at_conditional
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) y =
      ∫ A, (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) y ⁻¹' event).indicator
            (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K) := by
  rw [iteratedDeriv_concreteCenteredRankOneCOEEventPath_eq_zero_shift
    r K v event hevent y]
  apply hH16 hN hboundary hr v
  unfold transposeCongruenceFlow
  exact (measurable_transposeCongruence _) hevent

/-- H16 and product `L^1` produce a majorant uniform in all time and valid
for almost every direction. -/
theorem ae_norm_iteratedDeriv_concreteCenteredRankOneCOEEventPath_le_majorant
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hscore : CoeCornerCenteredPositiveScoreL1ThroughFourContract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    ∀ᵐ v ∂(complexUnitSphereProbabilityMeasure N), ∀ y : ℝ,
      ‖iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y‖ ≤
        concreteCenteredDensityScoreDirectionMajorant r N K v := by
  filter_upwards
    [ae_integrable_concreteCenteredDensityScore_section_conditional
      hscore hN hboundary hr] with v hv
  intro y
  rw [coeCorner_centeredFixedDirection_eventPath_derivative_at_conditional
    hH16 hN hboundary hr v event hevent y]
  have hbound :
      ‖∫ A, (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) y ⁻¹' event).indicator
            (concreteCenteredDensityScore r N K v) A
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K)‖ ≤
        ∫ A, ‖concreteCenteredDensityScore r N K v A‖
          ∂(concreteScaledCOECornerLaw
            LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
              N K) := by
    exact norm_integral_le_of_norm_le hv.norm
      (ae_of_all _ fun A ↦
        norm_indicator_le_norm_self
          (f := concreteCenteredDensityScore r N K v) (a := A))
  simpa only [concreteCenteredDensityScoreDirectionMajorant,
    Real.norm_eq_abs] using hbound

/-- Every fixed-order derivative family is integrable over the sphere at every
time.  Measurability is obtained from the measurable shifted product event,
not assumed as an extra contract. -/
theorem integrable_iteratedDeriv_concreteCenteredRankOneCOEEventPath_sphere
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hscore : CoeCornerCenteredPositiveScoreL1ThroughFourContract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    Integrable
      (fun v : ComplexUnitSphere N ↦
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y)
      (complexUnitSphereProbabilityMeasure N) := by
  let mu := concreteScaledCOECornerLaw
    LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore r N K Av.2 Av.1
  let shifted := concreteCenteredConditionalShiftedProjectiveEvent N y event
  let selected : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    shifted.indicator score
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega : N ≤ K)
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hscoreInt : Integrable score (mu.prod sphere) := by
    exact memLp_one_iff_integrable.mp
      (concreteCenteredDensityScoreProduct_memLp_one_conditional
        hscore hN hboundary hr)
  have hshifted : MeasurableSet shifted := by
    exact measurableSet_concreteCenteredConditionalShiftedProjectiveEvent
      y hevent
  have hselectedInt : Integrable selected (mu.prod sphere) := by
    exact hscoreInt.indicator hshifted
  have hfun :
      (fun v : ComplexUnitSphere N ↦
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y) =
        (fun v ↦ ∫ A, selected (A, v) ∂mu) := by
    funext v
    rw [coeCorner_centeredFixedDirection_eventPath_derivative_at_conditional
      hH16 hN hboundary hr v event hevent y]
    apply integral_congr_ae
    filter_upwards [] with A
    have hflow :=
      transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate
        hN y v A
    by_cases hmem : concreteOrbitalMatrixUpdate N y v A ∈ event
    · have hmemFlow :
          transposeCongruenceFlow
              (concreteCenteredOrbitalDirection N v) y A ∈ event := by
        simpa only [hflow] using hmem
      simp [selected, shifted,
        concreteCenteredConditionalShiftedProjectiveEvent, score,
        hmem, hmemFlow]
    · have hmemFlow :
          transposeCongruenceFlow
              (concreteCenteredOrbitalDirection N v) y A ∉ event := by
        simpa only [hflow] using hmem
      simp [selected, shifted,
        concreteCenteredConditionalShiftedProjectiveEvent, score,
        hmem, hmemFlow]
  rw [hfun]
  exact hselectedInt.integral_prod_right

/-- Dominated differentiation of the sphere integral at one successive order.
The global majorant is stronger than the local bound required by Mathlib. -/
theorem hasDerivAt_integral_iteratedDeriv_concreteCenteredRankOneCOEEventPath
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hfixedC4 : CoeCornerCenteredFixedDirectionC4Contract)
    (hscore : CoeCornerCenteredPositiveScoreL1ThroughFourContract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r < 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    HasDerivAt
      (fun x : ℝ ↦ ∫ v : ComplexUnitSphere N,
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) x
          ∂(complexUnitSphereProbabilityMeasure N))
      (∫ v : ComplexUnitSphere N,
        iteratedDeriv (r + 1)
          (concreteCenteredRankOneCOEEventPath K v event) y
          ∂(complexUnitSphereProbabilityMeasure N)) y := by
  let sphere := complexUnitSphereProbabilityMeasure N
  let F : ℝ → ComplexUnitSphere N → ℝ := fun x v ↦
    iteratedDeriv r
      (concreteCenteredRankOneCOEEventPath K v event) x
  let F' : ℝ → ComplexUnitSphere N → ℝ := fun x v ↦
    iteratedDeriv (r + 1)
      (concreteCenteredRankOneCOEEventPath K v event) x
  let bound : ComplexUnitSphere N → ℝ :=
    concreteCenteredDensityScoreDirectionMajorant (r + 1) N K
  have hrsucc : r + 1 ≤ 4 := by omega
  have hF_meas : ∀ᶠ x in 𝓝 y, AEStronglyMeasurable (F x) sphere := by
    filter_upwards [] with x
    exact (integrable_iteratedDeriv_concreteCenteredRankOneCOEEventPath_sphere
      hH16 hscore hN hboundary (by omega : r ≤ 4) event hevent x).1
  have hF_int : Integrable (F y) sphere := by
    exact integrable_iteratedDeriv_concreteCenteredRankOneCOEEventPath_sphere
      hH16 hscore hN hboundary (by omega : r ≤ 4) event hevent y
  have hF'_meas : AEStronglyMeasurable (F' y) sphere := by
    exact (integrable_iteratedDeriv_concreteCenteredRankOneCOEEventPath_sphere
      hH16 hscore hN hboundary hrsucc event hevent y).1
  have hbound : ∀ᵐ v ∂sphere, ∀ x ∈ (Set.univ : Set ℝ),
      ‖F' x v‖ ≤ bound v := by
    filter_upwards
      [ae_norm_iteratedDeriv_concreteCenteredRankOneCOEEventPath_le_majorant
        hH16 hscore hN hboundary hrsucc event hevent] with v hv
    intro x hx
    exact hv x
  have hboundInt : Integrable bound sphere := by
    exact integrable_concreteCenteredDensityScoreDirectionMajorant_conditional
      hscore hN hboundary hrsucc
  have hdiff : ∀ᵐ v ∂sphere, ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivAt (F · v) (F' x v) x := by
    filter_upwards [] with v
    intro x hx
    have hd : DifferentiableAt ℝ
        (iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event)) x :=
      ((hfixedC4 hN hboundary v event hevent).differentiable_iteratedDeriv
        r (by exact_mod_cast hr)) x
    have hsucc :
        deriv (iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event)) x =
          iteratedDeriv (r + 1)
            (concreteCenteredRankOneCOEEventPath K v event) x := by
      exact (congrFun (iteratedDeriv_succ
        (n := r)
        (f := concreteCenteredRankOneCOEEventPath K v event)) x).symm
    simpa only [F, F', hsucc] using hd.hasDerivAt
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := bound) (s := Set.univ) (x₀ := y)
    (by simp) hF_meas hF_int hF'_meas hbound hboundInt hdiff).2

/-- CONDITIONAL H18 for every order through four.  The conclusion is the
original declaration verbatim; only the three explicit upstream contracts
are added as theorem parameters. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_at_conditional
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hfixedC4 : CoeCornerCenteredFixedDirectionC4Contract)
    (hscore : CoeCornerCenteredPositiveScoreL1ThroughFourContract) :
    ∀ {N K r : ℕ}, (1 ≤ N) → (2 * N + 8 ≤ K) → (r ≤ 4) →
      (event : Set (ConcreteMatrixState N)) → MeasurableSet event →
      (y : ℝ) →
      iteratedDeriv r
          (concreteProjectiveAveragedCenteredCOEEventPath N K event) y =
        ∫ v : ComplexUnitSphere N,
          iteratedDeriv r
            (concreteCenteredRankOneCOEEventPath K v event) y
            ∂(complexUnitSphereProbabilityMeasure N) := by
  intro N K r hN hboundary hr event hevent y
  have hind : ∀ q : ℕ, q ≤ 4 → ∀ z : ℝ,
      iteratedDeriv q
          (concreteProjectiveAveragedCenteredCOEEventPath N K event) z =
        ∫ v : ComplexUnitSphere N,
          iteratedDeriv q
            (concreteCenteredRankOneCOEEventPath K v event) z
            ∂(complexUnitSphereProbabilityMeasure N) := by
    intro q
    induction q with
    | zero =>
        intro hq z
        simp only [iteratedDeriv_zero,
          concreteProjectiveAveragedCenteredCOEEventPath]
    | succ q ih =>
        intro hq z
        have hq_lt : q < 4 := by omega
        have hq_le : q ≤ 4 := by omega
        have hfun :
            iteratedDeriv q
                (concreteProjectiveAveragedCenteredCOEEventPath N K event) =
              fun x : ℝ ↦ ∫ v : ComplexUnitSphere N,
                iteratedDeriv q
                    (concreteCenteredRankOneCOEEventPath K v event) x
                  ∂(complexUnitSphereProbabilityMeasure N) := by
          funext x
          exact ih hq_le x
        rw [iteratedDeriv_succ
          (n := q)
          (f := concreteProjectiveAveragedCenteredCOEEventPath N K event), hfun]
        exact
          (hasDerivAt_integral_iteratedDeriv_concreteCenteredRankOneCOEEventPath
            hH16 hfixedC4 hscore hN hboundary hq_lt event hevent z).deriv
  exact hind r hr y

/-- Exact-quantifier wrapper matching the original H18 declaration. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_conditional
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hfixedC4 : CoeCornerCenteredFixedDirectionC4Contract)
    (hscore : CoeCornerCenteredPositiveScoreL1ThroughFourContract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y =
      ∫ v : ComplexUnitSphere N,
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y
          ∂(complexUnitSphereProbabilityMeasure N) := by
  exact coeCorner_centeredProjective_eventPath_derivative_interchange_at_conditional
    hH16 hfixedC4 hscore hN hboundary hr event hevent y

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
