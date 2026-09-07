import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H18_Proof

/-!
# CONDITIONAL H18 from compact-time zero-extended `L^1` envelopes

This is the moving-support-safe route.  The literal score is extended by zero
off the scaled symmetric COE support.  H16 identifies its fixed-direction
event integrals, genuine fixed-direction `C^4` supplies differentiability, and
one sphere-integrable envelope controls the `L^1` norms of the zero-extended
representatives on each compact time interval.

The exact hypotheses `1 ≤ N` and `2 * N + 8 ≤ K` occur in every scientific
contract below.  No projective-average conclusion occurs in a contract.
-/

open TopologicalSpace MeasureTheory Set Filter
open scoped Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The full scaled symmetric COE support. -/
def concreteScaledCOECornerSupportSet (N K : ℕ) :
    Set (ConcreteMatrixState N) :=
  {A | (unscaleCOECorner K A).IsSymm ∧
    coeCornerSupport (unscaleCOECorner K A)}

/-- A genuinely global score representative: it is exactly zero off the
scaled symmetric COE support. -/
def concreteCenteredDensityScoreZeroExt
    (r N K : ℕ) (v : ComplexUnitSphere N) :
    ConcreteMatrixState N → ℝ :=
  (concreteScaledCOECornerSupportSet N K).indicator
    (concreteCenteredDensityScore r N K v)

theorem concreteCenteredDensityScoreZeroExt_eq_zero_of_notMem
    {r N K : ℕ} {v : ComplexUnitSphere N} {A : ConcreteMatrixState N}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hA : A ∉ concreteScaledCOECornerSupportSet N K) :
    concreteCenteredDensityScoreZeroExt r N K v A = 0 := by
  exact Set.indicator_of_notMem hA _

/-- The product-space event selected after the centered flow at time `t`. -/
def concreteCenteredZeroExtShiftedEvent
    (N : ℕ) (t : ℝ) (event : Set (ConcreteMatrixState N)) :
    Set (ConcreteMatrixState N × ComplexUnitSphere N) :=
  {Av | transposeCongruenceFlow
      (concreteCenteredOrbitalDirection N Av.2) t Av.1 ∈ event}

/-- The zero-extended fixed-direction derivative representative restricted to
the shifted event. -/
def concreteCenteredZeroExtEventDerivativeIntegrand
    (r N K : ℕ) (event : Set (ConcreteMatrixState N)) (t : ℝ) :
    ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
  (concreteCenteredZeroExtShiftedEvent N t event).indicator
    (fun Av ↦ concreteCenteredDensityScoreZeroExt r N K Av.2 Av.1)

theorem concreteCenteredZeroExtEventDerivativeIntegrand_eq_zero_off_support
    {r N K : ℕ} {event : Set (ConcreteMatrixState N)} {t : ℝ}
    {A : ConcreteMatrixState N} {v : ComplexUnitSphere N}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hA : A ∉ concreteScaledCOECornerSupportSet N K) :
    concreteCenteredZeroExtEventDerivativeIntegrand r N K event t (A, v) = 0 := by
  by_cases hmem : (A, v) ∈ concreteCenteredZeroExtShiftedEvent N t event
  · rw [concreteCenteredZeroExtEventDerivativeIntegrand,
      Set.indicator_of_mem hmem,
      concreteCenteredDensityScoreZeroExt_eq_zero_of_notMem hN hboundary hA]
  · exact Set.indicator_of_notMem hmem _

/-- CONDITIONAL a.e. agreement between the literal score and its global zero
extension.  The equality is deliberately a.e., not pointwise at the moving
support boundary. -/
def CoeCornerCenteredZeroExtScoreAgreementContract : Prop :=
  ∀ {N K r : ℕ}, (1 ≤ N) → (2 * N + 8 ≤ K) → (r ≤ 4) →
    (v : ComplexUnitSphere N) →
    concreteCenteredDensityScoreZeroExt r N K v =ᵐ[
      concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
          N K]
      concreteCenteredDensityScore r N K v

/-- Still smaller CONDITIONAL source-level interface: the scaled COE law is
supported on the set used by the global zero extension.  This contract is
independent of derivative order and direction. -/
def CoeCornerCenteredScaledCOESupportContract : Prop :=
  ∀ {N K : ℕ}, (1 ≤ N) → (2 * N + 8 ≤ K) →
    ∀ᵐ A ∂(concreteScaledCOECornerLaw
      LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
        N K),
      A ∈ concreteScaledCOECornerSupportSet N K

/-- Almost-sure support internally implies agreement with the definitionally
zero-extended score for every order and direction. -/
theorem zeroExtScoreAgreement_of_scaledCOESupport
    (hsupport : CoeCornerCenteredScaledCOESupportContract) :
    CoeCornerCenteredZeroExtScoreAgreementContract := by
  intro N K r hN hboundary hr v
  filter_upwards [hsupport hN hboundary] with A hA
  simpa only [concreteCenteredDensityScoreZeroExt] using
    (Set.indicator_of_mem hA
      (concreteCenteredDensityScore r N K v))

/-- CONDITIONAL compact-time `L^1` envelope for the global zero-extended
representatives.  For each fixed time, product integrability provides joint
measurability in matrix and direction.  The last conjunct uses one common
full-measure set of directions for every time in the compact interval. -/
def CoeCornerCenteredCompactZeroExtL1EnvelopeContract : Prop :=
  ∀ {N K r : ℕ}, (1 ≤ N) → (2 * N + 8 ≤ K) → (r ≤ 4) →
    (event : Set (ConcreteMatrixState N)) → MeasurableSet event →
    (R : ℝ) → (0 < R) →
    ∃ B : ComplexUnitSphere N → ℝ,
      Integrable B (complexUnitSphereProbabilityMeasure N) ∧
      (∀ t ∈ Set.Icc (-R) R,
        Integrable
          (concreteCenteredZeroExtEventDerivativeIntegrand
            r N K event t)
          ((concreteScaledCOECornerLaw
              LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
                N K).prod (complexUnitSphereProbabilityMeasure N))) ∧
      (∀ᵐ v ∂(complexUnitSphereProbabilityMeasure N),
        ∀ t ∈ Set.Icc (-R) R,
          Integrable
            (fun A : ConcreteMatrixState N ↦
              concreteCenteredZeroExtEventDerivativeIntegrand
                r N K event t (A, v))
            (concreteScaledCOECornerLaw
              LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
                N K) ∧
          (∫ A : ConcreteMatrixState N,
              ‖concreteCenteredZeroExtEventDerivativeIntegrand
                r N K event t (A, v)‖
              ∂(concreteScaledCOECornerLaw
                LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
                  N K)) ≤ B v)

/-- H16 plus a.e. zero-extension agreement represents every all-time
fixed-direction derivative by the global zero-extended integrand. -/
theorem coeCorner_centeredFixedDirection_eventPath_derivative_zeroExt
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hzero : CoeCornerCenteredZeroExtScoreAgreementContract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (v : ComplexUnitSphere N)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (t : ℝ) :
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) t =
      ∫ A : ConcreteMatrixState N,
        concreteCenteredZeroExtEventDerivativeIntegrand
          r N K event t (A, v)
        ∂(concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K) := by
  rw [coeCorner_centeredFixedDirection_eventPath_derivative_at_conditional
    hH16 hN hboundary hr v event hevent t]
  apply integral_congr_ae
  filter_upwards [hzero hN hboundary hr v] with A hA
  by_cases hmem : transposeCongruenceFlow
      (concreteCenteredOrbitalDirection N v) t A ∈ event
  · simp [concreteCenteredZeroExtEventDerivativeIntegrand,
      concreteCenteredZeroExtShiftedEvent, hmem, hA]
  · simp [concreteCenteredZeroExtEventDerivativeIntegrand,
      concreteCenteredZeroExtShiftedEvent, hmem]

/-- A compact-time envelope for the zero-extended `L^1` representatives
induces the required sphere integrability and a common direction majorant for
the actual fixed-direction iterated derivatives. -/
theorem exists_compact_directionMajorant_iteratedDeriv_zeroExt
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hzero : CoeCornerCenteredZeroExtScoreAgreementContract)
    (henvelope : CoeCornerCenteredCompactZeroExtL1EnvelopeContract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (R : ℝ) (hR : 0 < R) :
    ∃ B : ComplexUnitSphere N → ℝ,
      Integrable B (complexUnitSphereProbabilityMeasure N) ∧
      (∀ t ∈ Set.Icc (-R) R,
        Integrable
          (fun v : ComplexUnitSphere N ↦
            iteratedDeriv r
              (concreteCenteredRankOneCOEEventPath K v event) t)
          (complexUnitSphereProbabilityMeasure N)) ∧
      (∀ᵐ v ∂(complexUnitSphereProbabilityMeasure N),
        ∀ t ∈ Set.Icc (-R) R,
          ‖iteratedDeriv r
              (concreteCenteredRankOneCOEEventPath K v event) t‖ ≤ B v) := by
  letI : IsProbabilityMeasure
      (concreteScaledCOECornerLaw
        LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
          N K) :=
    canonicalScaledCOECornerLaw_isProbability (by omega : N ≤ K)
  letI : IsProbabilityMeasure (complexUnitSphereProbabilityMeasure N) :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  obtain ⟨B, hB, hprod, hsections⟩ :=
    henvelope hN hboundary hr event hevent R hR
  refine ⟨B, hB, ?_, ?_⟩
  · intro t ht
    have hfun :
        (fun v : ComplexUnitSphere N ↦
          iteratedDeriv r
            (concreteCenteredRankOneCOEEventPath K v event) t) =
          fun v : ComplexUnitSphere N ↦
            ∫ A : ConcreteMatrixState N,
              concreteCenteredZeroExtEventDerivativeIntegrand
                r N K event t (A, v)
              ∂(concreteScaledCOECornerLaw
                LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
                  N K) := by
      funext v
      exact coeCorner_centeredFixedDirection_eventPath_derivative_zeroExt
        hH16 hzero hN hboundary hr v event hevent t
    rw [hfun]
    exact (hprod t ht).integral_prod_right
  · filter_upwards [hsections] with v hv
    intro t ht
    rw [coeCorner_centeredFixedDirection_eventPath_derivative_zeroExt
      hH16 hzero hN hboundary hr v event hevent t]
    exact (norm_integral_le_integral_norm _).trans (hv t ht).2

/-- One recursive differentiation step under the projective integral, using
only a compact interval around the evaluation point. -/
theorem hasDerivAt_integral_iteratedDeriv_compact_zeroExt
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hfixedC4 : CoeCornerCenteredFixedDirectionC4Contract)
    (hzero : CoeCornerCenteredZeroExtScoreAgreementContract)
    (henvelope : CoeCornerCenteredCompactZeroExtL1EnvelopeContract)
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
    iteratedDeriv r (concreteCenteredRankOneCOEEventPath K v event) x
  let F' : ℝ → ComplexUnitSphere N → ℝ := fun x v ↦
    iteratedDeriv (r + 1)
      (concreteCenteredRankOneCOEEventPath K v event) x
  let R : ℝ := |y| + 1
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hy : y ∈ Set.Ioo (-R) R := by
    dsimp [R]
    constructor
    · linarith [neg_le_abs y]
    · linarith [le_abs_self y]
  have hs : Set.Ioo (-R) R ∈ 𝓝 y := isOpen_Ioo.mem_nhds hy
  have hrsucc : r + 1 ≤ 4 := by omega
  obtain ⟨B, hB, hIntSucc, hboundCompact⟩ :=
    exists_compact_directionMajorant_iteratedDeriv_zeroExt
      hH16 hzero henvelope hN hboundary hrsucc event hevent R hR
  obtain ⟨B0, hB0, hInt, hbound0⟩ :=
    exists_compact_directionMajorant_iteratedDeriv_zeroExt
      hH16 hzero henvelope hN hboundary (by omega : r ≤ 4)
        event hevent R hR
  have hF_meas : ∀ᶠ x in 𝓝 y, AEStronglyMeasurable (F x) sphere := by
    filter_upwards [hs] with x hx
    exact (hInt x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).1
  have hF_int : Integrable (F y) sphere := by
    exact hInt y ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  have hF'_meas : AEStronglyMeasurable (F' y) sphere := by
    exact (hIntSucc y ⟨le_of_lt hy.1, le_of_lt hy.2⟩).1
  have hbound : ∀ᵐ v ∂sphere, ∀ x ∈ Set.Ioo (-R) R,
      ‖F' x v‖ ≤ B v := by
    filter_upwards [hboundCompact] with v hv
    intro x hx
    exact hv x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hdiff : ∀ᵐ v ∂sphere, ∀ x ∈ Set.Ioo (-R) R,
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
    (F := F) (F' := F') (bound := B) (s := Set.Ioo (-R) R) (x₀ := y)
    hs hF_meas hF_int hF'_meas hbound hB hdiff).2

/-- CONDITIONAL H18 from compact-time zero-extended `L^1` envelopes. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_at_compactL1_conditional
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hfixedC4 : CoeCornerCenteredFixedDirectionC4Contract)
    (hzero : CoeCornerCenteredZeroExtScoreAgreementContract)
    (henvelope : CoeCornerCenteredCompactZeroExtL1EnvelopeContract) :
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
        exact (hasDerivAt_integral_iteratedDeriv_compact_zeroExt
          hH16 hfixedC4 hzero henvelope hN hboundary hq_lt
            event hevent z).deriv
  exact hind r hr y

/-- Exact-quantifier wrapper matching the original H18 declaration. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_compactL1_conditional
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hfixedC4 : CoeCornerCenteredFixedDirectionC4Contract)
    (hzero : CoeCornerCenteredZeroExtScoreAgreementContract)
    (henvelope : CoeCornerCenteredCompactZeroExtL1EnvelopeContract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y =
      ∫ v : ComplexUnitSphere N,
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y
          ∂(complexUnitSphereProbabilityMeasure N) := by
  exact
    coeCorner_centeredProjective_eventPath_derivative_interchange_at_compactL1_conditional
      hH16 hfixedC4 hzero henvelope hN hboundary hr event hevent y

/-- Exact H18 wrapper using only the order-independent a.e. support contract
instead of a separate score-agreement premise. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_compactL1_support_conditional
    (hH16 : CoeCornerCenteredFixedDirectionH16Contract)
    (hfixedC4 : CoeCornerCenteredFixedDirectionC4Contract)
    (hsupport : CoeCornerCenteredScaledCOESupportContract)
    (henvelope : CoeCornerCenteredCompactZeroExtL1EnvelopeContract)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y =
      ∫ v : ComplexUnitSphere N,
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y
          ∂(complexUnitSphereProbabilityMeasure N) := by
  exact
    coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_compactL1_conditional
      hH16 hfixedC4 (zeroExtScoreAgreement_of_scaledCOESupport hsupport)
        henvelope hN hboundary hr event hevent y

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
