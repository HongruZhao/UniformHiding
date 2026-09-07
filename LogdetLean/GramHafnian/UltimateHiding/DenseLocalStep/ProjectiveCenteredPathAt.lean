import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredCOERawExternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFixedDirectionPathShift
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredFourthScore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthSecantIntegralVanishingFromPointwiseFTC
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCentralEventScore
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.SharedBetaCOEPathIdentification
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!
# All-time projective centered-COE derivatives

For each fixed projective direction the centered congruence is an additive
flow, and its arbitrary-time derivative is already reduced internally to an
origin derivative for a shifted event.  This file isolates the remaining
compact-parameter derivative formula at an arbitrary time.  It then proves
internally that every such derivative is bounded by the product-law `L^1`
norm of the literal centered score.  The release uses the proved H18
interchange theorem and therefore omits the obsolete duplicate regularity
declaration formerly stored here.
-/

open MeasureTheory Set

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

/-- Product-space event obtained by shifting an event in the same centered
projective direction carried by the second coordinate. -/
def concreteCenteredShiftedProjectiveEvent
    (N : ℕ) (y : ℝ) (event : Set (ConcreteMatrixState N)) :
    Set (ConcreteMatrixState N × ComplexUnitSphere N) :=
  (fun Av ↦ concreteOrbitalMatrixUpdate N y Av.2 Av.1) ⁻¹' event

theorem measurableSet_concreteCenteredShiftedProjectiveEvent
    {N : ℕ} (y : ℝ) {event : Set (ConcreteMatrixState N)}
    (hevent : MeasurableSet event) :
    MeasurableSet (concreteCenteredShiftedProjectiveEvent N y event) := by
  exact (measurable_concreteOrbitalMatrixUpdate N y) hevent

/-- Exact arbitrary-time derivative formula after the deterministic flow
shift.  The event may now depend on the projective direction, but the score
is still the literal origin score against the original square-COE law. -/
theorem coeCorner_centeredProjective_eventPath_derivative_at_eq_shifted
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y =
      ∫ v : ComplexUnitSphere N,
        ∫ A, (transposeCongruenceFlow
            (concreteCenteredOrbitalDirection N v) y ⁻¹' event).indicator
              (concreteCenteredDensityScore r N K v) A
          ∂(concreteScaledCOECornerLaw
            LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
              N K)
        ∂(complexUnitSphereProbabilityMeasure N) := by
  rw [coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_proved_from_A1
    hN hboundary hr event hevent y]
  apply integral_congr_ae
  filter_upwards [] with v
  rw [iteratedDeriv_concreteCenteredRankOneCOEEventPath_eq_zero_shift
    r K v event hevent y]
  exact coeCorner_centeredFixedDirection_eventPath_derivative_H16_proved_from_A1
    hN hboundary hr v _
      ((by
        unfold transposeCongruenceFlow
        exact measurable_transposeCongruence _ : Measurable
          (transposeCongruenceFlow
            (concreteCenteredOrbitalDirection N v) y)) hevent)

/-- The shifted iterated integral is exactly an indicator integral on the
COE/projective product space. -/
theorem shifted_centeredScore_integral_eq_prod
    {N K r : ℕ} (hN : 1 ≤ N) (hNK : N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ)
    (hscore : MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore r N K Av.2 Av.1) 1
      ((concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K).prod (complexUnitSphereProbabilityMeasure N))) :
    (∫ v : ComplexUnitSphere N,
        ∫ A, (transposeCongruenceFlow
            (concreteCenteredOrbitalDirection N v) y ⁻¹' event).indicator
              (concreteCenteredDensityScore r N K v) A
          ∂(concreteScaledCOECornerLaw
            LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
              N K)
        ∂(complexUnitSphereProbabilityMeasure N)) =
      ∫ Av, (concreteCenteredShiftedProjectiveEvent N y event).indicator
          (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
            concreteCenteredDensityScore r N K Av.2 Av.1) Av
        ∂((concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K).prod (complexUnitSphereProbabilityMeasure N)) := by
  let mu := concreteScaledCOECornerLaw
    LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily N K
  let sphere := complexUnitSphereProbabilityMeasure N
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore r N K Av.2 Av.1
  let shifted := concreteCenteredShiftedProjectiveEvent N y event
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability hNK
  letI : IsProbabilityMeasure sphere :=
    complexUnitSphereProbabilityMeasure_isProbability hN
  have hshifted : MeasurableSet shifted :=
    measurableSet_concreteCenteredShiftedProjectiveEvent y hevent
  have hscoreInt : Integrable score (mu.prod sphere) :=
    memLp_one_iff_integrable.mp hscore
  have hind : Integrable (shifted.indicator score) (mu.prod sphere) :=
    hscoreInt.indicator hshifted
  rw [integral_prod_symm _ hind]
  apply integral_congr_ae
  filter_upwards [] with v
  apply integral_congr_ae
  filter_upwards [] with A
  have hflow := transposeCongruenceFlow_centered_eq_concreteOrbitalMatrixUpdate
    hN y v A
  by_cases hmem : concreteOrbitalMatrixUpdate N y v A ∈ event
  · have hmemFlow :
        transposeCongruenceFlow (concreteCenteredOrbitalDirection N v) y A ∈
          event := by simpa [hflow] using hmem
    simp [shifted, concreteCenteredShiftedProjectiveEvent, score, hmem,
      hmemFlow]
  · have hmemFlow :
        transposeCongruenceFlow (concreteCenteredOrbitalDirection N v) y A ∉
          event := by simpa [hflow] using hmem
    simp [shifted, concreteCenteredShiftedProjectiveEvent, score, hmem,
      hmemFlow]

/-- All-time event derivatives are bounded by the product-law `L^1` norm of
the literal centered score.  This is the internal triangle/Fubini step that
keeps every numerical estimate out of the analytic interchange boundary. -/
theorem abs_coeCorner_centeredProjective_eventPath_derivative_at_le_lpNorm_one
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ)
    (hscore : MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore r N K Av.2 Av.1) 1
      ((concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K).prod (complexUnitSphereProbabilityMeasure N))) :
    |iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y| ≤
      lpNorm
        (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
          concreteCenteredDensityScore r N K Av.2 Av.1) 1
        ((concreteScaledCOECornerLaw
          LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
            N K).prod (complexUnitSphereProbabilityMeasure N)) := by
  rw [coeCorner_centeredProjective_eventPath_derivative_at_eq_shifted
    hN hboundary hr event hevent y]
  rw [shifted_centeredScore_integral_eq_prod hN (by omega) event hevent y hscore]
  exact LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.abs_integral_indicator_le_lpNorm_one
    hscore
      (measurableSet_concreteCenteredShiftedProjectiveEvent y hevent)

/-! ## Literal fourth-score specialization -/

/-- On the actual COE/projective product law, the literal fourth density
score is almost everywhere the internally assembled fourth Bell polynomial.
The only analytic equality used here is the pointwise-on-support determinant
calculus identity; lifting the COE support to the product is internal. -/
theorem concreteCenteredDensityScoreFourProduct_ae_eq_Bell
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
      concreteCenteredDensityScore 4 N K Av.2 Av.1) =ᵐ[
        concreteCenteredScoreProductLaw N K]
      concreteCenteredBellFourProduct N K := by
  have hsupportA :=
    friedmanMello1985_scaledCOECorner_ae_support_from_density
      hN (by omega : 2 * N ≤ K)
  have hsupport : ∀ᵐ Av ∂(concreteCenteredScoreProductLaw N K),
      (unscaleCOECorner K Av.1).IsSymm ∧
        coeCornerSupport (unscaleCOECorner K Av.1) :=
    Measure.quasiMeasurePreserving_fst.ae hsupportA
  filter_upwards [hsupport] with Av hAv
  rcases hAv with ⟨hsymm, hsupp⟩
  simpa [concreteCenteredBellFourProduct, concreteCenteredEll] using
    coeCorner_centeredDensityScore_four_eq_Bell_external_derived
      hN (by omega) Av.2 Av.1 hsymm hsupp

/-- The literal fourth density score itself belongs to product `L^1`. -/
theorem concreteCenteredDensityScoreFourProduct_memLp_one
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    MemLp
      (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
        concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
      (concreteCenteredScoreProductLaw N K) := by
  exact (memLp_congr_ae
    (concreteCenteredDensityScoreFourProduct_ae_eq_Bell hN hdense)).2
      (concreteCenteredBellFourProduct_memLp_one hN hdense)

/-- The literal fourth density score inherits the internally assembled
`O(N^2)` Bell bound. -/
theorem concreteCenteredDensityScoreFourProduct_lpNorm_one_le
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm
        (fun Av : ConcreteMatrixState N × ComplexUnitSphere N ↦
          concreteCenteredDensityScore 4 N K Av.2 Av.1) 1
        (concreteCenteredScoreProductLaw N K) ≤
      concreteCenteredScoreFourConstant * (N : ℝ) ^ 2 := by
  let score : ConcreteMatrixState N × ComplexUnitSphere N → ℝ :=
    fun Av ↦ concreteCenteredDensityScore 4 N K Av.2 Av.1
  let bell := concreteCenteredBellFourProduct N K
  let law := concreteCenteredScoreProductLaw N K
  have heq : score =ᵐ[law] bell :=
    concreteCenteredDensityScoreFourProduct_ae_eq_Bell hN hdense
  have hscore : MemLp score 1 law :=
    concreteCenteredDensityScoreFourProduct_memLp_one hN hdense
  have hbell : MemLp bell 1 law :=
    concreteCenteredBellFourProduct_memLp_one hN hdense
  have hnorm : lpNorm score 1 law = lpNorm bell 1 law := by
    rw [lpNorm_one_eq_integral_norm hscore.aestronglyMeasurable,
      lpNorm_one_eq_integral_norm hbell.aestronglyMeasurable]
    exact integral_congr_ae <| heq.mono fun Av hAv ↦ congrArg norm hAv
  rw [hnorm]
  exact concreteCenteredBellFourProduct_lpNorm_one_le hN hdense

/-- Every fourth derivative of the projectively averaged centered COE event
path is bounded by the same `O(N^2)` constant, uniformly in time. -/
theorem abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    |iteratedDeriv 4
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y| ≤
      concreteCenteredScoreFourConstant * (N : ℝ) ^ 2 := by
  have hraw :=
    abs_coeCorner_centeredProjective_eventPath_derivative_at_le_lpNorm_one
      hN (by omega) (by omega) event hevent y
      (concreteCenteredDensityScoreFourProduct_memLp_one hN hdense)
  exact hraw.trans
    (concreteCenteredDensityScoreFourProduct_lpNorm_one_le hN hdense)

/-- The actual same-beta orbital event path inherits the all-time fourth
score bound after changing only the event by the same beta sample's central
preimage. -/
theorem abs_iteratedDeriv_four_concreteSharedBetaOrbitalEventPath_le
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    |iteratedDeriv 4
        (concreteSharedBetaOrbitalEventPath m N
            (concreteScaledCOECornerLaw
              LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
                N K)
            q event) y| ≤
      concreteCenteredScoreFourConstant * (N : ℝ) ^ 2 := by
  let preevent := concreteCentralMatrixUpdate N
    (oneColumnCenteredScalarLog m N q) ⁻¹' event
  have hpre : MeasurableSet preevent :=
    (measurable_concreteCentralMatrixUpdate N _) hevent
  have hfun :
      concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
              N K)
          q event =
        concreteProjectiveAveragedCenteredCOEEventPath N K preevent := by
    funext t
    exact concreteSharedBetaOrbitalEventPath_eq_projectiveCenteredCOE
        hN (by omega) q event hevent t
  rw [hfun]
  exact abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le
    hN hdense preevent hpre y

/-- The actual same-beta orbital event path is `C^4`, uniformly for every
fixed beta sample and event. -/
theorem concreteSharedBetaOrbitalEventPath_contDiff_four
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    ContDiff ℝ 4
      (concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
              N K)
          q event) := by
  let preevent := concreteCentralMatrixUpdate N
    (oneColumnCenteredScalarLog m N q) ⁻¹' event
  have hpre : MeasurableSet preevent :=
    (measurable_concreteCentralMatrixUpdate N _) hevent
  have hfun :
      concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            LogdetLean.GramHafnian.CurrentPRL.canonicalUnitaryHaarProbabilityFamily
              N K)
          q event =
        concreteProjectiveAveragedCenteredCOEEventPath N K preevent := by
    funext t
    exact concreteSharedBetaOrbitalEventPath_eq_projectiveCenteredCOE
        hN (by omega) q event hevent t
  rw [hfun]
  exact coeCorner_centeredProjective_eventPath_contDiff_four_H17_proved_from_A1
    hN (by omega) preevent hpre

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
