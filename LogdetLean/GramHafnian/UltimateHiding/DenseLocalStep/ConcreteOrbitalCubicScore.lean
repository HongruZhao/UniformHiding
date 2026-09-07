import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteOrbitalOriginScore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7ExactConcreteCenteredCubicIdentification
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredScoreFubiniThirdInternal
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CubicTraceThreeRemainderBound
import Mathlib.Tactic

/-!
# Origin cubic score for the same-beta orbital path

This file connects the internally assembled exact R25 density to the third
event derivative of the actual same-beta orbital path.  The event estimate is
then just restriction by an indicator followed by the proved `L^1` bound.
No aggregate event-score, total-variation, local-step, or hiding statement is
assumed.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- The third derivative at the origin of the actual same-beta orbital event
path is `O(N)`.  This is derived eventwise from the supported-state R25
identity and the internally assembled centered cubic `L^1` estimate. -/
theorem abs_iteratedDeriv_three_concreteSharedBetaOrbitalEventPath_zero_le
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    |iteratedDeriv 3
        (concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)
          q event) 0| ≤
      concreteAveragedCenteredCubicNormalizationConstant * (N : ℝ) := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let preevent := concreteCentralMatrixUpdate N
    (oneColumnCenteredScalarLog m N q) ⁻¹' event
  have hpre : MeasurableSet preevent :=
    (measurable_concreteCentralMatrixUpdate N _) hevent
  have hfun : concreteSharedBetaOrbitalEventPath m N mu q event =
      concreteProjectiveAveragedCenteredCOEEventPath N K preevent := by
    funext t
    exact concreteSharedBetaOrbitalEventPath_eq_projectiveCenteredCOE
      hN (by omega) q event hevent t
  rw [hfun,
    coeCorner_centeredProjective_eventPath_derivative_literal_three_internal
      hN (by omega) preevent hpre]
  have hclosed : (fun A ↦ preevent.indicator (fun A ↦
        ∫ v : ComplexUnitSphere N,
          concreteCenteredDensityScore 3 N K v A
            ∂(complexUnitSphereProbabilityMeasure N)) A) =ᵐ[mu]
      preevent.indicator (concreteAveragedCenteredCubicDensity N K) := by
    filter_upwards
      [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
        with A hA
    rcases hA with ⟨hsymm, hsupport⟩
    by_cases hmem : A ∈ preevent
    · simp only [Set.indicator, hmem, if_true]
      exact integral_concreteCenteredDensityScoreThree_eq_density_of_H7Exact
        hN hdense A hsymm hsupport
    · simp only [Set.indicator, hmem, if_false]
  rw [integral_congr_ae hclosed]
  exact (abs_integral_indicator_le_lpNorm_one
      (concreteAveragedCenteredCubicDensity_memLp_one_normalization_internal
        hN hdense) hpre).trans
    (concreteAveragedCenteredCubicDensity_lpNorm_one_le_normalization_internal
      hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
