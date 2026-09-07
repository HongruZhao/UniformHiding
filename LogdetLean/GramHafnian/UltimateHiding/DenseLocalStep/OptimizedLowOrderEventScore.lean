import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteOrbitalOriginScore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.OptimizedCentralAndQuadraticScoreBounds

/-!
# Optimized low-order event-score endpoints

These are the event-path versions of the optimized first, second, and
averaged quadratic density-score estimates.  The derivative identities and
regularity inputs are unchanged.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Optimized base central first-event-derivative bound. -/
theorem abs_iteratedDeriv_one_concreteBaseCentralEventPath_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    |iteratedDeriv 1
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event) 0| ≤
      optimizedCentralScoreOneConstant * (N : ℝ) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [(LogdetLean.GramHafnian.UltimateHiding.H3H4Central.coeCorner_centralEventPath_derivatives_external_derived_of_A1
    hN hgap event hevent).1]
  exact (abs_integral_indicator_le_lpNorm_one
    (concreteCentralLogScoreOne_memLp_one hN hgap) hevent).trans
      (concreteCentralLogScoreOne_lpNorm_one_le_optimized hN hdense)

/-- Optimized base central second-event-derivative bound, uniform in time. -/
theorem abs_iteratedDeriv_two_concreteBaseCentralEventPath_le_optimized
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event)
    (y : ℝ) :
    |iteratedDeriv 2
        (concreteCentralEventPath N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) event) y| ≤
      optimizedCentralScoreTwoConstant * (N : ℝ) ^ 2 := by
  let mu := concreteScaledCOECornerLaw
    canonicalUnitaryHaarProbabilityFamily N K
  let shifted := concreteCentralMatrixUpdate N y ⁻¹' event
  have hshifted : MeasurableSet shifted :=
    (measurable_concreteCentralMatrixUpdate N y) hevent
  rw [iteratedDeriv_concreteCentralEventPath_eq_zero_shift
    2 N mu event hevent y]
  have hgap : 2 * N + 8 ≤ K := by omega
  rw [(LogdetLean.GramHafnian.UltimateHiding.H3H4Central.coeCorner_centralEventPath_derivatives_external_derived_of_A1
    hN hgap shifted hshifted).2]
  exact (abs_integral_indicator_le_lpNorm_one
    (concreteCentralDensityScoreTwo_memLp_one hN hdense) hshifted).trans
      (concreteCentralDensityScoreTwo_lpNorm_one_le_optimized hN hdense)

/-- Optimized eventwise second-order orbital score bound. -/
theorem abs_iteratedDeriv_two_concreteSharedBetaOrbitalEventPath_le_optimized
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    |iteratedDeriv 2
        (concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)
          q event) 0| ≤ optimizedOrbitalScoreTwoConstant := by
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
    concrete_projectiveAveraged_centered_second_derivative_eq_density_indicator_integral_H14Rewire
      hN hdense preevent hpre]
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hmemOne : MemLp (concreteCenteredQuadraticDensity N K) 1 mu :=
    (concreteCenteredQuadraticDensity_memLp_two_H14Rewire
      hN hdense).mono_exponent (by norm_num)
  exact (abs_integral_indicator_le_lpNorm_one hmemOne hpre).trans
    (concreteCenteredQuadraticDensity_lpNorm_one_le_optimized hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
