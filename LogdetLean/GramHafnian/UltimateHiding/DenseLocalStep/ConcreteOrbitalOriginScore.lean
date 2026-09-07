import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.SharedBetaCOEPathIdentification
import LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep.ConcreteCentralEventScore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredQuadraticScore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthSecantIntegralVanishingFromPointwiseFTC

/-!
# First and second orbital scores for the same-beta COE path

This file connects the exact projectively averaged centered-COE score
identities to the concrete same-beta orbital event path.  The first
derivative vanishes before taking absolute values.  The second derivative
is then bounded eventwise by the internally assembled `L^1` estimate for the
literal centered quadratic density.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.CurrentPRL

/-- The actual shared-beta orbital event path has zero first derivative at
the origin.  This is the exact projective cancellation `E_v Q_v = 0`, after
rewriting the fixed-beta path as the centered COE path on the corresponding
central preimage event. -/
theorem iteratedDeriv_one_concreteSharedBetaOrbitalEventPath_eq_zero
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    iteratedDeriv 1
        (concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)
          q event) 0 = 0 := by
  let preevent := concreteCentralMatrixUpdate N
    (oneColumnCenteredScalarLog m N q) ⁻¹' event
  have hpre : MeasurableSet preevent :=
    (measurable_concreteCentralMatrixUpdate N _) hevent
  have hfun : concreteSharedBetaOrbitalEventPath m N
      (concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K)
      q event =
      concreteProjectiveAveragedCenteredCOEEventPath N K preevent := by
    funext t
    exact concreteSharedBetaOrbitalEventPath_eq_projectiveCenteredCOE
      hN (by omega) q event hevent t
  rw [hfun]
  rw [coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_proved_from_A1
    (r := 1) hN (by omega) (by omega) preevent hpre 0]
  simp_rw [coeCorner_centeredFixedDirection_eventPath_derivative_H16_proved_from_A1
    (N := N) (K := K) (r := 1) hN (by omega) (by omega) _ preevent hpre]
  rw [coeCorner_centeredDensityScore_one_fubini
    hN (by omega) preevent hpre]
  apply integral_eq_zero_of_ae
  filter_upwards
    [friedmanMello1985_scaledCOECorner_ae_support_from_density hN (by omega)]
      with A hA
  rcases hA with ⟨hsymm, hsupport⟩
  by_cases hmem : A ∈ preevent
  · simp only [Set.indicator, hmem, if_true]
    have hscore : (fun v : ComplexUnitSphere N ↦
        concreteCenteredDensityScore 1 N K v A) =
        (fun v ↦ concreteCenteredRankOneFirstDensityScore N K v A) := by
      funext v
      exact coeCorner_centeredDensityScore_one_eq_explicit_external_derived
        hN (by omega) v A hsymm hsupport
    rw [hscore, integral_concreteCenteredRankOneFirstDensityScore hN A]
    simp
  · simp [Set.indicator, hmem]

/-- Eventwise second-order orbital score bound for the actual shared-beta
path.  The constant is dimension-free and comes from the concrete quadratic
COE score, not from an aggregate derivative assumption. -/
theorem abs_iteratedDeriv_two_concreteSharedBetaOrbitalEventPath_le
    {m N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (q : ℝ) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    |iteratedDeriv 2
        (concreteSharedBetaOrbitalEventPath m N
          (concreteScaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K)
          q event) 0| ≤ concreteOrbitalScoreTwoConstant := by
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
    concrete_projectiveAveraged_centered_second_derivative_eq_density_indicator_integral
      hN hdense preevent hpre]
  letI : IsProbabilityMeasure mu :=
    canonicalScaledCOECornerLaw_isProbability (by omega)
  have hmemOne : MemLp (concreteCenteredQuadraticDensity N K) 1 mu :=
    (concreteCenteredQuadraticDensity_memLp_two hN hdense).mono_exponent
      (by norm_num)
  exact (abs_integral_indicator_le_lpNorm_one
    hmemOne hpre).trans
      (concreteCenteredQuadraticDensity_lpNorm_one_le hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
