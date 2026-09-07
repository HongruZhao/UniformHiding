import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloSupportFromDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Coordinate form of the determinant-density law

This module contains only measure-theoretic bookkeeping.  It rewrites the
normalized determinant-density measure as an ordinary real integral on the
independent complex-symmetric coordinates.  The Friedman--Mello equality is
never invoked here.
-/

open MeasureTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.H3H4Central

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- Total mass of the unnormalized determinant-density measure. -/
def coeCornerRawMass (N K : ℕ) : ℝ≥0∞ :=
  coeCornerRawDeterminantDensityMeasure N K Set.univ

/-- The real coordinate density after the literal normalization used in
`coeCornerDeterminantDensityProbabilityMeasure`. -/
def coeCornerCoordinateProbabilityDensity (N K : ℕ)
    (x : ComplexSymmetricCoordinates N) : ℝ :=
  (coeCornerRawMass N K)⁻¹.toReal *
    (coeCornerDeterminantWeight N K x).toReal

theorem coeCornerDeterminantWeight_lt_top (N K : ℕ)
    (x : ComplexSymmetricCoordinates N) :
    coeCornerDeterminantWeight N K x < ∞ := by
  classical
  simp only [coeCornerDeterminantWeight]
  split <;> simp

theorem measurable_coeCornerCoordinateProbabilityDensity (N K : ℕ) :
    Measurable (coeCornerCoordinateProbabilityDensity N K) := by
  unfold coeCornerCoordinateProbabilityDensity
  exact measurable_const.mul
    (measurable_coeCornerDeterminantWeight N K).ennreal_toReal

/-- The normalized determinant-density measure evaluated on a measurable
matrix event is the integral of its literal real coordinate density. -/
theorem coeCornerDeterminantDensityProbabilityMeasure_real_eq_integral
    {N K : ℕ} (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) :
    (coeCornerDeterminantDensityProbabilityMeasure N K).real event =
      ∫ x, (complexSymmetricMatrixOfCoordinates ⁻¹' event).indicator
        (coeCornerCoordinateProbabilityDensity N K) x
        ∂(complexSymmetricCoordinateVolume N) := by
  let M := complexSymmetricMatrixOfCoordinates (N := N)
  let volumeC := complexSymmetricCoordinateVolume N
  let weight := coeCornerDeterminantWeight N K
  let raw := coeCornerRawDeterminantDensityMeasure N K
  let pre := M ⁻¹' event
  have hM : Measurable M := measurable_complexSymmetricMatrixOfCoordinates N
  have hpre : MeasurableSet pre := hevent.preimage hM
  have hweight : Measurable weight :=
    measurable_coeCornerDeterminantWeight N K
  have hweight_top : ∀ᵐ x ∂volumeC, weight x < ∞ :=
    Filter.Eventually.of_forall (coeCornerDeterminantWeight_lt_top N K)
  rw [show coeCornerDeterminantDensityProbabilityMeasure N K =
      (coeCornerRawMass N K)⁻¹ • raw by
    rfl,
    measureReal_ennreal_smul_apply]
  rw [show raw = Measure.map M (volumeC.withDensity weight) by rfl,
    map_measureReal_apply hM hevent]
  rw [← integral_indicator_one (μ := volumeC.withDensity weight) hpre]
  rw [integral_withDensity_eq_integral_toReal_smul hweight hweight_top]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ pre
  · have hx' : complexSymmetricMatrixOfCoordinates x ∈ event := by
      simpa only [pre, M, Set.mem_preimage] using hx
    simp [Set.indicator, hx, hx', weight,
      coeCornerCoordinateProbabilityDensity,
      coeCornerRawMass, ENNReal.toReal_inv]
  · have hx' : complexSymmetricMatrixOfCoordinates x ∉ event := by
      simpa only [pre, M, Set.mem_preimage] using hx
    simp [Set.indicator, hx, hx']

/-- Integral form of the normalized determinant-density law.  This is the
function-valued companion of
`coeCornerDeterminantDensityProbabilityMeasure_real_eq_integral`; it is
pure measure bookkeeping and does not invoke the Friedman--Mello law
identification. -/
theorem integral_coeCornerDeterminantDensityProbabilityMeasure_eq_coordinates
    {N K : ℕ} (f : ConcreteMatrixState N → ℝ) (hf : Measurable f) :
    ∫ A, f A ∂(coeCornerDeterminantDensityProbabilityMeasure N K) =
      ∫ x, f (complexSymmetricMatrixOfCoordinates x) *
          coeCornerCoordinateProbabilityDensity N K x
        ∂(complexSymmetricCoordinateVolume N) := by
  let M := complexSymmetricMatrixOfCoordinates (N := N)
  let volumeC := complexSymmetricCoordinateVolume N
  let weight := coeCornerDeterminantWeight N K
  let raw := coeCornerRawDeterminantDensityMeasure N K
  let normalizer := (coeCornerRawMass N K)⁻¹
  have hM : Measurable M := measurable_complexSymmetricMatrixOfCoordinates N
  have hweight : Measurable weight :=
    measurable_coeCornerDeterminantWeight N K
  have hweight_top : ∀ᵐ x ∂volumeC, weight x < ∞ :=
    Filter.Eventually.of_forall (coeCornerDeterminantWeight_lt_top N K)
  rw [show coeCornerDeterminantDensityProbabilityMeasure N K =
      normalizer • raw by rfl,
    integral_smul_measure]
  rw [show raw = Measure.map M (volumeC.withDensity weight) by rfl,
    integral_map_of_stronglyMeasurable hM hf.stronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul hweight hweight_top]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [coeCornerCoordinateProbabilityDensity, coeCornerRawMass,
    ENNReal.toReal_inv, M, weight, normalizer]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.H3H4Central
