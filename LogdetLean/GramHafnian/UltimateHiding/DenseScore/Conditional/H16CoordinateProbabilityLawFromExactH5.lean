import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16FourthRadialIntegrabilityFromExactH5
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16MeasureTransport
import Mathlib.Tactic

/-!
# The normalized coordinate determinant law from exact H5

This module identifies the scaled COE law with the pushforward of the literal
normalized determinant density on independent symmetric coordinates.  Both
finiteness and nondegeneracy of the raw normalization are derived from exact
H5 and the probability character of the concrete COE law.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- Exact H5 also excludes zero raw determinant mass. -/
theorem h16_coeCornerRawDeterminantDensityMeasure_univ_ne_zero_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    coeCornerRawDeterminantDensityMeasure N K Set.univ ≠ 0 := by
  have hprob :
      concreteUnscaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K Set.univ = 1 :=
    h16_concreteUnscaledCOECornerLaw_apply_univ (by omega)
  have heq := hH5 (n := N) (k := K) hN h2NK
  have hnormalized :
      coeCornerDeterminantDensityProbabilityMeasure N K Set.univ = 1 := by
    rw [← heq]
    exact hprob
  intro hzero
  have hmeasureZero : coeCornerRawDeterminantDensityMeasure N K = 0 :=
    Measure.measure_univ_eq_zero.mp hzero
  have hprobZero : coeCornerDeterminantDensityProbabilityMeasure N K = 0 := by
    unfold coeCornerDeterminantDensityProbabilityMeasure
    rw [hmeasureZero]
    simp
  rw [hprobZero] at hnormalized
  simp at hnormalized

theorem h16COECoordinateRawMass_ne_zero_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    h16COECoordinateRawMass N K ≠ 0 :=
  h16_coeCornerRawDeterminantDensityMeasure_univ_ne_zero_of_exactH5
    hH5 hN h2NK

theorem h16COECoordinateRawMass_ne_top_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    h16COECoordinateRawMass N K ≠ ∞ :=
  h16_coeCornerRawDeterminantDensityMeasure_univ_ne_top_of_exactH5
    hH5 hN h2NK

/-- Every literal determinant weight is finite pointwise. -/
theorem coeCornerDeterminantWeight_ne_top
    (N K : ℕ) (x : ComplexSymmetricCoordinates N) :
    coeCornerDeterminantWeight N K x ≠ ∞ := by
  classical
  unfold coeCornerDeterminantWeight
  dsimp only
  split_ifs <;> simp

/-- The normalized coordinate density as the nonnegative density expected by
`Measure.withDensity`. -/
def h16COECoordinateProbabilityWeight
    (N K : ℕ) (x : ComplexSymmetricCoordinates N) : ℝ≥0 :=
  (h16COECoordinateRawMass N K)⁻¹.toNNReal *
    (coeCornerDeterminantWeight N K x).toNNReal

theorem measurable_h16COECoordinateProbabilityWeight (N K : ℕ) :
    Measurable (h16COECoordinateProbabilityWeight N K) := by
  unfold h16COECoordinateProbabilityWeight
  exact measurable_const.mul
    (measurable_coeCornerDeterminantWeight N K).ennreal_toNNReal

/-- Its real coercion is definitionally the real probability density used by
the literal centered jets. -/
theorem h16COECoordinateProbabilityWeight_coe_real
    (N K : ℕ) (x : ComplexSymmetricCoordinates N) :
    (h16COECoordinateProbabilityWeight N K x : ℝ) =
      h16COECoordinateProbabilityDensity N K x := by
  simp [h16COECoordinateProbabilityWeight,
    h16COECoordinateProbabilityDensity,
    ENNReal.coe_toNNReal_eq_toReal]

/-- Under exact H5, its `ENNReal` coercion is exactly raw weight multiplied
by the inverse raw mass. -/
theorem h16COECoordinateProbabilityWeight_coe_ennreal_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (h2NK : 2 * N ≤ K)
    (x : ComplexSymmetricCoordinates N) :
    (h16COECoordinateProbabilityWeight N K x : ℝ≥0∞) =
      (h16COECoordinateRawMass N K)⁻¹ *
        coeCornerDeterminantWeight N K x := by
  unfold h16COECoordinateProbabilityWeight
  rw [ENNReal.coe_mul]
  rw [ENNReal.coe_toNNReal
    (ENNReal.inv_ne_top.mpr
      (h16COECoordinateRawMass_ne_zero_of_exactH5 hH5 hN h2NK))]
  rw [ENNReal.coe_toNNReal (coeCornerDeterminantWeight_ne_top N K x)]

/-- Exact H5 identifies the scaled law with the pushforward of the normalized
coordinate determinant density. -/
theorem h16_scaledLaw_eq_map_coordinateProbabilityDensity_of_exactH5
    (hH5 : H16ExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K =
      Measure.map (h16ScaledSymmetricCoordinateEmbedding N K)
        ((complexSymmetricCoordinateVolume N).withDensity
          (fun x ↦
            (h16COECoordinateProbabilityWeight N K x : ℝ≥0∞))) := by
  have hK : 0 < K := by omega
  rw [h16_scaledLaw_eq_commonAmbient_withDensity_of_exactH5
    hH5 hN h2NK]
  unfold h16ScaledDeterminantAmbient
  rw [withDensity_smul_measure]
  rw [← h16_map_scaledCoordinateDensity hK]
  rw [← Measure.map_smul]
  congr 1
  let c : ℝ≥0∞ := (h16COECoordinateRawMass N K)⁻¹
  have hfun :
      (fun x : ComplexSymmetricCoordinates N ↦
        (h16COECoordinateProbabilityWeight N K x : ℝ≥0∞)) =
      c • coeCornerDeterminantWeight N K := by
    funext x
    change (h16COECoordinateProbabilityWeight N K x : ℝ≥0∞) =
      c * coeCornerDeterminantWeight N K x
    exact h16COECoordinateProbabilityWeight_coe_ennreal_of_exactH5
      hH5 hN h2NK x
  rw [hfun, withDensity_smul c
    (measurable_coeCornerDeterminantWeight N K)]
  rfl

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
