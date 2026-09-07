import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16AmbientDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

/-!
# H16: push determinant densities to a common ambient measure

This module contains only measure geometry.  It neither assumes nor proves an
event derivative.  The generic first lemma avoids an unnecessary inverse or
measurable-embedding construction: a density already written as `W ∘ κ`
pushes through `κ` to density `W` over `map κ μ`.

The final theorem uses an exact H5 theorem parameter and proves the complete
time-zero common-ambient density identity, including the paper's `sqrt K`
scaling and the canonical normalization already present in the determinant
density definition.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-! ## Generic `map` / `withDensity` algebra -/

/-- Pushforward commutes with a density pulled back from the target.  No
injectivity hypothesis is needed. -/
theorem h16_map_withDensity_comp
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Y) (hκ : Measurable κ)
    (W : Y → ℝ≥0∞) (hW : Measurable W) :
    Measure.map κ (μ.withDensity (W ∘ κ)) =
      (Measure.map κ μ).withDensity W := by
  ext s hs
  rw [Measure.map_apply hκ hs,
    withDensity_apply _ (hs.preimage hκ), withDensity_apply _ hs,
    setLIntegral_map hs hW hκ]
  rfl

/-- Compatibility on the source is enough to push an arbitrarily named
source density to a target density. -/
theorem h16_map_withDensity_of_compat
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (κ : X → Y) (hκ : Measurable κ)
    (w : X → ℝ≥0∞) (W : Y → ℝ≥0∞) (hW : Measurable W)
    (hcompat : ∀ x, W (κ x) = w x) :
    Measure.map κ (μ.withDensity w) =
      (Measure.map κ μ).withDensity W := by
  have hw : w = W ∘ κ := by
    funext x
    exact (hcompat x).symm
  rw [hw]
  exact h16_map_withDensity_comp μ κ hκ W hW

/-- If a measurable bijective change of variables preserves the ambient
measure, it transports a density to the density composed with its inverse. -/
theorem h16_map_withDensity_inverse_of_map_eq
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (κ ι : X → X)
    (hκ : Measurable κ) (hι : Measurable ι)
    (hleft : ∀ x, ι (κ x) = x)
    (hmap : Measure.map κ μ = μ)
    (w : X → ℝ≥0∞) (hw : Measurable w) :
    Measure.map κ (μ.withDensity w) =
      μ.withDensity (w ∘ ι) := by
  calc
    Measure.map κ (μ.withDensity w) =
        (Measure.map κ μ).withDensity (w ∘ ι) :=
      h16_map_withDensity_of_compat μ κ hκ w (w ∘ ι)
        (hw.comp hι) (fun x ↦ by
          change w (ι (κ x)) = w x
          rw [hleft x])
    _ = μ.withDensity (w ∘ ι) := by rw [hmap]

/-! ## The scaled determinant weight really is the coordinate weight -/

theorem h16_scaledWeight_compat_coordinates
    {N K : ℕ} (hK : 0 < K) (x : ComplexSymmetricCoordinates N) :
    (h16ScaledZeroExtendedDeterminantWeight N K
        (h16ScaledSymmetricCoordinateEmbedding N K x) : ℝ≥0∞) =
      coeCornerDeterminantWeight N K x := by
  classical
  rw [ENNReal.coe_nnreal_eq]
  change ENNReal.ofReal
      (h16ScaledZeroExtendedDeterminantWeightReal N K
        (h16ScaledSymmetricCoordinateEmbedding N K x)) =
    coeCornerDeterminantWeight N K x
  unfold h16ScaledZeroExtendedDeterminantWeightReal
  unfold h16ScaledSymmetricCoordinateEmbedding
  rw [unscaleCOECorner_h16ScaleCOECorner hK]
  unfold h16ZeroExtendedDeterminantWeightReal
  unfold coeCornerDeterminantWeight
  dsimp only
  split_ifs <;> simp

/-- The unnormalized determinant density, after paper scaling, is a density
with respect to the single pushed flat symmetric-coordinate measure. -/
theorem h16_map_scaledCoordinateDensity
    {N K : ℕ} (hK : 0 < K) :
    Measure.map (h16ScaledSymmetricCoordinateEmbedding N K)
        ((complexSymmetricCoordinateVolume N).withDensity
          (coeCornerDeterminantWeight N K)) =
      (h16ScaledSymmetricCoordinateVolume N K).withDensity
        (fun A ↦
          (h16ScaledZeroExtendedDeterminantWeight N K A : ℝ≥0∞)) := by
  exact h16_map_withDensity_of_compat
    (complexSymmetricCoordinateVolume N)
    (h16ScaledSymmetricCoordinateEmbedding N K)
    (measurable_h16ScaledSymmetricCoordinateEmbedding N K)
    (coeCornerDeterminantWeight N K)
    (fun A ↦ (h16ScaledZeroExtendedDeterminantWeight N K A : ℝ≥0∞))
    (measurable_coe_nnreal_ennreal.comp
      (measurable_h16ScaledZeroExtendedDeterminantWeight N K))
    (h16_scaledWeight_compat_coordinates hK)

/-! ## Exact H5 gives the fully normalized scaled common-ambient density -/

/-- Put the canonical probability normalization into the ambient measure,
leaving the determinant weight itself finite-valued and nonnegative. -/
def h16ScaledDeterminantAmbient (N K : ℕ) :
    Measure (ConcreteMatrixState N) :=
  (coeCornerRawDeterminantDensityMeasure N K Set.univ)⁻¹ •
    h16ScaledSymmetricCoordinateVolume N K

/-- Exact H5, with no appeal to the project's H5 axiom, identifies the
scaled COE law with the normalized common-ambient determinant density. -/
theorem h16_scaledLaw_eq_commonAmbient_withDensity_of_exactH5
    (hH5 : H16AmbientExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (h2NK : 2 * N ≤ K) :
    concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K =
      (h16ScaledDeterminantAmbient N K).withDensity
        (fun A ↦
          (h16ScaledZeroExtendedDeterminantWeight N K A : ℝ≥0∞)) := by
  have hK : 0 < K := by omega
  have hrecover :
      Measure.map (h16ScaleCOECorner (N := N) K)
          (concreteUnscaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) =
        concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K := by
    unfold concreteUnscaledCOECornerLaw
    rw [Measure.map_map (measurable_h16ScaleCOECorner N K)
      (measurable_unscaleCOECorner N K)]
    have hcomp :
        h16ScaleCOECorner (N := N) K ∘ unscaleCOECorner K = id := by
      funext A
      exact h16ScaleCOECorner_unscaleCOECorner hK A
    rw [hcomp, Measure.map_id]
  calc
    concreteScaledCOECornerLaw
        canonicalUnitaryHaarProbabilityFamily N K =
        Measure.map (h16ScaleCOECorner (N := N) K)
          (concreteUnscaledCOECornerLaw
            canonicalUnitaryHaarProbabilityFamily N K) := hrecover.symm
    _ = Measure.map (h16ScaleCOECorner (N := N) K)
          (coeCornerDeterminantDensityProbabilityMeasure N K) := by
      rw [hH5 (n := N) (k := K) hN h2NK]
    _ = (h16ScaledDeterminantAmbient N K).withDensity
          (fun A ↦
            (h16ScaledZeroExtendedDeterminantWeight N K A : ℝ≥0∞)) := by
      unfold coeCornerDeterminantDensityProbabilityMeasure
      unfold coeCornerRawDeterminantDensityMeasure
      unfold h16ScaledDeterminantAmbient
      unfold h16ScaledSymmetricCoordinateVolume
      rw [Measure.map_smul]
      rw [Measure.map_map (measurable_h16ScaleCOECorner N K)
        (measurable_complexSymmetricMatrixOfCoordinates N)]
      change
        (Measure.map (complexSymmetricMatrixOfCoordinates (N := N))
              ((complexSymmetricCoordinateVolume N).withDensity
                (coeCornerDeterminantWeight N K)) Set.univ)⁻¹ •
            Measure.map (h16ScaledSymmetricCoordinateEmbedding N K)
              ((complexSymmetricCoordinateVolume N).withDensity
                (coeCornerDeterminantWeight N K)) =
          (((Measure.map (complexSymmetricMatrixOfCoordinates (N := N))
                ((complexSymmetricCoordinateVolume N).withDensity
                  (coeCornerDeterminantWeight N K)) Set.univ)⁻¹ •
              Measure.map (h16ScaledSymmetricCoordinateEmbedding N K)
                (complexSymmetricCoordinateVolume N)).withDensity
            (fun A ↦
              (h16ScaledZeroExtendedDeterminantWeight N K A : ℝ≥0∞)))
      rw [h16_map_scaledCoordinateDensity hK]
      rw [withDensity_smul_measure]
      rfl

/-! ## All moving-measure algebra after the one Jacobian lemma -/

/-- Preservation of the unnormalized flat scaled coordinate measure implies
preservation of the canonically normalized common ambient measure. -/
theorem h16ScaledDeterminantAmbient_invariant_of_coordinateVolume
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (hvolume :
      Measure.map
          (transposeCongruenceFlow
            (concreteCenteredOrbitalDirection N v) t)
          (h16ScaledSymmetricCoordinateVolume N K) =
        h16ScaledSymmetricCoordinateVolume N K) :
    Measure.map
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t)
        (h16ScaledDeterminantAmbient N K) =
      h16ScaledDeterminantAmbient N K := by
  unfold h16ScaledDeterminantAmbient
  rw [Measure.map_smul, hvolume]

/-- Once centered congruence is known to preserve the explicit common
ambient measure, pushing the time-zero determinant density gives exactly the
inverse-flow zero-extended density. -/
theorem h16_map_commonAmbientDensity_centered_of_invariant
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (hinvariant :
      Measure.map
          (transposeCongruenceFlow
            (concreteCenteredOrbitalDirection N v) t)
          (h16ScaledDeterminantAmbient N K) =
        h16ScaledDeterminantAmbient N K) :
    Measure.map
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t)
        ((h16ScaledDeterminantAmbient N K).withDensity
          (fun A ↦
            (h16ScaledZeroExtendedDeterminantWeight N K A : ℝ≥0∞))) =
      (h16ScaledDeterminantAmbient N K).withDensity
        (fun A ↦
          (h16CenteredInverseZeroExtendedDeterminantWeight K v t A :
            ℝ≥0∞)) := by
  calc
    Measure.map
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t)
        ((h16ScaledDeterminantAmbient N K).withDensity
          (fun A ↦
            (h16ScaledZeroExtendedDeterminantWeight N K A : ℝ≥0∞))) =
        (Measure.map
          (transposeCongruenceFlow
            (concreteCenteredOrbitalDirection N v) t)
          (h16ScaledDeterminantAmbient N K)).withDensity
            (fun A ↦
              (h16CenteredInverseZeroExtendedDeterminantWeight K v t A :
                ℝ≥0∞)) := by
      apply h16_map_withDensity_of_compat
      · exact measurable_transposeCongruence _
      · exact measurable_coe_nnreal_ennreal.comp
          (measurable_h16CenteredInverseZeroExtendedDeterminantWeight v t)
      · intro A
        exact congrArg (fun z : ℝ≥0 ↦ (z : ℝ≥0∞))
          (h16CenteredInverseZeroExtendedDeterminantWeight_flow v t A)
    _ = (h16ScaledDeterminantAmbient N K).withDensity
          (fun A ↦
            (h16CenteredInverseZeroExtendedDeterminantWeight K v t A :
              ℝ≥0∞)) := by rw [hinvariant]

/-- Exact H5 plus the single common-ambient invariance lemma yields the full
event-free moving-law density identity. -/
theorem h16_map_scaledLaw_eq_commonAmbient_movingDensity_of_exactH5
    (hH5 : H16AmbientExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (t : ℝ)
    (hinvariant :
      Measure.map
          (transposeCongruenceFlow
            (concreteCenteredOrbitalDirection N v) t)
          (h16ScaledDeterminantAmbient N K) =
        h16ScaledDeterminantAmbient N K) :
    Measure.map
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      (h16ScaledDeterminantAmbient N K).withDensity
        (fun A ↦
          (h16CenteredInverseZeroExtendedDeterminantWeight K v t A :
            ℝ≥0∞)) := by
  rw [h16_scaledLaw_eq_commonAmbient_withDensity_of_exactH5
    hH5 hN (by omega : 2 * N ≤ K)]
  exact h16_map_commonAmbientDensity_centered_of_invariant v t hinvariant

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
