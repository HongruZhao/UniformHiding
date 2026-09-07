import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CoordinateGeometry
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16MeasureTransport
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Tactic

/-!
# H16: coordinate Jacobian to moving common-ambient density

This module proves every measure-theoretic consequence of the one remaining
finite-dimensional identity: the centered congruence coordinate map has
absolute real determinant one.  The identity itself is named as a proposition,
not assumed as an axiom.
-/

open MeasureTheory
open scoped ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- The complex-linear centered coordinate flow, restricted to real scalars
and bundled continuously using finite dimensionality. -/
def centeredTransposeCongruenceFlowCoordinateRealCLE {N : ℕ}
    (v : ComplexUnitSphere N) (t : ℝ) :
    ComplexSymmetricCoordinates N ≃L[ℝ] ComplexSymmetricCoordinates N :=
  ((centeredTransposeCongruenceFlowCoordinateLinearEquiv v t).restrictScalars
    ℝ).toContinuousLinearEquiv

@[simp]
theorem centeredTransposeCongruenceFlowCoordinateRealCLE_apply
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    centeredTransposeCongruenceFlowCoordinateRealCLE v t x =
      transposeCongruenceFlowCoordinates
        (concreteCenteredOrbitalDirection N v) t x :=
  rfl

/-- The complex determinant-one statement for the centered flow.  This is the
smallest finite-dimensional identity left after transporting congruence to
independent symmetric coordinates. -/
abbrev H16CenteredCoordinateComplexJacobianOne {N : ℕ}
    (v : ComplexUnitSphere N) (t : ℝ) : Prop :=
  LinearMap.det
      (centeredTransposeCongruenceFlowCoordinateLinearEquiv v t).toLinearMap = 1

/-- The corresponding absolute real determinant-one statement. -/
abbrev H16CenteredCoordinateJacobianOne {N : ℕ}
    (v : ComplexUnitSphere N) (t : ℝ) : Prop :=
  |LinearMap.det
      (centeredTransposeCongruenceFlowCoordinateRealCLE v t).toLinearMap| = 1

/-- Restriction of scalars turns the real determinant into the complex algebra
norm.  Consequently complex determinant one is sufficient for the exact real
Jacobian needed by the measure-transport argument. -/
theorem h16_centeredCoordinate_jacobianOne_of_complex
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (hcomplex : H16CenteredCoordinateComplexJacobianOne v t) :
    H16CenteredCoordinateJacobianOne v t := by
  unfold H16CenteredCoordinateJacobianOne
  change
    |LinearMap.det
        ((centeredTransposeCongruenceFlowCoordinateLinearEquiv v t).toLinearMap.restrictScalars
          ℝ)| = 1
  rw [LinearMap.det_restrictScalars, hcomplex]
  simp [Algebra.norm_complex_apply]

/-- Jacobian one gives preservation of flat independent complex-symmetric
coordinate volume. -/
theorem h16_centeredCoordinate_measurePreserving_of_jacobianOne
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (hjac : H16CenteredCoordinateJacobianOne v t) :
    MeasurePreserving
      (centeredTransposeCongruenceFlowCoordinateRealCLE v t)
      (complexSymmetricCoordinateVolume N)
      (complexSymmetricCoordinateVolume N) := by
  have hvol : complexSymmetricCoordinateVolume N =
      (volume : Measure (ComplexSymmetricCoordinates N)) := by
    unfold complexSymmetricCoordinateVolume
    exact MeasureTheory.volume_pi.symm
  rw [hvol]
  let e := centeredTransposeCongruenceFlowCoordinateRealCLE v t
  have hdet : |LinearMap.det e.toLinearMap| = 1 := by
    simpa only [e] using hjac
  have hdet_ne : LinearMap.det e.toLinearMap ≠ 0 := by
    intro hzero
    simp [hzero] at hdet
  refine ⟨e.continuous.measurable, ?_⟩
  change Measure.map e.toLinearMap volume = volume
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet_ne]
  rw [abs_inv, hdet]
  simp

/-- The paper scaling intertwines the coordinate flow and the matrix flow. -/
theorem h16_centeredFlow_scaledCoordinateEmbedding
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    transposeCongruenceFlow
        (concreteCenteredOrbitalDirection N v) t
        (h16ScaledSymmetricCoordinateEmbedding N K x) =
      h16ScaledSymmetricCoordinateEmbedding N K
        (centeredTransposeCongruenceFlowCoordinateRealCLE v t x) := by
  unfold h16ScaledSymmetricCoordinateEmbedding h16ScaleCOECorner
  rw [centeredTransposeCongruenceFlowCoordinateRealCLE_apply]
  rw [transposeCongruenceFlowCoordinates_matrix]
  unfold transposeCongruenceFlow
  rw [transposeCongruence_smul]

/-- Jacobian one therefore preserves the flat scaled symmetric-coordinate
measure on the full matrix ambient space. -/
theorem h16_scaledCoordinateVolume_invariant_of_jacobianOne
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (hjac : H16CenteredCoordinateJacobianOne v t) :
    Measure.map
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t)
        (h16ScaledSymmetricCoordinateVolume N K) =
      h16ScaledSymmetricCoordinateVolume N K := by
  let e := centeredTransposeCongruenceFlowCoordinateRealCLE v t
  have he : Measurable e := e.continuous.measurable
  have hcoord : Measure.map e (complexSymmetricCoordinateVolume N) =
      complexSymmetricCoordinateVolume N :=
    (h16_centeredCoordinate_measurePreserving_of_jacobianOne v t hjac).map_eq
  have hflow : Measurable
      (transposeCongruenceFlow
        (concreteCenteredOrbitalDirection N v) t) := by
    exact measurable_transposeCongruence _
  unfold h16ScaledSymmetricCoordinateVolume
  rw [Measure.map_map hflow
    (measurable_h16ScaledSymmetricCoordinateEmbedding N K)]
  have hintertwine :
      transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t ∘
          h16ScaledSymmetricCoordinateEmbedding N K =
        h16ScaledSymmetricCoordinateEmbedding N K ∘ e := by
    funext x
    exact h16_centeredFlow_scaledCoordinateEmbedding v t x
  rw [hintertwine]
  rw [← Measure.map_map
    (measurable_h16ScaledSymmetricCoordinateEmbedding N K) he]
  rw [hcoord]

/-- The same one Jacobian identity preserves the normalized common ambient
measure. -/
theorem h16_scaledDeterminantAmbient_invariant_of_jacobianOne
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (hjac : H16CenteredCoordinateJacobianOne v t) :
    Measure.map
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t)
        (h16ScaledDeterminantAmbient N K) =
      h16ScaledDeterminantAmbient N K :=
  h16ScaledDeterminantAmbient_invariant_of_coordinateVolume v t
    (h16_scaledCoordinateVolume_invariant_of_jacobianOne v t hjac)

/-- Exact H5 and the one coordinate-Jacobian proposition imply the complete
all-time event-free moving density identity. -/
theorem h16_map_scaledLaw_eq_commonAmbient_movingDensity_of_exactH5_and_jacobianOne
    (hH5 : H16AmbientExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (t : ℝ)
    (hjac : H16CenteredCoordinateJacobianOne v t) :
    Measure.map
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      (h16ScaledDeterminantAmbient N K).withDensity
        (fun A ↦
          (h16CenteredInverseZeroExtendedDeterminantWeight K v t A :
            ℝ≥0∞)) :=
  h16_map_scaledLaw_eq_commonAmbient_movingDensity_of_exactH5
    hH5 hN hboundary v t
      (h16_scaledDeterminantAmbient_invariant_of_jacobianOne v t hjac)

/-- Fully assembled moving-density law with only the complex determinant-one
identity left as a finite-dimensional premise. -/
theorem h16_map_scaledLaw_eq_commonAmbient_movingDensity_of_exactH5_and_complexJacobianOne
    (hH5 : H16AmbientExactH5Family) {N K : ℕ}
    (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (v : ComplexUnitSphere N) (t : ℝ)
    (hcomplex : H16CenteredCoordinateComplexJacobianOne v t) :
    Measure.map
        (transposeCongruenceFlow
          (concreteCenteredOrbitalDirection N v) t)
        (concreteScaledCOECornerLaw
          canonicalUnitaryHaarProbabilityFamily N K) =
      (h16ScaledDeterminantAmbient N K).withDensity
        (fun A ↦
          (h16CenteredInverseZeroExtendedDeterminantWeight K v t A :
            ℝ≥0∞)) :=
  h16_map_scaledLaw_eq_commonAmbient_movingDensity_of_exactH5_and_jacobianOne
    hH5 hN hboundary v t
      (h16_centeredCoordinate_jacobianOne_of_complex v t hcomplex)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
