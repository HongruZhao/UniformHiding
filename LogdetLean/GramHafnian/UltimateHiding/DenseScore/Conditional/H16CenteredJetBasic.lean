import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16BoundaryExponentFour
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredWeakGeneratorInterface
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CoordinateVolume

/-!
# H16 literal centered-jet transport identities

This module proves the definition-level support, flow, and density identities
surrounding the determinant-boundary analysis.  The only Jacobian statement
is explicitly conditional on the independent complex-coordinate determinant
identity.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

@[simp]
theorem h16CenteredCoordinateFlow_zero
    {N : ℕ} (v : ComplexUnitSphere N)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredCoordinateFlow v 0 x = x := by
  exact transposeCongruenceFlowCoordinates_zero _ x

theorem h16CenteredCoordinateFlow_add
    {N : ℕ} (v : ComplexUnitSphere N) (s t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredCoordinateFlow v (s + t) x =
      h16CenteredCoordinateFlow v s
        (h16CenteredCoordinateFlow v t x) := by
  exact transposeCongruenceFlowCoordinates_add_time _ s t x

@[simp]
theorem h16CenteredCoordinateFlow_neg_left
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredCoordinateFlow v (-t)
        (h16CenteredCoordinateFlow v t x) = x := by
  exact transposeCongruenceFlowCoordinates_neg_left _ t x

@[simp]
theorem h16CenteredCoordinateFlow_neg_right
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredCoordinateFlow v t
        (h16CenteredCoordinateFlow v (-t) x) = x := by
  exact transposeCongruenceFlowCoordinates_neg_right _ t x

theorem h16CenteredCoordinateFlow_measurePreserving_of_complexJacobianOne
    {N : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (hjac : H16CenteredCoordinateComplexJacobianOne v t) :
    MeasurePreserving
      (h16CenteredCoordinateFlow v t)
      (complexSymmetricCoordinateVolume N)
      (complexSymmetricCoordinateVolume N) := by
  change MeasurePreserving
    (centeredTransposeCongruenceFlowCoordinateRealCLE v t)
    (complexSymmetricCoordinateVolume N)
    (complexSymmetricCoordinateVolume N)
  exact h16_centeredCoordinate_measurePreserving_of_jacobianOne v t
    (h16_centeredCoordinate_jacobianOne_of_complex v t hjac)

theorem h16CenteredTransportJet_zero_off_support
    {N K : ℕ} (r : Fin 5) (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N)
    (hx : x ∉ h16CenteredTransportSupport v t) :
    h16CenteredTransportJet N K r v t x = 0 := by
  simp [h16CenteredTransportJet, hx]

theorem h16CenteredTransportJet_zero_eq_probabilityDensity
    {N K : ℕ} (v : ComplexUnitSphere N) (t : ℝ)
    (x : ComplexSymmetricCoordinates N) :
    h16CenteredTransportJet N K 0 v t x =
      h16COECoordinateProbabilityDensity N K
        (h16CenteredCoordinateFlow v (-t) x) := by
  classical
  by_cases hx : x ∈ h16CenteredTransportSupport v t
  · have hsupp : coeCornerSupport
        (complexSymmetricMatrixOfCoordinates
          (h16CenteredCoordinateFlow v (-t) x)) := by
      simpa [h16CenteredTransportSupport] using hx
    let C := complexSymmetricMatrixOfCoordinates
      (h16CenteredCoordinateFlow v (-t) x)
    have hC : coeCornerSupport C := by
      simpa [C] using hsupp
    have hbase : 0 ≤
        (Matrix.det (1 - C.conjTranspose * C)).re :=
      (RCLike.lt_iff_re_im.mp hC.det_pos).1.le
    have hpow : 0 ≤ Real.rpow
        (Matrix.det (1 - C.conjTranspose * C)).re
        (coeCornerDensityExponent N K) :=
      Real.rpow_nonneg hbase _
    have htoReal :
        (ENNReal.ofReal (Real.rpow
          (Matrix.det (1 - C.conjTranspose * C)).re
          (coeCornerDensityExponent N K))).toReal =
          Real.rpow (Matrix.det (1 - C.conjTranspose * C)).re
            (coeCornerDensityExponent N K) :=
      ENNReal.toReal_ofReal hpow
    have hweight :
        (coeCornerDeterminantWeight N K
          (h16CenteredCoordinateFlow v (-t) x)).toReal =
          Real.rpow (Matrix.det (1 - C.conjTranspose * C)).re
            (coeCornerDensityExponent N K) := by
      unfold coeCornerDeterminantWeight
      dsimp only
      rw [if_pos hsupp]
      simpa [C] using htoReal
    simp [h16CenteredTransportJet, hx, iteratedDeriv_zero,
      h16CenteredTransportInteriorDensity,
      h16CenteredTransportGapDeterminant,
      h16COECoordinateProbabilityDensity,
      hweight, C]
  · have hsupp : ¬ coeCornerSupport
        (complexSymmetricMatrixOfCoordinates
          (h16CenteredCoordinateFlow v (-t) x)) := by
      simpa [h16CenteredTransportSupport] using hx
    simp [h16CenteredTransportJet, hx,
      h16COECoordinateProbabilityDensity,
      coeCornerDeterminantWeight, hsupp]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
