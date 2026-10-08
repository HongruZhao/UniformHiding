import A1.SymmetricCongruenceJacobian

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder ENNReal
open Matrix MeasureTheory Set
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace A1Research

theorem symmetricRealCongruenceLinearMap_one (m : ℕ) :
    symmetricRealCongruenceLinearMap (1 : Matrix (Fin m) (Fin m) ℂ) = 1 := by
  apply LinearMap.ext
  intro x
  change A2Research.symmetricCongruenceLinearMap (1 : Matrix (Fin m) (Fin m) ℂ) x = x
  rw [A2Research.symmetricCongruenceLinearMap_one]
  rfl

def symmetricRealCongruenceLinearEquiv {m : ℕ}
    (C : Matrix (Fin m) (Fin m) ℂ) (hC : IsUnit C) :
    ComplexSymmetricCoordinates m ≃ₗ[ℝ] ComplexSymmetricCoordinates m where
  toLinearMap := symmetricRealCongruenceLinearMap C
  invFun := symmetricRealCongruenceLinearMap C⁻¹
  left_inv := by
    intro x
    change (symmetricRealCongruenceLinearMap C⁻¹ * symmetricRealCongruenceLinearMap C) x = x
    rw [← symmetricRealCongruenceLinearMap_mul,
      Matrix.nonsing_inv_mul C ((Matrix.isUnit_iff_isUnit_det C).mp hC),
      symmetricRealCongruenceLinearMap_one]
    rfl
  right_inv := by
    intro x
    change (symmetricRealCongruenceLinearMap C * symmetricRealCongruenceLinearMap C⁻¹) x = x
    rw [← symmetricRealCongruenceLinearMap_mul,
      Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hC),
      symmetricRealCongruenceLinearMap_one]
    rfl

theorem measurableEmbedding_symmetricRealCongruence {m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUnit C) :
    MeasurableEmbedding (symmetricRealCongruenceLinearMap C) :=
  (symmetricRealCongruenceLinearEquiv C hC).toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding

theorem det_symmetricRealCongruence_ne_zero {m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUnit C) :
    LinearMap.det (symmetricRealCongruenceLinearMap C) ≠ 0 := by
  have he : symmetricRealCongruenceLinearMap C * symmetricRealCongruenceLinearMap C⁻¹ = 1 := by
    rw [← symmetricRealCongruenceLinearMap_mul,
      Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hC),
      symmetricRealCongruenceLinearMap_one]
  have hd := congrArg LinearMap.det he
  simp only [map_mul, map_one] at hd
  intro hz
  simp only [hz, zero_mul, zero_ne_one] at hd

theorem map_symmetricRealCongruence_volume {m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUnit C) :
    Measure.map (symmetricRealCongruenceLinearMap C) (complexSymmetricCoordinateVolume m) =
      ENNReal.ofReal |(LinearMap.det (symmetricRealCongruenceLinearMap C))⁻¹| •
        complexSymmetricCoordinateVolume m := by
  letI : (complexSymmetricCoordinateVolume m).IsAddHaarMeasure := by
    change (volume : Measure (ComplexSymmetricCoordinates m)).IsAddHaarMeasure
    infer_instance
  exact Measure.map_linearMap_addHaar_eq_smul_addHaar _
    (det_symmetricRealCongruence_ne_zero hC)

/-- Exact fixed-covariance change of variables, for any nonnegative test. -/
theorem lintegral_symmetricRealCongruence {m : ℕ}
    {C : Matrix (Fin m) (Fin m) ℂ} (hC : IsUnit C)
    (f : ComplexSymmetricCoordinates m → ℝ≥0∞) :
    ∫⁻ x, f x ∂(complexSymmetricCoordinateVolume m) =
      ∫⁻ x, ENNReal.ofReal |LinearMap.det (symmetricRealCongruenceLinearMap C)| *
        f (symmetricRealCongruenceLinearMap C x) ∂(complexSymmetricCoordinateVolume m) := by
  let J : ℝ := |LinearMap.det (symmetricRealCongruenceLinearMap C)|
  have hJ : 0 < J := abs_pos.mpr (det_symmetricRealCongruence_ne_zero hC)
  have hmeasure : ENNReal.ofReal J •
      Measure.map (symmetricRealCongruenceLinearMap C) (complexSymmetricCoordinateVolume m) =
        complexSymmetricCoordinateVolume m := by
    rw [map_symmetricRealCongruence_volume hC, smul_smul, abs_inv]
    change (ENNReal.ofReal J * ENNReal.ofReal J⁻¹) • _ = _
    rw [← ENNReal.ofReal_mul hJ.le, mul_inv_cancel₀ hJ.ne', ENNReal.ofReal_one, one_smul]
  calc
    _ = ∫⁻ x, f x ∂(ENNReal.ofReal J • Measure.map
        (symmetricRealCongruenceLinearMap C) (complexSymmetricCoordinateVolume m)) := by
      rw [hmeasure]
    _ = ENNReal.ofReal J * ∫⁻ x, f (symmetricRealCongruenceLinearMap C x)
        ∂(complexSymmetricCoordinateVolume m) := by
      rw [lintegral_smul_measure, (measurableEmbedding_symmetricRealCongruence hC).lintegral_map]
      rfl
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end A1Research
