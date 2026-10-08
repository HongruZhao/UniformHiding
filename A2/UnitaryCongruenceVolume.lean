import A2.UnitaryCongruenceAlgebra
import A2.OrbitJacobianDiagonal

open MeasureTheory Matrix
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

namespace A2Research

theorem continuous_det_unitaryCongruenceRepresentation (N : ℕ) :
    Continuous (fun U : Matrix.unitaryGroup (Fin N) ℂ ↦
      LinearMap.det (unitaryCongruenceRepresentation N U)) := by
  classical
  let b := Module.finBasis ℝ (ComplexSymmetricCoordinates N)
  have hm : Continuous (fun U : Matrix.unitaryGroup (Fin N) ℂ ↦
      LinearMap.toMatrix b b (unitaryCongruenceRepresentation N U)) := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    simp only [LinearMap.toMatrix_apply]
    exact (continuous_apply i).comp
      (b.continuous_coe_repr.comp (continuous_unitaryCongruenceRepresentation_apply N (b j)))
  have heq : (fun U : Matrix.unitaryGroup (Fin N) ℂ ↦
      LinearMap.det (unitaryCongruenceRepresentation N U)) =
      fun U ↦ (LinearMap.toMatrix b b (unitaryCongruenceRepresentation N U)).det := by
    funext U
    exact (LinearMap.det_toMatrix b _).symm
  rw [heq]
  exact hm.matrix_det

/-- The full real determinant of the actual unitary congruence action has
absolute value one, independently of the chosen real basis. -/
theorem abs_det_unitaryCongruenceRepresentation (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    |LinearMap.det (unitaryCongruenceRepresentation N U)| = 1 :=
  abs_eq_one_compact_character (LinearMap.det.comp (unitaryCongruenceRepresentation N))
    (continuous_det_unitaryCongruenceRepresentation N) U

/-- Unitary congruence preserves the exact independent-coordinate volume. -/
theorem measurePreserving_unitaryCongruenceRepresentation (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    MeasurePreserving (unitaryCongruenceRepresentation N U)
      (complexSymmetricCoordinateVolume N) (complexSymmetricCoordinateVolume N) := by
  letI : (complexSymmetricCoordinateVolume N).IsAddHaarMeasure := by
    change (volume : Measure (ComplexSymmetricCoordinates N)).IsAddHaarMeasure
    infer_instance
  have habs := abs_det_unitaryCongruenceRepresentation N U
  have hd : LinearMap.det (unitaryCongruenceRepresentation N U) ≠ 0 := by
    intro h
    exact zero_ne_one (by simpa only [h, abs_zero] using habs)
  refine ⟨(unitaryCongruenceRepresentation N U).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
    (complexSymmetricCoordinateVolume N) hd]
  simp only [abs_inv, habs, inv_one, ENNReal.ofReal_one, one_smul]

def realCoordinateCongruenceLinearMap (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    TakagiRealCoordinates N →ₗ[ℝ] TakagiRealCoordinates N :=
  (takagiRealComplexCoordinatesEquiv N).symm.toLinearMap.comp
    ((unitaryCongruenceRepresentation N U).comp (takagiRealComplexCoordinatesEquiv N).toLinearMap)

/-- The same exact determinant in the chart's literal real coordinates. -/
theorem abs_det_realCoordinateCongruenceLinearMap (N : ℕ)
    (U : Matrix.unitaryGroup (Fin N) ℂ) :
    |LinearMap.det (realCoordinateCongruenceLinearMap N U)| = 1 := by
  have heq := LinearMap.det_conj (unitaryCongruenceRepresentation N U)
    (takagiRealComplexCoordinatesEquiv N).symm
  simp only [LinearEquiv.symm_symm] at heq
  rw [realCoordinateCongruenceLinearMap, heq]
  exact abs_det_unitaryCongruenceRepresentation N U

end A2Research
