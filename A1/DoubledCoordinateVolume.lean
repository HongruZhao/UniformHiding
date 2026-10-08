import A1.DoubledRealCoordinateEquiv
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal
open A3Research
open LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace A1Research

def complexPairCoordinateVolume (m : ℕ) :
    Measure (HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m) :=
  (hermitianCoordinateVolume m ℂ).prod (complexSymmetricCoordinateVolume m)

instance complexPairCoordinateVolume_isAddHaar (m : ℕ) :
    IsAddHaarMeasure (complexPairCoordinateVolume m) := by
  letI : IsAddHaarMeasure (hermitianCoordinateVolume m ℂ) := by
    unfold hermitianCoordinateVolume
    exact prod.instIsAddHaarMeasure _ _
  letI : IsAddHaarMeasure (complexSymmetricCoordinateVolume m) := by
    change IsAddHaarMeasure (volume : Measure (ComplexSymmetricCoordinates m))
    infer_instance
  unfold complexPairCoordinateVolume
  exact prod.instIsAddHaarMeasure _ _

instance doubledRealCoordinateVolume_isAddHaar (m : ℕ) :
    IsAddHaarMeasure (hermitianCoordinateVolume (2 * m) ℝ) := by
  unfold hermitianCoordinateVolume
  exact prod.instIsAddHaarMeasure _ _

instance mappedDoubledRealCoordinateVolume_isAddHaar (m : ℕ) :
    IsAddHaarMeasure (Measure.map (doubledRealCoordinatePairLinearEquiv m)
      (hermitianCoordinateVolume (2 * m) ℝ)) :=
  (doubledRealCoordinatePairLinearEquiv m).toContinuousLinearEquiv.isAddHaarMeasure_map _

def doubledCoordinateVolumeConstant (m : ℕ) : ℝ≥0 :=
  addHaarScalarFactor
    (Measure.map (doubledRealCoordinatePairLinearEquiv m)
      (hermitianCoordinateVolume (2 * m) ℝ))
    (complexPairCoordinateVolume m)

theorem doubledCoordinateVolumeConstant_pos (m : ℕ) :
    0 < doubledCoordinateVolumeConstant m := by
  unfold doubledCoordinateVolumeConstant
  letI : IsAddHaarMeasure (Measure.map (doubledRealCoordinatePairLinearEquiv m)
      (hermitianCoordinateVolume (2 * m) ℝ)) :=
    (doubledRealCoordinatePairLinearEquiv m).toContinuousLinearEquiv.isAddHaarMeasure_map _
  exact addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

/-- The genuine linear coordinate change preserves flat volume up to a positive finite scalar. -/
theorem map_doubledRealCoordinatePair_volume (m : ℕ) :
    Measure.map (doubledRealCoordinatePairLinearEquiv m)
      (hermitianCoordinateVolume (2 * m) ℝ) =
        doubledCoordinateVolumeConstant m • complexPairCoordinateVolume m := by
  letI : IsAddHaarMeasure (Measure.map (doubledRealCoordinatePairLinearEquiv m)
      (hermitianCoordinateVolume (2 * m) ℝ)) :=
    (doubledRealCoordinatePairLinearEquiv m).toContinuousLinearEquiv.isAddHaarMeasure_map _
  exact isAddLeftInvariant_eq_smul
    (Measure.map (doubledRealCoordinatePairLinearEquiv m)
      (hermitianCoordinateVolume (2 * m) ℝ)) (complexPairCoordinateVolume m)

theorem measurableEmbedding_doubledRealCoordinatePair (m : ℕ) :
    MeasurableEmbedding (doubledRealCoordinatePairLinearEquiv m) :=
  (doubledRealCoordinatePairLinearEquiv m).toContinuousLinearEquiv.toHomeomorph.isClosedEmbedding.measurableEmbedding

/-- Literal doubled Gaussian-Gram coordinate substitution; no integrand regularity is assumed. -/
theorem lintegral_doubledRealCoordinatePair (m : ℕ)
    (f : HermitianCoordinates (2 * m) ℝ → ℝ≥0∞)
    (g : HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m → ℝ≥0∞) :
    ∫⁻ x, f x * g (doubledRealCoordinatePairLinearEquiv m x)
        ∂(hermitianCoordinateVolume (2 * m) ℝ) =
      (doubledCoordinateVolumeConstant m : ℝ≥0∞) *
        ∫⁻ y, f ((doubledRealCoordinatePairLinearEquiv m).symm y) * g y
          ∂(complexPairCoordinateVolume m) := by
  calc
    _ = ∫⁻ y, f ((doubledRealCoordinatePairLinearEquiv m).symm y) * g y
        ∂(Measure.map (doubledRealCoordinatePairLinearEquiv m)
          (hermitianCoordinateVolume (2 * m) ℝ)) := by
      rw [(measurableEmbedding_doubledRealCoordinatePair m).lintegral_map]
      simp only [LinearEquiv.symm_apply_apply]
    _ = _ := by
      rw [map_doubledRealCoordinatePair_volume, lintegral_smul_measure]
      rfl

end A1Research
