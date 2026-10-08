import A1.DoubledWishartDensity
import A1.DoubledCoordinateVolume

open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal
open A3Research

noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace A1Research

/-- The actual real Wishart density in the Hermitian/symmetric complex pair coordinates. -/
theorem map_doubledWishart_to_pair_density (n m : ℕ) :
    (wishartAmbientMeasure (2 * m) ℝ ((n : ℝ) / 2)).map
      (doubledRealCoordinatePairLinearEquiv m) =
        (doubledCoordinateVolumeConstant m : ℝ≥0∞) •
          (complexPairCoordinateVolume m).withDensity (doubledPairWishartDensity n m) := by
  have he : Measurable (doubledRealCoordinatePairLinearEquiv m) :=
    (doubledRealCoordinatePairLinearEquiv m).toContinuousLinearEquiv.continuous.measurable
  apply Measure.ext_of_lintegral _
  intro g hg
  rw [lintegral_map hg he, lintegral_smul_measure]
  unfold wishartAmbientMeasure
  have htest : Measurable (fun x : HermitianCoordinates (2 * m) ℝ ↦
      g (doubledRealCoordinatePairLinearEquiv m x)) := hg.comp he
  rw [lintegral_withDensity_eq_lintegral_mul _
    (measurable_wishartAmbientDensity ((n : ℝ) / 2)) htest,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_doubledPairWishartDensity n m) hg]
  exact lintegral_doubledRealCoordinatePair m
    (wishartAmbientDensity (2 * m) ℝ ((n : ℝ) / 2)) g

end A1Research
