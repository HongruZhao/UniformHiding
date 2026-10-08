import A1.DoubledWishartDensity
import A1.DoubledCoordinateVolume
import Mathlib.MeasureTheory.Integral.Prod

open Matrix MeasureTheory Measure Set
open A3Research
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section
namespace A1Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem lintegral_doubledPairWishartDensity_fiber (n m : ℕ)
    (t : HermitianCoordinates m ℂ) (f : ComplexSymmetricCoordinates m → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ z, doubledPairWishartDensity n m (t, z) * f (normalizedComplexPairCoordinates (t, z))
        ∂(complexSymmetricCoordinateVolume m) =
      ENNReal.ofReal (doubledWishartKernelConstant n m) *
        wishartAmbientDensity m ℂ n t *
          ∫⁻ c, FriedmanMelloA1.determinantWeight n m c * f c
            ∂(complexSymmetricCoordinateVolume m) := by
  classical
  by_cases ht : (hermitianMatrixOfCoordinates t).PosDef
  · have hL := (A3Research.posDef_cfc_sqrt ht).transpose.isUnit
    rw [lintegral_symmetricRealCongruence hL]
    calc
      _ = ∫⁻ c, (ENNReal.ofReal (doubledWishartKernelConstant n m) *
          wishartAmbientDensity m ℂ n t) *
            (FriedmanMelloA1.determinantWeight n m c * f c)
            ∂(complexSymmetricCoordinateVolume m) := by
        apply lintegral_congr
        intro c
        change ENNReal.ofReal |LinearMap.det (symmetricRealCongruenceLinearMap
            (CFC.sqrt (hermitianMatrixOfCoordinates t)).transpose)| *
          (doubledPairWishartDensity n m (complexPairScaledCoordinates t c) *
            f (normalizedComplexPairCoordinates (complexPairScaledCoordinates t c))) = _
        rw [← mul_assoc, doubledPairWishartDensity_mul_jacobian ht c,
          normalizedComplexPairCoordinates_scaled ht c, mul_assoc]
      _ = _ := lintegral_const_mul _ ((measurable_determinantWeight n m).mul hf)
  · simp only [doubledPairWishartDensity_eq_zero_of_not_posDef ht,
      zero_mul, lintegral_zero, wishartAmbientDensity, if_neg ht, mul_zero]

theorem lintegral_doubledPairWishartDensity_stat (n m : ℕ)
    (f : ComplexSymmetricCoordinates m → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p, doubledPairWishartDensity n m p * f (normalizedComplexPairCoordinates p)
        ∂(complexPairCoordinateVolume m) =
      ENNReal.ofReal (doubledWishartKernelConstant n m) *
        (wishartAmbientMeasure m ℂ n Set.univ) *
          ∫⁻ c, FriedmanMelloA1.determinantWeight n m c * f c
            ∂(complexSymmetricCoordinateVolume m) := by
  letI : SigmaFinite (complexSymmetricCoordinateVolume m) := by
    change SigmaFinite (volume : Measure (ComplexSymmetricCoordinates m))
    infer_instance
  have hm : Measurable (fun p : HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m ↦
      doubledPairWishartDensity n m p * f (normalizedComplexPairCoordinates p)) :=
    (measurable_doubledPairWishartDensity n m).mul
      (hf.comp (measurable_normalizedComplexPairCoordinates m))
  unfold complexPairCoordinateVolume
  rw [lintegral_prod _ hm.aemeasurable]
  simp_rw [lintegral_doubledPairWishartDensity_fiber n m _ f hf]
  simp_rw [mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_mul_const _ (measurable_wishartAmbientDensity (n := m) (K := ℂ) n)]
  have hmass : (∫⁻ t, wishartAmbientDensity m ℂ n t ∂(hermitianCoordinateVolume m ℂ)) =
      wishartAmbientMeasure m ℂ n Set.univ := by
    rw [wishartAmbientMeasure, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
  rw [hmass, ← mul_assoc]

def doubledWishartMarginalConstant (n m : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (doubledWishartKernelConstant n m) * wishartAmbientMeasure m ℂ n Set.univ

theorem map_normalizedComplexPair_doubledDensity (n m : ℕ) :
    ((complexPairCoordinateVolume m).withDensity (doubledPairWishartDensity n m)).map
        normalizedComplexPairCoordinates =
      doubledWishartMarginalConstant n m •
        (complexSymmetricCoordinateVolume m).withDensity (FriedmanMelloA1.determinantWeight n m) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_normalizedComplexPairCoordinates m) hs,
    Measure.smul_apply, smul_eq_mul]
  let f : ComplexSymmetricCoordinates m → ℝ≥0∞ := s.indicator (fun _ ↦ 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hl := lintegral_doubledPairWishartDensity_stat n m f hf
  have hleft : ((complexPairCoordinateVolume m).withDensity
      (doubledPairWishartDensity n m)) (normalizedComplexPairCoordinates ⁻¹' s) =
        ∫⁻ p, doubledPairWishartDensity n m p * f (normalizedComplexPairCoordinates p)
          ∂(complexPairCoordinateVolume m) := by
    rw [withDensity_apply _ ((measurable_normalizedComplexPairCoordinates m) hs),
      ← lintegral_indicator ((measurable_normalizedComplexPairCoordinates m) hs)]
    apply lintegral_congr
    intro p
    by_cases hp : normalizedComplexPairCoordinates p ∈ s <;>
      simp [f, hp]
  have hright : ((complexSymmetricCoordinateVolume m).withDensity
      (FriedmanMelloA1.determinantWeight n m)) s =
        ∫⁻ c, FriedmanMelloA1.determinantWeight n m c * f c
          ∂(complexSymmetricCoordinateVolume m) := by
    rw [withDensity_apply _ hs, ← lintegral_indicator hs]
    apply lintegral_congr
    intro c
    by_cases hc : c ∈ s <;> simp [f, hc]
  rw [hleft, hright]
  exact hl

end A1Research
