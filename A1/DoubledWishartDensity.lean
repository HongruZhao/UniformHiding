import A1.DoubledWishartKernel
import A1.SymmetricSqrtCongruence

open Matrix MeasureTheory Set
open A3Research
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section
namespace A1Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def doubledPairWishartDensity (n m : ℕ)
    (p : HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m) : ℝ≥0∞ :=
  wishartAmbientDensity (2 * m) ℝ ((n : ℝ) / 2) (complexPairRealCoordinates p)

theorem measurable_doubledPairWishartDensity (n m : ℕ) :
    Measurable (doubledPairWishartDensity n m) :=
  (measurable_wishartAmbientDensity ((n : ℝ) / 2)).comp
    (doubledRealCoordinatePairLinearEquiv m).symm.toContinuousLinearEquiv.continuous.measurable

theorem doubledPairWishartDensity_eq_zero_of_not_posDef {n m : ℕ}
    {t : HermitianCoordinates m ℂ} (ht : ¬(hermitianMatrixOfCoordinates t).PosDef)
    (z : ComplexSymmetricCoordinates m) : doubledPairWishartDensity n m (t, z) = 0 := by
  classical
  unfold doubledPairWishartDensity wishartAmbientDensity
  exact if_neg (complexPairRealCoordinates_not_posDef_of_hermitianPart ht z)

theorem doubledPairWishartDensity_scaled {n m : ℕ}
    {t : HermitianCoordinates m ℂ} (ht : (hermitianMatrixOfCoordinates t).PosDef)
    (c : ComplexSymmetricCoordinates m) :
    ENNReal.ofReal ((hermitianMatrixOfCoordinates t).det.re ^ (m + 1)) *
      doubledPairWishartDensity n m (complexPairScaledCoordinates t c) =
        ENNReal.ofReal (doubledWishartKernelConstant n m) *
          wishartAmbientDensity m ℂ n t * FriedmanMelloA1.determinantWeight n m c := by
  classical
  have hpos : 0 < (hermitianMatrixOfCoordinates t).det.re := (Complex.pos_iff.mp ht.det_pos).1
  have hJ : 0 ≤ (hermitianMatrixOfCoordinates t).det.re ^ (m + 1) :=
    (pow_pos hpos _).le
  have hconst := (doubledWishartKernelConstant_pos n m).le
  by_cases hc : FriedmanMelloA1.support (complexSymmetricMatrixOfCoordinates c)
  · have hW := (complexPairRealCoordinates_scaled_posDef_iff ht c).mpr hc
    simp only [doubledPairWishartDensity, wishartAmbientDensity, if_pos hW, if_pos ht,
      FriedmanMelloA1.determinantWeight, if_pos hc]
    rw [← ENNReal.ofReal_mul hJ]
    have hK := (wishartAmbientKernel_pos (n : ℝ)
      (show t ∈ wishartPositiveDefiniteDomain m ℂ from ht)).le
    rw [← ENNReal.ofReal_mul hconst, ← ENNReal.ofReal_mul (mul_nonneg hconst hK)]
    congr 1
    rw [mul_comm ((hermitianMatrixOfCoordinates t).det.re ^ (m + 1)),
      doubledWishartKernel_scaled ht c hc]
    rfl
  · have hW : ¬(hermitianMatrixOfCoordinates (complexPairRealCoordinates
        (complexPairScaledCoordinates t c))).PosDef :=
      fun h ↦ hc ((complexPairRealCoordinates_scaled_posDef_iff ht c).mp h)
    simp only [doubledPairWishartDensity, wishartAmbientDensity, if_neg hW,
      FriedmanMelloA1.determinantWeight, if_neg hc, mul_zero]

theorem doubledPairWishartDensity_mul_jacobian {n m : ℕ}
    {t : HermitianCoordinates m ℂ} (ht : (hermitianMatrixOfCoordinates t).PosDef)
    (c : ComplexSymmetricCoordinates m) :
    ENNReal.ofReal |LinearMap.det (symmetricRealCongruenceLinearMap
      (CFC.sqrt (hermitianMatrixOfCoordinates t)).transpose)| *
      doubledPairWishartDensity n m (complexPairScaledCoordinates t c) =
        ENNReal.ofReal (doubledWishartKernelConstant n m) *
          wishartAmbientDensity m ℂ n t * FriedmanMelloA1.determinantWeight n m c := by
  rw [abs_det_symmetricRealCongruence_sqrt_transpose ht]
  exact doubledPairWishartDensity_scaled ht c

end A1Research
