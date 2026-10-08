import A3.BetaMatrixAlgebra
import A3.WishartAmbientKernel

open scoped BigOperators Matrix.Norms.Elementwise ComplexOrder MatrixOrder ENNReal
open Matrix MeasureTheory Set

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

namespace A3Research

variable {n : ℕ} {K : Type*} [RCLike K]

def hermitianComplementCoordinates (x : HermitianCoordinates n K) : HermitianCoordinates n K :=
  hermitianCoordinateProjection (1 - hermitianMatrixOfCoordinates x)

@[simp] theorem hermitianMatrixOf_complementCoordinates (x : HermitianCoordinates n K) :
    hermitianMatrixOfCoordinates (hermitianComplementCoordinates x) =
      1 - hermitianMatrixOfCoordinates x :=
  hermitianMatrixOfCoordinates_projection _
    (Matrix.isHermitian_one.sub (hermitianMatrixOfCoordinates_isHermitian x))

theorem continuous_hermitianComplementCoordinates :
    Continuous (hermitianComplementCoordinates : HermitianCoordinates n K → _) :=
  continuous_hermitianCoordinateProjection.comp
    (continuous_const.sub continuous_hermitianMatrixOfCoordinates)

theorem det_eq_ofReal_re_of_isHermitian {C : Matrix (Fin n) (Fin n) K}
    (hC : C.IsHermitian) : C.det = (RCLike.re C.det : K) := by
  rw [hC.det_eq_prod_eigenvalues, ← map_prod (algebraMap ℝ K)]
  simp only [RCLike.ofReal_re]

theorem wishartDetReal_hermitianConjugation
    {C : Matrix (Fin n) (Fin n) K} (hC : C.IsHermitian) (x : HermitianCoordinates n K) :
    wishartDetReal (hermitianCoordinateConjugationLinearMap C x) =
      RCLike.re (C * C).det * wishartDetReal x := by
  unfold wishartDetReal
  rw [hermitianCoordinateConjugation_reconstruct, hC.eq,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_mul,
    det_eq_ofReal_re_of_isHermitian hC,
    det_eq_ofReal_re_of_isHermitian (hermitianMatrixOfCoordinates_isHermitian x)]
  simp only [RCLike.mul_re, RCLike.ofReal_re, RCLike.ofReal_im, mul_zero, sub_zero]
  ring

def betaMatrixKernel (n : ℕ) (K : Type*) [RCLike K] (α δ : ℝ)
    (x : HermitianCoordinates n K) : ℝ :=
  wishartDetReal x ^ (α - wishartHermitianKappa n K) *
    wishartDetReal (hermitianComplementCoordinates x) ^ (δ - wishartHermitianKappa n K)

def betaMatrixDensity (n : ℕ) (K : Type*) [RCLike K] (α δ : ℝ)
    (x : HermitianCoordinates n K) : ℝ≥0∞ := by
  classical
  exact if x ∈ hermitianBetaDomain n K then ENNReal.ofReal (betaMatrixKernel n K α δ x) else 0

def betaMatrixRawMeasure (n : ℕ) (K : Type*) [RCLike K]
    [MeasureSpace K] [BorelSpace K] (α δ : ℝ) : Measure (HermitianCoordinates n K) :=
  (hermitianCoordinateVolume n K).withDensity (betaMatrixDensity n K α δ)

theorem betaMatrixKernel_pos (α δ : ℝ) {x : HermitianCoordinates n K}
    (hx : x ∈ hermitianBetaDomain n K) : 0 < betaMatrixKernel n K α δ x := by
  apply mul_pos
  · exact Real.rpow_pos_of_pos (wishartDetReal_pos hx.1) _
  · apply Real.rpow_pos_of_pos
    apply wishartDetReal_pos
    change (hermitianMatrixOfCoordinates (hermitianComplementCoordinates x)).PosDef
    rw [hermitianMatrixOf_complementCoordinates]
    exact hx.2

theorem measurable_betaMatrixKernel [MeasurableSpace K] [BorelSpace K] (α δ : ℝ) :
    Measurable (betaMatrixKernel n K α δ) := by
  unfold betaMatrixKernel wishartDetReal
  have hc := continuous_hermitianComplementCoordinates (n := n) (K := K)
  have hm := continuous_hermitianMatrixOfCoordinates (n := n) (K := K)
  fun_prop

theorem measurable_betaMatrixDensity [MeasurableSpace K] [BorelSpace K] [PolishSpace K]
    (α δ : ℝ) : Measurable (betaMatrixDensity n K α δ) := by
  classical
  exact Measurable.ite (measurableSet_hermitianBetaDomain (n := n) (K := K))
    (measurable_betaMatrixKernel α δ).ennreal_ofReal measurable_const

theorem wishartHermitianKappa_nat_sub (hn : 1 ≤ n) :
    wishartHermitianKappa n K = 1 + (Module.finrank ℝ K : ℝ) * (n - 1 : ℕ) / 2 := by
  rw [wishartHermitianKappa, Nat.cast_sub hn, Nat.cast_one]

/-- Actual complement congruence adds back the fixed total matrix. -/
theorem hermitianConjugation_add_complement
    {C : Matrix (Fin n) (Fin n) K} (hC : C.IsHermitian) (x : HermitianCoordinates n K) :
    hermitianMatrixOfCoordinates (hermitianCoordinateConjugationLinearMap C x) +
      hermitianMatrixOfCoordinates (hermitianCoordinateConjugationLinearMap C
        (hermitianComplementCoordinates x)) = C * C := by
  rw [hermitianCoordinateConjugation_reconstruct,
    hermitianCoordinateConjugation_reconstruct, hermitianMatrixOf_complementCoordinates,
    ← Matrix.add_mul, ← Matrix.mul_add, add_sub_cancel, Matrix.mul_one, hC.eq]

/-- The product of the two Wishart exponential factors is the total trace factor. -/
theorem exp_neg_trace_hermitianConjugation_pair
    {C : Matrix (Fin n) (Fin n) K} (hC : C.IsHermitian) (x : HermitianCoordinates n K) :
    Real.exp (-wishartTraceReal (hermitianCoordinateConjugationLinearMap C x)) *
      Real.exp (-wishartTraceReal (hermitianCoordinateConjugationLinearMap C
        (hermitianComplementCoordinates x))) = Real.exp (-RCLike.re (C * C).trace) := by
  rw [← Real.exp_add]
  congr 1
  unfold wishartTraceReal
  rw [← neg_add, ← map_add, ← Matrix.trace_add, hermitianConjugation_add_complement hC]

/-- Exact density factorization under the fixed positive-definite congruence. -/
theorem wishartAmbientKernel_pair_jacobian
    (hn : 1 ≤ n) (α δ : ℝ) {C : Matrix (Fin n) (Fin n) K} (hC : C.PosDef)
    {x : HermitianCoordinates n K} (hx : x ∈ hermitianBetaDomain n K) :
    wishartAmbientKernel n K α (hermitianCoordinateConjugationLinearMap C x) *
      wishartAmbientKernel n K δ (hermitianCoordinateConjugationLinearMap C
        (hermitianComplementCoordinates x)) *
      |LinearMap.det (hermitianCoordinateConjugationLinearMap C)| =
      wishartAmbientKernel n K (α + δ) (hermitianCoordinateProjection (C * C)) *
        betaMatrixKernel n K α δ x := by
  have hcomp : hermitianComplementCoordinates x ∈ wishartPositiveDefiniteDomain n K := by
    change (hermitianMatrixOfCoordinates (hermitianComplementCoordinates x)).PosDef
    rw [hermitianMatrixOf_complementCoordinates]
    exact hx.2
  have hS : (C * C).PosDef := by
    simpa only [Matrix.star_eq_conjTranspose, hC.isHermitian.eq, Matrix.mul_one] using
      hC.isUnit.posDef_star_right_conjugate_iff.mpr
        (show (1 : Matrix (Fin n) (Fin n) K).PosDef from Matrix.PosDef.one)
  have hpS := re_det_pos_of_posDef hS
  have hpx := wishartDetReal_pos hx.1
  have hpc := wishartDetReal_pos hcomp
  have hproj := hermitianMatrixOfCoordinates_projection (C * C) hS.isHermitian
  unfold wishartAmbientKernel betaMatrixKernel
  rw [wishartDetReal_hermitianConjugation hC.isHermitian,
    wishartDetReal_hermitianConjugation hC.isHermitian,
    Real.mul_rpow hpS.le hpx.le, Real.mul_rpow hpS.le hpc.le,
    abs_det_hermitianCoordinateConjugation_posDef_square hC,
    ← wishartHermitianKappa_nat_sub (K := K) hn]
  have hexp := exp_neg_trace_hermitianConjugation_pair hC.isHermitian x
  have hpow : (RCLike.re (C * C).det) ^ (α - wishartHermitianKappa n K) *
      (RCLike.re (C * C).det) ^ (δ - wishartHermitianKappa n K) *
      (RCLike.re (C * C).det) ^ wishartHermitianKappa n K =
      (RCLike.re (C * C).det) ^ (α + δ - wishartHermitianKappa n K) := by
    rw [← Real.rpow_add hpS, ← Real.rpow_add hpS]
    congr 1
    ring
  have hedet : wishartDetReal (hermitianCoordinateProjection (C * C)) =
      RCLike.re (C * C).det := by rw [wishartDetReal, hproj]
  have hetr : wishartTraceReal (hermitianCoordinateProjection (C * C)) =
      RCLike.re (C * C).trace := by rw [wishartTraceReal, hproj]
  rw [hedet, hetr]
  calc
    _ = (Real.exp (-wishartTraceReal (hermitianCoordinateConjugationLinearMap C x)) *
        Real.exp (-wishartTraceReal (hermitianCoordinateConjugationLinearMap C
          (hermitianComplementCoordinates x)))) *
        ((RCLike.re (C * C).det) ^ (α - wishartHermitianKappa n K) *
          (RCLike.re (C * C).det) ^ (δ - wishartHermitianKappa n K) *
          (RCLike.re (C * C).det) ^ wishartHermitianKappa n K) *
        (wishartDetReal x ^ (α - wishartHermitianKappa n K) *
          wishartDetReal (hermitianComplementCoordinates x) ^ (δ - wishartHermitianKappa n K)) := by ring
    _ = _ := by rw [hexp, hpow]

end A3Research
