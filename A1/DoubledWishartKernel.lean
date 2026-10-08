import A1.DoubledGramSupport
import A1.SymmetricCongruenceMeasure
import A1.CornerSquareRootMeasurable

open Matrix MeasureTheory Set
open A3Research
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator ENNReal

noncomputable section
namespace A1Research

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def normalizedComplexPairCoordinates {m : ℕ}
    (p : HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m) :
    ComplexSymmetricCoordinates m :=
  A2Research.symmetricCoordinateProjection m
    (normalizedComplexPairOverlap (hermitianMatrixOfCoordinates p.1)
      (complexSymmetricMatrixOfCoordinates p.2))

theorem measurable_normalizedComplexPairCoordinates (m : ℕ) :
    Measurable (normalizedComplexPairCoordinates (m := m)) := by
  have hp : Measurable (fun p : HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m ↦
      (hermitianMatrixOfCoordinates p.1, complexSymmetricMatrixOfCoordinates p.2)) :=
    ((measurable_hermitianMatrixOfCoordinates m ℂ).comp measurable_fst).prodMk
      ((continuous_symmetricCoordinateReconstruction m).measurable.comp measurable_snd)
  have hm := (measurable_normalizedComplexPairOverlap m).comp hp
  exact (measurable_symmetricCoordinateProjection m).comp hm

def complexPairScaledCoordinates {m : ℕ} (t : HermitianCoordinates m ℂ)
    (c : ComplexSymmetricCoordinates m) :
    HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m :=
  (t, symmetricRealCongruenceLinearMap (CFC.sqrt (hermitianMatrixOfCoordinates t)).transpose c)

theorem complexPairScaledCoordinates_reconstruct {m : ℕ}
    (t : HermitianCoordinates m ℂ) (c : ComplexSymmetricCoordinates m) :
    complexSymmetricMatrixOfCoordinates (complexPairScaledCoordinates t c).2 =
      (CFC.sqrt (hermitianMatrixOfCoordinates t)).transpose *
        complexSymmetricMatrixOfCoordinates c * CFC.sqrt (hermitianMatrixOfCoordinates t) := by
  change A2Research.symmetricCoordinateEmbedding m
      (A2Research.symmetricCongruenceLinearMap
        (CFC.sqrt (hermitianMatrixOfCoordinates t)).transpose c) =
    (CFC.sqrt (hermitianMatrixOfCoordinates t)).transpose *
      A2Research.symmetricCoordinateEmbedding m c * CFC.sqrt (hermitianMatrixOfCoordinates t)
  rw [A2Research.symmetricCoordinateEmbedding_congruence, Matrix.transpose_transpose]

theorem normalizedComplexPairCoordinates_scaled {m : ℕ}
    {t : HermitianCoordinates m ℂ} (ht : (hermitianMatrixOfCoordinates t).PosDef)
    (c : ComplexSymmetricCoordinates m) :
    normalizedComplexPairCoordinates (complexPairScaledCoordinates t c) = c := by
  unfold normalizedComplexPairCoordinates
  rw [complexPairScaledCoordinates_reconstruct]
  dsimp only [complexPairScaledCoordinates, Prod.fst]
  have hL := (A3Research.posDef_cfc_sqrt ht).isUnit
  have hLt : IsUnit (CFC.sqrt (hermitianMatrixOfCoordinates t)).transpose := by
    simpa only [Matrix.isUnit_transpose] using hL
  unfold normalizedComplexPairOverlap
  rw [← mul_assoc, ← mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hLt),
    one_mul, mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hL), mul_one]
  exact A2Research.symmetricCoordinateProjection_embedding m c

theorem trace_submatrix_equiv {I J : Type*} [Fintype I] [Fintype J]
    {R : Type*} [AddCommMonoid R] (e : I ≃ J) (W : Matrix J J R) :
    (W.submatrix e e).trace = W.trace := by
  unfold Matrix.trace Matrix.diag
  exact Equiv.sum_comp e (fun j ↦ W j j)

theorem hermitianMatrixOfCoordinates_complexPair {m : ℕ}
    (p : HermitianCoordinates m ℂ × ComplexSymmetricCoordinates m) :
    hermitianMatrixOfCoordinates (complexPairRealCoordinates p) =
      (complexPairRealMatrix (hermitianMatrixOfCoordinates p.1)
        (complexSymmetricMatrixOfCoordinates p.2)).submatrix
          (doubledIndexEquiv m).symm (doubledIndexEquiv m).symm := by
  have h := doubledRealCoordinatesMatrix_complexPair p
  ext i j
  have hi := congrArg (fun W ↦ W ((doubledIndexEquiv m).symm i)
    ((doubledIndexEquiv m).symm j)) h
  simpa only [doubledRealCoordinatesMatrix, Matrix.submatrix, Matrix.of_apply,
    Equiv.apply_symm_apply] using hi

theorem complexPairRealCoordinates_scaled_posDef_iff {m : ℕ}
    {t : HermitianCoordinates m ℂ} (ht : (hermitianMatrixOfCoordinates t).PosDef)
    (c : ComplexSymmetricCoordinates m) :
    (hermitianMatrixOfCoordinates (complexPairRealCoordinates
      (complexPairScaledCoordinates t c))).PosDef ↔
        FriedmanMelloA1.support (complexSymmetricMatrixOfCoordinates c) := by
  rw [hermitianMatrixOfCoordinates_complexPair,
    posDef_submatrix_equiv_rclike, complexPairScaledCoordinates_reconstruct]
  exact complexPairRealMatrix_scaled_posDef_iff ht (complexSymmetricMatrixOfCoordinates_isSymm c)

theorem complexPairRealCoordinates_not_posDef_of_hermitianPart {m : ℕ}
    {t : HermitianCoordinates m ℂ} (ht : ¬(hermitianMatrixOfCoordinates t).PosDef)
    (z : ComplexSymmetricCoordinates m) :
    ¬(hermitianMatrixOfCoordinates (complexPairRealCoordinates (t, z))).PosDef := by
  rw [hermitianMatrixOfCoordinates_complexPair, posDef_submatrix_equiv_rclike,
    complexPairRealMatrix_posDef_iff_augmented]
  exact fun h ↦ ht (augmentedComplexPair_posDef_hermitianPart h)

def doubledWishartKernelConstant (n m : ℕ) : ℝ :=
  (((2 : ℝ) ^ (2 * m))⁻¹) ^ FriedmanMelloA1.densityExponent n m

theorem doubledWishartKernelConstant_pos (n m : ℕ) :
    0 < doubledWishartKernelConstant n m :=
  Real.rpow_pos_of_pos (inv_pos.mpr (by positivity)) _

theorem doubledWishartKernel_exponent (n m : ℕ) :
    (n : ℝ) / 2 - wishartHermitianKappa (2 * m) ℝ =
      FriedmanMelloA1.densityExponent n m := by
  simp only [wishartHermitianKappa, Module.finrank_self, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, FriedmanMelloA1.densityExponent]
  ring

theorem doubledWishartKernel_scaled {n m : ℕ}
    {t : HermitianCoordinates m ℂ} (ht : (hermitianMatrixOfCoordinates t).PosDef)
    (c : ComplexSymmetricCoordinates m)
    (hc : FriedmanMelloA1.support (complexSymmetricMatrixOfCoordinates c)) :
    wishartAmbientKernel (2 * m) ℝ ((n : ℝ) / 2)
      (complexPairRealCoordinates (complexPairScaledCoordinates t c)) *
        (hermitianMatrixOfCoordinates t).det.re ^ (m + 1) =
      doubledWishartKernelConstant n m *
        wishartAmbientKernel m ℂ n t *
          (1 - (complexSymmetricMatrixOfCoordinates c).conjTranspose *
            complexSymmetricMatrixOfCoordinates c).det.re ^
              FriedmanMelloA1.densityExponent n m := by
  have hd := complexPairRealMatrix_scaled_det ht (complexSymmetricMatrixOfCoordinates_isSymm c)
  have htr := complexPairRealMatrix_trace (hermitianMatrixOfCoordinates t)
    ((CFC.sqrt (hermitianMatrixOfCoordinates t)).transpose *
      complexSymmetricMatrixOfCoordinates c * CFC.sqrt (hermitianMatrixOfCoordinates t))
  have hp : 0 < (hermitianMatrixOfCoordinates t).det.re := (Complex.pos_iff.mp ht.det_pos).1
  have hgap : 0 < (1 - (complexSymmetricMatrixOfCoordinates c).conjTranspose *
      complexSymmetricMatrixOfCoordinates c).det.re := (Complex.pos_iff.mp hc.det_pos).1
  unfold wishartAmbientKernel wishartDetReal wishartTraceReal
  rw [hermitianMatrixOfCoordinates_complexPair, complexPairScaledCoordinates_reconstruct,
    Matrix.det_submatrix_equiv_self, trace_submatrix_equiv]
  dsimp only [complexPairScaledCoordinates, Prod.fst, RCLike.re_to_real]
  rw [hd, htr, doubledWishartKernel_exponent]
  rw [Real.mul_rpow (mul_nonneg (inv_nonneg.mpr (by positivity)) (sq_nonneg _)) hgap.le,
    Real.mul_rpow (inv_nonneg.mpr (by positivity)) (sq_nonneg _),
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul hp.le,
    ← Real.rpow_natCast _ (m + 1)]
  have he : 2 * FriedmanMelloA1.densityExponent n m + (m + 1 : ℕ) =
      (n : ℝ) - wishartHermitianKappa m ℂ := by
    simp only [FriedmanMelloA1.densityExponent, wishartHermitianKappa,
      Complex.finrank_real_complex, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    ring
  have hpow : (hermitianMatrixOfCoordinates t).det.re ^
        (2 * FriedmanMelloA1.densityExponent n m) *
      (hermitianMatrixOfCoordinates t).det.re ^ ((m + 1 : ℕ) : ℝ) =
        (hermitianMatrixOfCoordinates t).det.re ^ ((n : ℝ) - wishartHermitianKappa m ℂ) := by
    rw [← Real.rpow_add hp, he]
  unfold doubledWishartKernelConstant
  calc
    _ = (((2 : ℝ) ^ (2 * m))⁻¹) ^ FriedmanMelloA1.densityExponent n m *
      (Real.exp (-(hermitianMatrixOfCoordinates t).trace.re) *
        ((hermitianMatrixOfCoordinates t).det.re ^
            (2 * FriedmanMelloA1.densityExponent n m) *
          (hermitianMatrixOfCoordinates t).det.re ^ ((m + 1 : ℕ) : ℝ))) *
      (1 - (complexSymmetricMatrixOfCoordinates c).conjTranspose *
        complexSymmetricMatrixOfCoordinates c).det.re ^
          FriedmanMelloA1.densityExponent n m := by norm_num only [Nat.cast_ofNat]; ring
    _ = _ := by rw [hpow]; rfl

end A1Research
