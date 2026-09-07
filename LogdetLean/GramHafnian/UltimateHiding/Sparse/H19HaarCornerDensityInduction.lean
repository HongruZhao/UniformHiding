import LogdetLean.GramHafnian.UltimateHiding.Sparse.CircularGaussianDensityBasic
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19JiangRawDensity
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.RingTheory.Complex

/-!
# Algebraic ingredients for an inductive Haar-corner density proof

This file contains only finite-dimensional algebra and change-of-variables
lemmas.  In particular, it does not use the raw Jiang density axiom.  The
lemmas isolate the determinant and complex Jacobian calculations needed when
one appends a column to a rectangular matrix and then writes the new column as
`x = D^(1/2) u`, where `D = I - A Aᴴ`.
-/

open MeasureTheory Matrix
open scoped ENNReal BigOperators ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

open LocalAnticoncentration

/-! ## Appending one block-column -/

/-- Appending a block-column adds its row Gram matrix. -/
theorem fromCols_mul_conjTranspose_eq_add
    {m n r : Type*} [Fintype n] [Fintype r]
    (A : Matrix m n ℂ) (x : Matrix m r ℂ) :
    Matrix.fromCols A x * (Matrix.fromCols A x).conjTranspose =
      A * A.conjTranspose + x * x.conjTranspose := by
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows]

/-- The column Gram matrix of an appended block-column is the corresponding
`2 x 2` block matrix. -/
theorem conjTranspose_mul_fromCols_eq_fromBlocks
    {m n r : Type*} [Fintype m]
    (A : Matrix m n ℂ) (x : Matrix m r ℂ) :
    (Matrix.fromCols A x).conjTranspose * Matrix.fromCols A x =
      Matrix.fromBlocks
        (A.conjTranspose * A) (A.conjTranspose * x)
        (x.conjTranspose * A) (x.conjTranspose * x) := by
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul_fromCols]

/-- The literal block form of `I - [A x]ᴴ[A x]`. -/
theorem one_sub_conjTranspose_mul_fromCols_eq_fromBlocks
    {m n r : Type*} [Fintype m] [DecidableEq n] [DecidableEq r]
    (A : Matrix m n ℂ) (x : Matrix m r ℂ) :
    1 - (Matrix.fromCols A x).conjTranspose * Matrix.fromCols A x =
      Matrix.fromBlocks
        (1 - A.conjTranspose * A) (-(A.conjTranspose * x))
        (-(x.conjTranspose * A)) (1 - x.conjTranspose * x) := by
  rw [conjTranspose_mul_fromCols_eq_fromBlocks]
  ext (_ | _) (_ | _) <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

/-- Block-column Schur determinant identity.  This is the usual first step
in an induction on the number of columns. -/
theorem det_one_sub_conjTranspose_mul_fromCols_schur
    {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r]
    (A : Matrix m n ℂ) (x : Matrix m r ℂ)
    [Invertible (1 - A.conjTranspose * A)] :
    Matrix.det
        (1 - (Matrix.fromCols A x).conjTranspose * Matrix.fromCols A x) =
      Matrix.det (1 - A.conjTranspose * A) *
        Matrix.det
          ((1 - x.conjTranspose * x) -
            (-(x.conjTranspose * A)) * ⅟(1 - A.conjTranspose * A) *
              (-(A.conjTranspose * x))) := by
  rw [one_sub_conjTranspose_mul_fromCols_eq_fromBlocks,
    Matrix.det_fromBlocks₁₁]

/-- The same Schur identity with the two minus signs in the off-diagonal
blocks cancelled. -/
theorem det_one_sub_conjTranspose_mul_fromCols_schur_clean
    {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq n] [DecidableEq r]
    (A : Matrix m n ℂ) (x : Matrix m r ℂ)
    [Invertible (1 - A.conjTranspose * A)] :
    Matrix.det
        (1 - (Matrix.fromCols A x).conjTranspose * Matrix.fromCols A x) =
      Matrix.det (1 - A.conjTranspose * A) *
        Matrix.det
          ((1 - x.conjTranspose * x) -
            (x.conjTranspose * A) * ⅟(1 - A.conjTranspose * A) *
              (A.conjTranspose * x)) := by
  rw [det_one_sub_conjTranspose_mul_fromCols_schur]
  congr 2
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-- Sylvester's determinant identity in the exact two orientations used by
the rectangular matrix-ball density. -/
theorem det_one_sub_conjTranspose_mul_eq_det_one_sub_mul_conjTranspose
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℂ) :
    Matrix.det (1 - A.conjTranspose * A) =
      Matrix.det (1 - A * A.conjTranspose) := by
  simpa using Matrix.det_one_sub_mul_comm A.conjTranspose A

/-- Appending a block-column converts the determinant to the rank update
`D - x xᴴ`, where `D = I - A Aᴴ`.  No invertibility is required. -/
theorem det_one_sub_conjTranspose_mul_fromCols_eq_rankUpdate
    {m n r : Type*} [Fintype m] [Fintype n] [Fintype r]
    [DecidableEq m] [DecidableEq n] [DecidableEq r]
    (A : Matrix m n ℂ) (x : Matrix m r ℂ) :
    Matrix.det
        (1 - (Matrix.fromCols A x).conjTranspose * Matrix.fromCols A x) =
      Matrix.det ((1 - A * A.conjTranspose) - x * x.conjTranspose) := by
  rw [Matrix.det_one_sub_mul_comm
      (Matrix.fromCols A x).conjTranspose (Matrix.fromCols A x),
    fromCols_mul_conjTranspose_eq_add]
  congr 1
  noncomm_ring

/-! ## Complex-linear real Jacobian -/

/-- Coordinatewise complex Lebesgue measure on one complex column. -/
def complexColumnLebesgueVolume (K : ℕ) :
    Measure (Fin K → ℂ) :=
  Measure.pi fun _ : Fin K ↦ (volume : Measure ℂ)

instance complexColumnLebesgueVolume_sigmaFinite
    (K : ℕ) :
    SigmaFinite (complexColumnLebesgueVolume K) := by
  unfold complexColumnLebesgueVolume
  exact Measure.pi.sigmaFinite _

instance complexColumnLebesgueVolume_isAddHaarMeasure
    (K : ℕ) :
    Measure.IsAddHaarMeasure (complexColumnLebesgueVolume K) := by
  unfold complexColumnLebesgueVolume
  exact Measure.pi.isAddHaarMeasure _

theorem complexColumnLebesgueVolume_eq_volume (K : ℕ) :
    complexColumnLebesgueVolume K = (volume : Measure (Fin K → ℂ)) := by
  exact MeasureTheory.volume_pi.symm

/-- The determinant of a complex-linear endomorphism, viewed as a real-linear
endomorphism, is the complex norm-square of its complex determinant. -/
theorem det_restrictScalars_mulVecLin
    {K : ℕ} (S : Matrix (Fin K) (Fin K) ℂ) :
    LinearMap.det ((S.mulVecLin).restrictScalars ℝ) =
      Complex.normSq (Matrix.det S) := by
  rw [LinearMap.det_restrictScalars, ← Matrix.toLin'_apply',
    LinearMap.det_toLin', Algebra.norm_complex_apply]

/-- Real Jacobian / volume scaling for the complex-linear substitution
`x = S u`.  The multiplier is `|det_C S|^(-2)`. -/
theorem map_complexColumnLebesgueVolume_mulVec
    {K : ℕ} (S : Matrix (Fin K) (Fin K) ℂ)
    (hS : Matrix.det S ≠ 0) :
    Measure.map (fun u : Fin K → ℂ ↦ S *ᵥ u)
        (complexColumnLebesgueVolume K) =
      ENNReal.ofReal |(Complex.normSq (Matrix.det S))⁻¹| •
        complexColumnLebesgueVolume K := by
  rw [complexColumnLebesgueVolume_eq_volume]
  have hreal : LinearMap.det ((S.mulVecLin).restrictScalars ℝ) ≠ 0 := by
    rw [det_restrictScalars_mulVecLin]
    exact (Complex.normSq_pos.mpr hS).ne'
  change Measure.map ((S.mulVecLin).restrictScalars ℝ)
      (volume : Measure (Fin K → ℂ)) = _
  simpa only [det_restrictScalars_mulVecLin] using
    (Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (Fin K → ℂ)) hreal)

/-! ## The positive defect square root -/

/-- The left defect attached to a rectangular matrix. -/
def haarCornerLeftDefect {K N : ℕ}
    (A : Matrix (Fin K) (Fin N) ℂ) : Matrix (Fin K) (Fin K) ℂ :=
  1 - A * A.conjTranspose

/-- The canonical positive square root of the left defect. -/
def haarCornerDefectSqrt {K N : ℕ}
    (A : Matrix (Fin K) (Fin N) ℂ) : Matrix (Fin K) (Fin K) ℂ :=
  CFC.sqrt (haarCornerLeftDefect A)

def haarCornerDefectSqrtLinear {K N : ℕ}
    (A : Matrix (Fin K) (Fin N) ℂ) :
    (Fin K → ℂ) →ₗ[ℂ] (Fin K → ℂ) :=
  (haarCornerDefectSqrt A).mulVecLin

theorem haarCornerDefectSqrt_mul_self
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) :
    haarCornerDefectSqrt A * haarCornerDefectSqrt A =
      haarCornerLeftDefect A := by
  exact CFC.sqrt_mul_sqrt_self _ hA.posSemidef.nonneg

theorem haarCornerDefectSqrt_isHermitian
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ) :
    (haarCornerDefectSqrt A).IsHermitian := by
  exact IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)

theorem haarCornerDefectSqrt_isUnit
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) :
    IsUnit (haarCornerDefectSqrt A) := by
  exact (CFC.isUnit_sqrt_iff _ hA.posSemidef.nonneg).mpr hA.isUnit

theorem haarCornerDefectSqrtLinear_det
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ) :
    (haarCornerDefectSqrtLinear A).det =
      (haarCornerDefectSqrt A).det := by
  change LinearMap.det (Matrix.toLin' (haarCornerDefectSqrt A)) = _
  exact LinearMap.det_toLin' _

theorem haarCornerDefectSqrtLinear_det_ne_zero
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) :
    (haarCornerDefectSqrtLinear A).det ≠ 0 := by
  rw [haarCornerDefectSqrtLinear_det]
  simpa [Matrix.isUnit_iff_isUnit_det] using
    haarCornerDefectSqrt_isUnit A hA

/-- The real Jacobian of `u ↦ D^(1/2)u` is `det D`. -/
theorem haarCornerDefectSqrtLinear_real_det
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) :
    ((haarCornerDefectSqrtLinear A).restrictScalars ℝ).det =
      (haarCornerLeftDefect A).det.re := by
  change LinearMap.det
      (((haarCornerDefectSqrt A).mulVecLin).restrictScalars ℝ) = _
  rw [det_restrictScalars_mulVecLin,
    show haarCornerDefectSqrt A = CFC.sqrt (haarCornerLeftDefect A) by rfl,
    Matrix.PosSemidef.det_sqrt hA.posSemidef]
  rw [RCLike.sqrt_of_nonneg hA.det_pos.le]
  change Complex.normSq
      ((↑(√((haarCornerLeftDefect A).det.re)) : ℂ)) =
    (haarCornerLeftDefect A).det.re
  rw [Complex.normSq_ofReal]
  exact Real.mul_self_sqrt ((RCLike.nonneg_iff.mp hA.det_pos.le).1)

/-- Exact volume scaling for the square-root substitution `x = D^(1/2)u`. -/
theorem map_complexColumnLebesgueVolume_haarCornerDefectSqrt
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) :
    Measure.map
        (fun u : Fin K → ℂ ↦ haarCornerDefectSqrt A *ᵥ u)
        (complexColumnLebesgueVolume K) =
      ENNReal.ofReal |((haarCornerLeftDefect A).det.re)⁻¹| •
        complexColumnLebesgueVolume K := by
  have hdetReal := haarCornerDefectSqrtLinear_real_det A hA
  change LinearMap.det
      (((haarCornerDefectSqrt A).mulVecLin).restrictScalars ℝ) = _ at hdetReal
  rw [det_restrictScalars_mulVecLin] at hdetReal
  rw [map_complexColumnLebesgueVolume_mulVec
    (haarCornerDefectSqrt A)]
  · rw [hdetReal]
  · rw [← haarCornerDefectSqrtLinear_det]
    exact haarCornerDefectSqrtLinear_det_ne_zero A hA

/-- The invertible square-root substitution as a measurable equivalence. -/
def haarCornerDefectSqrtMeasurableEquiv
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) :
    (Fin K → ℂ) ≃ᵐ (Fin K → ℂ) :=
  ((haarCornerDefectSqrtLinear A).equivOfDetNeZero (haarCornerDefectSqrtLinear_det_ne_zero A hA)).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

@[simp]
theorem haarCornerDefectSqrtMeasurableEquiv_apply
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) (u : Fin K → ℂ) :
    haarCornerDefectSqrtMeasurableEquiv A hA u =
      haarCornerDefectSqrt A *ᵥ u :=
  rfl

theorem map_haarCornerDefectSqrtMeasurableEquiv_volume
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) :
    Measure.map (haarCornerDefectSqrtMeasurableEquiv A hA)
        (complexColumnLebesgueVolume K) =
      ENNReal.ofReal |((haarCornerLeftDefect A).det.re)⁻¹| •
        complexColumnLebesgueVolume K := by
  change Measure.map
      (fun u : Fin K → ℂ ↦ haarCornerDefectSqrt A *ᵥ u)
      (complexColumnLebesgueVolume K) = _
  exact map_complexColumnLebesgueVolume_haarCornerDefectSqrt A hA

/-- Density transport under `x = D^(1/2)u`.  This is the exact
change-of-variables formula: compose the old density with the inverse map and
multiply by the inverse real Jacobian. -/
theorem map_haarCornerDefectSqrtMeasurableEquiv_withDensity
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef)
    (rho : (Fin K → ℂ) → ℝ≥0∞) (hrho : Measurable rho) :
    Measure.map (haarCornerDefectSqrtMeasurableEquiv A hA)
        ((complexColumnLebesgueVolume K).withDensity rho) =
      (complexColumnLebesgueVolume K).withDensity
        (fun x ↦
          ENNReal.ofReal |((haarCornerLeftDefect A).det.re)⁻¹| *
            rho ((haarCornerDefectSqrtMeasurableEquiv A hA).symm x)) := by
  let e := haarCornerDefectSqrtMeasurableEquiv A hA
  rw [map_measurableEquiv_withDensity_localAnticoncentration e
    (complexColumnLebesgueVolume K) rho hrho]
  rw [map_haarCornerDefectSqrtMeasurableEquiv_volume A hA,
    withDensity_smul_measure,
    ← withDensity_smul
      (ENNReal.ofReal |((haarCornerLeftDefect A).det.re)⁻¹|)
      (hrho.comp e.symm.measurable)]
  congr 1

/-! ## Determinant factorization after `x = D^(1/2)u` -/

/-- Matrix identity behind the square-root substitution. -/
theorem haarCorner_rankUpdate_sqrt_factorization
    {K N r : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef)
    (u : Matrix (Fin K) (Fin r) ℂ) :
    haarCornerLeftDefect A -
        (haarCornerDefectSqrt A * u) *
          (haarCornerDefectSqrt A * u).conjTranspose =
      haarCornerDefectSqrt A *
        (1 - u * u.conjTranspose) * haarCornerDefectSqrt A := by
  rw [Matrix.conjTranspose_mul,
    (haarCornerDefectSqrt_isHermitian A).eq,
    ← haarCornerDefectSqrt_mul_self A hA]
  have hprod :
      (haarCornerDefectSqrt A * u) *
          (u.conjTranspose * haarCornerDefectSqrt A) =
        (haarCornerDefectSqrt A * (u * u.conjTranspose)) *
          haarCornerDefectSqrt A := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [hprod, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]

/-- Determinant factorization for the rank update after the square-root
substitution. -/
theorem det_haarCorner_rankUpdate_sqrt_factorization
    {K N r : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef)
    (u : Matrix (Fin K) (Fin r) ℂ) :
    Matrix.det
        (haarCornerLeftDefect A -
          (haarCornerDefectSqrt A * u) *
            (haarCornerDefectSqrt A * u).conjTranspose) =
      Matrix.det (haarCornerLeftDefect A) *
        Matrix.det (1 - u * u.conjTranspose) := by
  rw [haarCorner_rankUpdate_sqrt_factorization A hA u,
    Matrix.det_mul, Matrix.det_mul]
  calc
    Matrix.det (haarCornerDefectSqrt A) *
          Matrix.det (1 - u * u.conjTranspose) *
          Matrix.det (haarCornerDefectSqrt A) =
        Matrix.det (haarCornerDefectSqrt A * haarCornerDefectSqrt A) *
          Matrix.det (1 - u * u.conjTranspose) := by
            rw [Matrix.det_mul]
            ring
    _ = Matrix.det (haarCornerLeftDefect A) *
          Matrix.det (1 - u * u.conjTranspose) := by
            rw [haarCornerDefectSqrt_mul_self A hA]

/-- Complete appended-column determinant separation. -/
theorem det_one_sub_appended_sqrtColumn_factorization
    {K N r : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef)
    (u : Matrix (Fin K) (Fin r) ℂ) :
    Matrix.det
        (1 -
          (Matrix.fromCols A (haarCornerDefectSqrt A * u)).conjTranspose *
            Matrix.fromCols A (haarCornerDefectSqrt A * u)) =
      Matrix.det (haarCornerLeftDefect A) *
        Matrix.det (1 - u * u.conjTranspose) := by
  rw [det_one_sub_conjTranspose_mul_fromCols_eq_rankUpdate]
  exact det_haarCorner_rankUpdate_sqrt_factorization A hA u

/-! ## The one-column radial factor -/

def complexColumnMatrix {K : ℕ} (u : Fin K → ℂ) :
    Matrix (Fin K) (Fin 1) ℂ :=
  fun i _ ↦ u i

@[simp]
theorem complexColumnMatrix_apply {K : ℕ}
    (u : Fin K → ℂ) (i : Fin K) (j : Fin 1) :
    complexColumnMatrix u i j = u i :=
  rfl

def complexColumnNormSq {K : ℕ} (u : Fin K → ℂ) : ℝ :=
  ∑ i, Complex.normSq (u i)

/-- The exact scalar-column Schur determinant identity.  The final `Fin 1`
determinant has been reduced to its unique scalar entry. -/
theorem det_one_sub_appended_column_schur_scalar
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (x : Fin K → ℂ) [Invertible (1 - A.conjTranspose * A)] :
    Matrix.det
        (1 -
          (Matrix.fromCols A (complexColumnMatrix x)).conjTranspose *
            Matrix.fromCols A (complexColumnMatrix x)) =
      Matrix.det (1 - A.conjTranspose * A) *
        ((show Matrix (Fin 1) (Fin 1) ℂ from
            (1 - (complexColumnMatrix x).conjTranspose *
                complexColumnMatrix x) -
              ((complexColumnMatrix x).conjTranspose * A) *
                ⅟(1 - A.conjTranspose * A) *
                  (A.conjTranspose * complexColumnMatrix x)) 0 0) := by
  simpa only [Matrix.det_fin_one] using
    (det_one_sub_conjTranspose_mul_fromCols_schur_clean
      A (complexColumnMatrix x))

/-- The determinant of the rank-one unit-ball defect is `1 - ‖u‖²`. -/
theorem det_one_sub_complexColumnMatrix_outer
    {K : ℕ} (u : Fin K → ℂ) :
    Matrix.det
        (1 - complexColumnMatrix u *
          (complexColumnMatrix u).conjTranspose) =
      ((1 - complexColumnNormSq u : ℝ) : ℂ) := by
  rw [Matrix.det_one_sub_mul_comm
      (complexColumnMatrix u) (complexColumnMatrix u).conjTranspose,
    Matrix.det_fin_one]
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, complexColumnMatrix_apply,
    Fin.isValue, if_true]
  have hsum : (∑ i, star (u i) * u i) =
      (((complexColumnNormSq u : ℝ) : ℂ)) := by
    calc
      ∑ i, star (u i) * u i =
          ∑ i, ((Complex.normSq (u i) : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro i _
            exact (Complex.normSq_eq_conj_mul_self (z := u i)).symm
      _ = (((∑ i, Complex.normSq (u i) : ℝ) : ℂ)) := by
            exact (Complex.ofReal_sum Finset.univ
              (fun i ↦ Complex.normSq (u i))).symm
      _ = (((complexColumnNormSq u : ℝ) : ℂ)) := by rfl
  rw [hsum]
  push_cast
  rfl

/-- Scalar form of the appended-column determinant separation. -/
theorem det_one_sub_appended_sqrtColumn_eq_defect_mul_one_sub_normSq
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef)
    (u : Fin K → ℂ) :
    Matrix.det
        (1 -
          (Matrix.fromCols A
            (haarCornerDefectSqrt A * complexColumnMatrix u)).conjTranspose *
          Matrix.fromCols A
            (haarCornerDefectSqrt A * complexColumnMatrix u)) =
      Matrix.det (haarCornerLeftDefect A) *
        ((1 - complexColumnNormSq u : ℝ) : ℂ) := by
  rw [det_one_sub_appended_sqrtColumn_factorization A hA,
    det_one_sub_complexColumnMatrix_outer]

/-! ## Exponent and normalizer recursion -/

/-- The Jacobian contributes exactly one extra power of the old defect
determinant in the stable matrix-ball range. -/
theorem jacobian_mul_detFactor_pow_succColumn
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M)
    (d q : ℝ) :
    d * (d * q) ^ (M - K - (N + 1)) =
      d ^ (M - K - N) * q ^ (M - K - (N + 1)) := by
  rw [mul_pow]
  have hexp : M - K - N = (M - K - (N + 1)) + 1 := by
    omega
  rw [hexp, pow_succ]
  ring

/-- Exact one-column recursion of Jiang's displayed factorial normalizer. -/
@[simp]
theorem jiangUnscaledTallHaarCornerNormalizer_zero_column
    (M K : ℕ) :
    jiangUnscaledTallHaarCornerNormalizer M K 0 = 1 := by
  simp [jiangUnscaledTallHaarCornerNormalizer]

/-- Exact one-column recursion of Jiang's displayed factorial normalizer. -/
theorem jiangUnscaledTallHaarCornerNormalizer_succ_column
    (M K N : ℕ) :
    jiangUnscaledTallHaarCornerNormalizer M K (N + 1) =
      jiangUnscaledTallHaarCornerNormalizer M K N *
        (Real.pi ^ K)⁻¹ *
        (((Nat.factorial (M - (N + 1)) : ℕ) : ℝ) /
          ((Nat.factorial (M - (N + 1) - K) : ℕ) : ℝ)) := by
  unfold jiangUnscaledTallHaarCornerNormalizer
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [Nat.mul_succ, pow_add, _root_.mul_inv_rev]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
