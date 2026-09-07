import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerSupportFactorization
import LogdetLean.GramHafnian.UltimateHiding.Sparse.H19HaarCornerBaseColumn

/-!
# Support and pointwise density balance for Haar-corner column induction

For an old corner `A` with positive-definite left defect, the square-root
successor coordinate

`[A, (I - A A*)^(1/2) u]`

lies in Jiang's successor support exactly when `u` lies in the closed complex
unit ball.  The same factorization, together with the elementary successor
normalizer identity, gives the pointwise density/Jacobian balance used in the
column induction.
-/

open Matrix
open scoped ComplexOrder MatrixOrder BigOperators ENNReal

namespace LogdetLean.GramHafnian.UltimateHiding.Sparse

noncomputable section

/-- The left defect of the square-root appended corner is an invertible
congruence of the rank-one unit-ball defect. -/
theorem haarCornerLeftDefect_haarCornerAppendSqrtColumn_eq
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef)
    (u : Fin K → ℂ) :
    haarCornerLeftDefect (haarCornerAppendSqrtColumn (A, u)) =
      haarCornerDefectSqrt A *
        (1 - complexColumnMatrix u *
          (complexColumnMatrix u).conjTranspose) *
        haarCornerDefectSqrt A := by
  let C : Matrix (Fin K) (Fin N ⊕ Fin 1) ℂ :=
    Matrix.fromCols A
      (haarCornerDefectSqrt A * complexColumnMatrix u)
  have hgram :
      haarCornerAppendSqrtColumn (A, u) *
          (haarCornerAppendSqrtColumn (A, u)).conjTranspose =
        C * C.conjTranspose := by
    rw [haarCornerAppendSqrtColumn]
    rw [Matrix.conjTranspose_reindex]
    simpa [C] using
      (Matrix.reindexLinearEquiv_mul (R := ℂ) (A := ℂ)
        (Equiv.refl (Fin K))
        (finSumFinEquiv : Fin N ⊕ Fin 1 ≃ Fin (N + 1))
        (Equiv.refl (Fin K)) C C.conjTranspose)
  rw [haarCornerLeftDefect, hgram]
  change
    1 -
        Matrix.fromCols A
          (haarCornerDefectSqrt A * complexColumnMatrix u) *
          (Matrix.fromCols A
            (haarCornerDefectSqrt A * complexColumnMatrix u)).conjTranspose = _
  rw [fromCols_mul_conjTranspose_eq_add]
  calc
    1 -
          (A * A.conjTranspose +
            (haarCornerDefectSqrt A * complexColumnMatrix u) *
              (haarCornerDefectSqrt A * complexColumnMatrix u).conjTranspose) =
        haarCornerLeftDefect A -
          (haarCornerDefectSqrt A * complexColumnMatrix u) *
            (haarCornerDefectSqrt A * complexColumnMatrix u).conjTranspose := by
      simp only [haarCornerLeftDefect]
      noncomm_ring
    _ = _ := haarCorner_rankUpdate_sqrt_factorization A hA
      (complexColumnMatrix u)

/-- Exact successor-support reduction: under a positive-definite old defect,
Jiang support of the appended corner is precisely the closed unit-ball
condition on the normalized successor column. -/
theorem jiangUnscaledTallHaarCornerSupport_haarCornerAppendSqrtColumn_iff
    {K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef)
    (u : Fin K → ℂ) :
    jiangUnscaledTallHaarCornerSupport
        (haarCornerAppendSqrtColumn (A, u)) ↔
      complexColumnNormSq u ≤ 1 := by
  rw [jiangUnscaledTallHaarCornerSupport_iff_posSemidef]
  rw [posSemidef_one_sub_conjTranspose_mul_iff_one_sub_mul_conjTranspose]
  rw [show
    1 - haarCornerAppendSqrtColumn (A, u) *
        (haarCornerAppendSqrtColumn (A, u)).conjTranspose =
      haarCornerLeftDefect (haarCornerAppendSqrtColumn (A, u)) by rfl]
  rw [haarCornerLeftDefect_haarCornerAppendSqrtColumn_eq A hA u]
  have hcongr :=
    (haarCornerDefectSqrt_isUnit A hA).posSemidef_star_right_conjugate_iff
      (x := 1 - complexColumnMatrix u *
        (complexColumnMatrix u).conjTranspose)
  rw [show star (haarCornerDefectSqrt A) =
      haarCornerDefectSqrt A by
    rw [Matrix.star_eq_conjTranspose,
      (haarCornerDefectSqrt_isHermitian A).eq]] at hcongr
  exact hcongr.trans
    (posSemidef_one_sub_complexColumnMatrix_outer_iff u)

/-- The Euclidean squared norm used by the sphere-coordinate density is the
literal coordinate sum `complexColumnNormSq`. -/
theorem h19BaseColumn_euclideanNormSq_eq_complexColumnNormSq
    (K : ℕ) (u : Fin K → ℂ) :
    ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin K))‖ ^ 2 =
      complexColumnNormSq u := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold complexColumnNormSq
  apply Finset.sum_congr rfl
  intro i _
  exact (Complex.normSq_eq_norm_sq (u i)).symm

/-- The base-column factorial normalizer is exactly the Jiang successor
fiber normalizer in the admissible successor-size regime. -/
theorem h19BaseColumnNormalizer_eq_jiangHaarCornerSuccFiberNormalizer
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M) :
    h19BaseColumnNormalizer K (M - K - N) =
      jiangHaarCornerSuccFiberNormalizer M K N := by
  have hnum : K + (M - K - N) - 1 = M - (N + 1) := by omega
  have hden : M - K - N - 1 = M - (N + 1) - K := by omega
  unfold h19BaseColumnNormalizer jiangHaarCornerSuccFiberNormalizer
  rw [hnum, hden]
  ring

/-- With one extra residual dimension, the explicit open-ball density from
the Haar-column theorem agrees pointwise with the closed-ball Jiang fiber
density.  Strictness makes both sides vanish on the unit-sphere boundary. -/
theorem h19BaseColumnRawPDF_eq_jiangHaarCornerSuccFiberPDF
    {M K N : ℕ} (hsize : K + (N + 1) < M) (u : Fin K → ℂ) :
    h19BaseColumnRawPDF K (M - K - N) u =
      jiangHaarCornerSuccFiberPDF M K N u := by
  have hsize' : K + (N + 1) ≤ M := Nat.le_of_lt hsize
  have hexp : M - K - N - 1 = M - K - (N + 1) := by omega
  have hpowpos : 0 < M - K - (N + 1) := by omega
  have hnormsq := h19BaseColumn_euclideanNormSq_eq_complexColumnNormSq K u
  have hnorm_nonneg :
      0 ≤ ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin K))‖ :=
    norm_nonneg _
  have hnorm_iff :
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Fin K))‖ < 1 ↔
        complexColumnNormSq u < 1 := by
    rw [← hnormsq]
    constructor <;> intro h <;> nlinarith
  unfold h19BaseColumnRawPDF h19BaseColumnVectorPDF
  unfold jiangHaarCornerSuccFiberPDF
  rw [h19BaseColumnNormalizer_eq_jiangHaarCornerSuccFiberNormalizer hsize',
    hexp]
  by_cases hu : complexColumnNormSq u < 1
  · rw [if_pos (hnorm_iff.mpr hu), if_pos hu.le]
    rw [hnormsq]
  · rw [if_neg (not_congr hnorm_iff |>.mpr hu)]
    by_cases hle : complexColumnNormSq u ≤ 1
    · have heq : complexColumnNormSq u = 1 :=
        le_antisymm hle (le_of_not_gt hu)
      rw [if_pos hle, heq]
      simp [Nat.ne_of_gt hpowpos]
    · rw [if_neg hle]

private theorem jiangUnscaledTallHaarCornerNormalizer_pos
    (M K N : ℕ) :
    0 < jiangUnscaledTallHaarCornerNormalizer M K N := by
  unfold jiangUnscaledTallHaarCornerNormalizer
  positivity

/-- A positive-definite left defect puts the point strictly inside Jiang's
old support, so the old density is nonzero. -/
theorem jiangUnscaledTallHaarCornerPDF_ne_zero_of_leftDefect_posDef
    {M K N : ℕ} (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) :
    jiangUnscaledTallHaarCornerPDF M K N A ≠ 0 := by
  have hold : jiangUnscaledTallHaarCornerSupport A := by
    rw [jiangUnscaledTallHaarCornerSupport_iff_posSemidef]
    exact
      (posSemidef_one_sub_conjTranspose_mul_iff_one_sub_mul_conjTranspose A).mpr
        hA.posSemidef
  have hdet :
      0 < (Matrix.det (1 - A.conjTranspose * A)).re := by
    rw [det_one_sub_conjTranspose_mul_eq_det_one_sub_mul_conjTranspose]
    exact (RCLike.pos_iff.mp hA.det_pos).1
  rw [jiangUnscaledTallHaarCornerPDF, if_pos hold]
  exact ne_of_gt (ENNReal.ofReal_pos.mpr
    (mul_pos (jiangUnscaledTallHaarCornerNormalizer_pos M K N)
      (pow_pos hdet _)))

/-- Pointwise Jiang density balance for the closed-ball successor fiber.
The factor `det(I-AA*)` is the real Jacobian of
`u ↦ (I-AA*)^(1/2)u`. -/
theorem jiangUnscaledTallHaarCornerPDF_haarCornerAppendSqrtColumn_balance
    {M K N : ℕ} (hsize : K + (N + 1) ≤ M)
    (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) (u : Fin K → ℂ) :
    jiangUnscaledTallHaarCornerPDF M K N A *
        jiangHaarCornerSuccFiberPDF M K N u =
      ENNReal.ofReal (haarCornerLeftDefect A).det.re *
        jiangUnscaledTallHaarCornerPDF M K (N + 1)
          (haarCornerAppendSqrtColumn (A, u)) := by
  let d : ℝ := (haarCornerLeftDefect A).det.re
  let q : ℝ := 1 - complexColumnNormSq u
  have hd : 0 < d := (RCLike.pos_iff.mp hA.det_pos).1
  have hold : jiangUnscaledTallHaarCornerSupport A := by
    rw [jiangUnscaledTallHaarCornerSupport_iff_posSemidef]
    exact
      (posSemidef_one_sub_conjTranspose_mul_iff_one_sub_mul_conjTranspose A).mpr
        hA.posSemidef
  by_cases hu : complexColumnNormSq u ≤ 1
  · have hq : 0 ≤ q := sub_nonneg.mpr hu
    have hnew : jiangUnscaledTallHaarCornerSupport
        (haarCornerAppendSqrtColumn (A, u)) :=
      (jiangUnscaledTallHaarCornerSupport_haarCornerAppendSqrtColumn_iff
        A hA u).mpr hu
    have hdet :
        (Matrix.det (1 -
          (haarCornerAppendSqrtColumn (A, u)).conjTranspose *
            haarCornerAppendSqrtColumn (A, u))).re = d * q := by
      rw [det_one_sub_haarCornerAppendSqrtColumn_eq A hA u]
      dsimp only [d, q]
      rw [Complex.mul_re]
      have him : (haarCornerLeftDefect A).det.im = 0 :=
        Complex.conj_eq_iff_im.mp
          ((Matrix.det_conjTranspose (haarCornerLeftDefect A)).symm.trans
            (congrArg Matrix.det hA.isHermitian))
      simp [him]
    rw [jiangUnscaledTallHaarCornerPDF,
      jiangHaarCornerSuccFiberPDF,
      jiangUnscaledTallHaarCornerPDF,
      if_pos hold, if_pos hu, if_pos hnew, hdet]
    rw [det_one_sub_conjTranspose_mul_eq_det_one_sub_mul_conjTranspose]
    change ENNReal.ofReal
        (jiangUnscaledTallHaarCornerNormalizer M K N *
          d ^ (M - K - N)) *
        ENNReal.ofReal
          (jiangHaarCornerSuccFiberNormalizer M K N *
            q ^ (M - K - (N + 1))) =
      ENNReal.ofReal d *
        ENNReal.ofReal
          (jiangUnscaledTallHaarCornerNormalizer M K (N + 1) *
            (d * q) ^ (M - K - (N + 1)))
    rw [← ENNReal.ofReal_mul (mul_nonneg
      (jiangUnscaledTallHaarCornerNormalizer_pos M K N).le
      (pow_nonneg hd.le _))]
    rw [← ENNReal.ofReal_mul hd.le]
    exact congrArg ENNReal.ofReal
      (jiang_succ_normalizer_det_power_balance hsize d q)
  · have hnew : ¬ jiangUnscaledTallHaarCornerSupport
        (haarCornerAppendSqrtColumn (A, u)) := by
      simpa [
        jiangUnscaledTallHaarCornerSupport_haarCornerAppendSqrtColumn_iff
          A hA u] using hu
    simp [jiangHaarCornerSuccFiberPDF, hu,
      jiangUnscaledTallHaarCornerPDF, hnew]

/-- The same pointwise density/Jacobian balance in terms of the explicit
top-coordinate Haar-column density used by the successor representation. -/
theorem jiangUnscaledTallHaarCornerPDF_haarCornerAppendSqrtColumn_raw_balance
    {M K N : ℕ} (hsize : K + (N + 1) < M)
    (A : Matrix (Fin K) (Fin N) ℂ)
    (hA : (haarCornerLeftDefect A).PosDef) (u : Fin K → ℂ) :
    jiangUnscaledTallHaarCornerPDF M K N A *
        h19BaseColumnRawPDF K (M - K - N) u =
      ENNReal.ofReal (haarCornerLeftDefect A).det.re *
        jiangUnscaledTallHaarCornerPDF M K (N + 1)
          (haarCornerAppendSqrtColumn (A, u)) := by
  rw [h19BaseColumnRawPDF_eq_jiangHaarCornerSuccFiberPDF hsize u]
  exact
    jiangUnscaledTallHaarCornerPDF_haarCornerAppendSqrtColumn_balance
      (Nat.le_of_lt hsize) A hA u

end

end LogdetLean.GramHafnian.UltimateHiding.Sparse
