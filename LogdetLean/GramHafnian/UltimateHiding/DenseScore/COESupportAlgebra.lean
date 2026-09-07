import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalCOEExternal
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# Deterministic COE support algebra

This file derives the `R20` identities used by the centered quadratic score
from only the literal COE support facts

* `C` is complex symmetric;
* `I-CᴴC` is positive definite.

In particular, no trace identity, score estimate, moment estimate,
total-variation estimate, or hiding conclusion is assumed here.  The key
matrix facts are the push-through identity
`(I-CCᴴ)⁻¹C=C(I-CᴴC)⁻¹` and
`TTᴴ=Z(I+Z)`.
-/

open scoped BigOperators ComplexConjugate ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- `W=I+Y/c`, written this way so the `R30` substitution is transparent. -/
def concreteCOEWMatrix (N K : ℕ) (A : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  1 + ((((concreteCOEExponent N K)⁻¹ : ℝ) : ℂ)) •
    concreteCOEY N K A

/-- `R=sqrt(c) T` in the exact centered likelihood calculus. -/
def concreteCOERMatrix (N K : ℕ) (A : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  (((Real.sqrt (concreteCOEExponent N K) : ℝ) : ℂ)) • concreteCOET K A

private def supportH {N : ℕ} (C : ConcreteMatrixState N) :=
  1 - C.conjTranspose * C

private def supportG {N : ℕ} (C : ConcreteMatrixState N) :=
  1 - C * C.conjTranspose

private theorem supportG_det_eq_supportH_det {N : ℕ}
    (C : ConcreteMatrixState N) :
    (supportG C).det = (supportH C).det := by
  exact Matrix.det_one_sub_mul_comm C C.conjTranspose

private theorem supportG_mul_C_eq_C_mul_supportH {N : ℕ}
    (C : ConcreteMatrixState N) :
    supportG C * C = C * supportH C := by
  unfold supportG supportH
  noncomm_ring

/-- Push-through identity on the open matrix ball. -/
private theorem support_inv_push_through {N : ℕ}
    (C : ConcreteMatrixState N) (hH : (supportH C).PosDef) :
    (supportG C)⁻¹ * C = C * (supportH C)⁻¹ := by
  letI : Invertible (supportH C) := hH.isUnit.invertible
  have hGunit : IsUnit (supportG C) := by
    rw [Matrix.isUnit_iff_isUnit_det, supportG_det_eq_supportH_det]
    exact (Matrix.isUnit_iff_isUnit_det (supportH C)).mp hH.isUnit
  letI : Invertible (supportG C) := hGunit.invertible
  apply (Matrix.inv_mul_eq_iff_eq_mul_of_invertible (supportG C) C
    (C * (supportH C)⁻¹)).2
  rw [← Matrix.mul_assoc, supportG_mul_C_eq_C_mul_supportH,
    Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]

private theorem supportG_transpose_eq_supportH {N : ℕ}
    (C : ConcreteMatrixState N) (hC : C.IsSymm) :
    (supportG C).transpose = supportH C := by
  unfold supportG supportH
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    hC.eq, hC.conjTranspose.eq]

private theorem supportT_isSymm {N : ℕ} (C : ConcreteMatrixState N)
    (hC : C.IsSymm) (hH : (supportH C).PosDef) :
    ((supportG C)⁻¹ * C).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv,
    supportG_transpose_eq_supportH C hC, hC.eq]
  exact (support_inv_push_through C hH).symm

private theorem supportZ_isHermitian {N : ℕ} (C : ConcreteMatrixState N)
    (hH : (supportH C).PosDef) :
    (C * (supportH C)⁻¹ * C.conjTranspose).IsHermitian := by
  exact Matrix.isHermitian_mul_mul_conjTranspose C hH.isHermitian.inv

private theorem real_smul_supportZ_isHermitian {N : ℕ}
    (C : ConcreteMatrixState N) (hH : (supportH C).PosDef) (c : ℝ) :
    (((c : ℝ) : ℂ) •
      (C * (supportH C)⁻¹ * C.conjTranspose)).IsHermitian := by
  apply (supportZ_isHermitian C hH).smul
  change star (c : ℂ) = (c : ℂ)
  simp

private theorem trace_im_eq_zero_of_isHermitian {N : ℕ}
    {A : ConcreteMatrixState N} (hA : A.IsHermitian) :
    (Matrix.trace A).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have ht := congrArg Matrix.trace hA.eq
  rw [Matrix.trace_conjTranspose] at ht
  exact ht

private theorem trace_scaled_supportZ_im_zero {N : ℕ}
    (C : ConcreteMatrixState N) (hH : (supportH C).PosDef) (c : ℝ) :
    (Matrix.trace (((c : ℝ) : ℂ) •
      (C * (supportH C)⁻¹ * C.conjTranspose))).im = 0 :=
  trace_im_eq_zero_of_isHermitian
    (real_smul_supportZ_isHermitian C hH c)

private theorem trace_scaled_supportZ_sq_im_zero {N : ℕ}
    (C : ConcreteMatrixState N) (hH : (supportH C).PosDef) (c : ℝ) :
    (Matrix.trace (
      (((c : ℝ) : ℂ) • (C * (supportH C)⁻¹ * C.conjTranspose)) *
      (((c : ℝ) : ℂ) •
        (C * (supportH C)⁻¹ * C.conjTranspose)))).im = 0 := by
  apply trace_im_eq_zero_of_isHermitian
  simpa only [pow_two] using
    (real_smul_supportZ_isHermitian C hH c).pow 2

private theorem supportG_isHermitian {N : ℕ}
    (C : ConcreteMatrixState N) : (supportG C).IsHermitian := by
  exact Matrix.isHermitian_one.sub
    (Matrix.isHermitian_mul_conjTranspose_self C)

private theorem supportG_inv_eq_one_add_Z {N : ℕ}
    (C : ConcreteMatrixState N) (hH : (supportH C).PosDef) :
    (supportG C)⁻¹ =
      1 + C * (supportH C)⁻¹ * C.conjTranspose := by
  letI : Invertible (supportH C) := hH.isUnit.invertible
  have hGunit : IsUnit (supportG C) := by
    rw [Matrix.isUnit_iff_isUnit_det, supportG_det_eq_supportH_det]
    exact (Matrix.isUnit_iff_isUnit_det (supportH C)).mp hH.isUnit
  letI : Invertible (supportG C) := hGunit.invertible
  have hinvOne :=
    (Matrix.inv_mul_eq_iff_eq_mul_of_invertible (supportG C) 1
      (1 + C * (supportH C)⁻¹ * C.conjTranspose)).2 (by
        rw [Matrix.mul_add, Matrix.mul_one]
        rw [show supportG C *
            (C * (supportH C)⁻¹ * C.conjTranspose) =
              C * C.conjTranspose by
          calc
            supportG C *
                (C * (supportH C)⁻¹ * C.conjTranspose) =
                (supportG C * C) * (supportH C)⁻¹ *
                  C.conjTranspose := by noncomm_ring
            _ = (C * supportH C) * (supportH C)⁻¹ *
                  C.conjTranspose := by
              rw [supportG_mul_C_eq_C_mul_supportH]
            _ = C * ((supportH C) * (supportH C)⁻¹) *
                  C.conjTranspose := by noncomm_ring
            _ = C * C.conjTranspose := by
              rw [Matrix.mul_inv_of_invertible, Matrix.mul_one]]
        unfold supportG
        noncomm_ring)
  calc
    (supportG C)⁻¹ = (supportG C)⁻¹ * 1 := (Matrix.mul_one _).symm
    _ = _ := hinvOne

/-- `TTᴴ=Z(I+Z)` on the open matrix ball. -/
private theorem supportT_mul_conjTranspose_eq_Z_mul_one_add_Z {N : ℕ}
    (C : ConcreteMatrixState N) (hH : (supportH C).PosDef) :
    ((supportG C)⁻¹ * C) *
        ((supportG C)⁻¹ * C).conjTranspose =
      (C * (supportH C)⁻¹ * C.conjTranspose) *
        (1 + C * (supportH C)⁻¹ * C.conjTranspose) := by
  letI : Invertible (supportH C) := hH.isUnit.invertible
  have hGunit : IsUnit (supportG C) := by
    rw [Matrix.isUnit_iff_isUnit_det, supportG_det_eq_supportH_det]
    exact (Matrix.isUnit_iff_isUnit_det (supportH C)).mp hH.isUnit
  letI : Invertible (supportG C) := hGunit.invertible
  have hGinvH : ((supportG C)⁻¹).IsHermitian :=
    (supportG_isHermitian C).inv
  calc
    ((supportG C)⁻¹ * C) *
        ((supportG C)⁻¹ * C).conjTranspose =
        ((supportG C)⁻¹ * C * C.conjTranspose) *
          (supportG C)⁻¹ := by
      rw [Matrix.conjTranspose_mul, hGinvH.eq]
      noncomm_ring
    _ = (C * (supportH C)⁻¹ * C.conjTranspose) *
          (supportG C)⁻¹ := by
      rw [show (supportG C)⁻¹ * C * C.conjTranspose =
          C * (supportH C)⁻¹ * C.conjTranspose by
        rw [support_inv_push_through C hH]]
    _ = _ := by rw [supportG_inv_eq_one_add_Z C hH]

/-- The unscaled `Z` statistic is Hermitian on the open COE matrix ball. -/
theorem concreteCOEZ_isHermitian_of_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (concreteCOEZ K A).IsHermitian := by
  let C := unscaleCOECorner K A
  have hH : (supportH C).PosDef := by
    unfold coeCornerSupport at hsupport
    change (1 - C.conjTranspose * C).PosDef
    simpa only [C] using hsupport
  unfold concreteCOEZ
  dsimp only
  exact supportZ_isHermitian C hH

/-- The unscaled bilinear matrix `T` is complex symmetric whenever the COE
corner itself is symmetric. -/
theorem concreteCOET_isSymm_of_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (concreteCOET K A).IsSymm := by
  let C := unscaleCOECorner K A
  have hH : (supportH C).PosDef := by
    unfold coeCornerSupport at hsupport
    change (1 - C.conjTranspose * C).PosDef
    simpa only [C] using hsupport
  have hC : C.IsSymm := by simpa only [C] using hsymm
  unfold concreteCOET
  dsimp only
  exact supportT_isSymm C hC hH

/-- The unscaled bilinear matrix satisfies `TTᴴ=Z(I+Z)` on the open COE
matrix ball.  This is the public support-algebra form used by the cubic
projective contraction; it contains no density or moment input. -/
theorem concreteCOET_mul_conjTranspose_eq_Z_mul_one_add_Z
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCOET K A * (concreteCOET K A).conjTranspose =
      concreteCOEZ K A * (1 + concreteCOEZ K A) := by
  let C := unscaleCOECorner K A
  have hH : (supportH C).PosDef := by
    unfold coeCornerSupport at hsupport
    change (1 - C.conjTranspose * C).PosDef
    simpa only [C] using hsupport
  unfold concreteCOET concreteCOEZ
  dsimp only
  exact supportT_mul_conjTranspose_eq_Z_mul_one_add_Z C hH

/-- Literal dictionary for the paper's `Omega = I + Z` notation.  On a
nonzero exponent, the likelihood-calculus matrix `W = I + Y / c` is exactly
`I + Z`, because `Y = c Z`. -/
theorem concreteCOEWMatrix_eq_one_add_Z
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0) :
    concreteCOEWMatrix N K A = 1 + concreteCOEZ K A := by
  unfold concreteCOEWMatrix concreteCOEY
  rw [smul_smul]
  have hscalar :
      (((concreteCOEExponent N K)⁻¹ : ℝ) : ℂ) *
          ((concreteCOEExponent N K : ℝ) : ℂ) = 1 := by
    norm_cast
    exact inv_mul_cancel₀ hc
  rw [hscalar, one_smul]

/-- Literal dictionary for the paper's
`R = sqrt(c) (I + Z) C` notation on the open matrix ball. -/
theorem concreteCOERMatrix_eq_sqrt_exponent_smul_one_add_Z_mul_unscale
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCOERMatrix N K A =
      (((Real.sqrt (concreteCOEExponent N K) : ℝ) : ℂ)) •
        ((1 + concreteCOEZ K A) * unscaleCOECorner K A) := by
  let C := unscaleCOECorner K A
  have hH : (supportH C).PosDef := by
    unfold coeCornerSupport at hsupport
    change (1 - C.conjTranspose * C).PosDef
    simpa only [C] using hsupport
  unfold concreteCOERMatrix concreteCOET concreteCOEZ
  change (((Real.sqrt (concreteCOEExponent N K) : ℝ) : ℂ)) •
      ((supportG C)⁻¹ * C) =
    (((Real.sqrt (concreteCOEExponent N K) : ℝ) : ℂ)) •
      ((1 + C * (supportH C)⁻¹ * C.conjTranspose) * C)
  rw [supportG_inv_eq_one_add_Z C hH]

theorem concreteCOEWMatrix_trace_re
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0) :
    (Matrix.trace (concreteCOEWMatrix N K A)).re =
      (N : ℝ) + concreteCOETraceOne N K A /
        concreteCOEExponent N K := by
  unfold concreteCOEWMatrix concreteCOETraceOne concreteRealTrace
  rw [Matrix.trace_add, Matrix.trace_smul]
  simp only [Matrix.trace_one, Complex.add_re, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Fintype.card_fin]
  norm_num
  field_simp [hc]

theorem concreteCOEWMatrix_mul_Y_trace_re
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hc : concreteCOEExponent N K ≠ 0) :
    (Matrix.trace
      (concreteCOEWMatrix N K A * concreteCOEY N K A)).re =
      concreteCOETraceOne N K A + concreteCOETraceTwo N K A /
        concreteCOEExponent N K := by
  unfold concreteCOEWMatrix concreteCOETraceOne concreteCOETraceTwo
    concreteRealTrace
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.trace_add,
    Matrix.trace_smul]
  simp only [Complex.add_re, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp [hc]

private theorem scaled_supportT_mul_conjTranspose_eq_scaled_Z_mul_one_add_Z
    {N : ℕ} (C : ConcreteMatrixState N)
    (hH : (supportH C).PosDef) (c : ℝ) (hc : 0 ≤ c) :
    ((((Real.sqrt c : ℝ) : ℂ)) • ((supportG C)⁻¹ * C)) *
        (((((Real.sqrt c : ℝ) : ℂ)) •
          ((supportG C)⁻¹ * C)).conjTranspose) =
      (((c : ℝ) : ℂ) •
        (C * (supportH C)⁻¹ * C.conjTranspose)) *
        (1 + C * (supportH C)⁻¹ * C.conjTranspose) := by
  have hstar : star (((Real.sqrt c : ℝ) : ℂ)) =
      (((Real.sqrt c : ℝ) : ℂ)) := by simp
  rw [Matrix.conjTranspose_smul]
  rw [hstar, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show ((Real.sqrt c : ℂ) * (Real.sqrt c : ℂ)) = (c : ℂ) by
    norm_cast
    simpa only [pow_two] using Real.sq_sqrt hc]
  rw [supportT_mul_conjTranspose_eq_Z_mul_one_add_Z C hH]
  rw [Matrix.smul_mul]

theorem concreteCOERMatrix_mul_conjTranspose_eq_Y_mul_W
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hcpos : 0 < concreteCOEExponent N K)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCOERMatrix N K A *
        (concreteCOERMatrix N K A).conjTranspose =
      concreteCOEY N K A * concreteCOEWMatrix N K A := by
  let C := unscaleCOECorner K A
  let c := concreteCOEExponent N K
  have hH : (supportH C).PosDef := by
    unfold coeCornerSupport at hsupport
    change (1 - C.conjTranspose * C).PosDef
    simpa only [C] using hsupport
  have hc : c ≠ 0 := ne_of_gt hcpos
  unfold concreteCOERMatrix concreteCOET concreteCOEY concreteCOEZ
    concreteCOEWMatrix
  dsimp only
  change ((((Real.sqrt c : ℝ) : ℂ)) • ((supportG C)⁻¹ * C)) *
        (((((Real.sqrt c : ℝ) : ℂ)) •
          ((supportG C)⁻¹ * C)).conjTranspose) =
      (((c : ℝ) : ℂ) •
        (C * (supportH C)⁻¹ * C.conjTranspose)) *
        (1 + (((c⁻¹ : ℝ) : ℂ)) •
          (((c : ℝ) : ℂ) •
            (C * (supportH C)⁻¹ * C.conjTranspose)))
  rw [show (((c⁻¹ : ℝ) : ℂ)) •
          (((c : ℝ) : ℂ) •
            (C * (supportH C)⁻¹ * C.conjTranspose)) =
        C * (supportH C)⁻¹ * C.conjTranspose by
    simp only [smul_smul]
    rw [show (((c⁻¹ : ℝ) : ℂ) * ((c : ℝ) : ℂ)) = 1 by
      norm_cast
      exact inv_mul_cancel₀ hc, one_smul]]
  exact scaled_supportT_mul_conjTranspose_eq_scaled_Z_mul_one_add_Z
    C hH c hcpos.le

/-- Literal paper form `R Rᴴ = Y Omega`, with `Omega = I + Z`. -/
theorem concreteCOERMatrix_mul_conjTranspose_eq_Y_mul_one_add_Z
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hcpos : 0 < concreteCOEExponent N K)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCOERMatrix N K A *
        (concreteCOERMatrix N K A).conjTranspose =
      concreteCOEY N K A * (1 + concreteCOEZ K A) := by
  rw [concreteCOERMatrix_mul_conjTranspose_eq_Y_mul_W A hcpos hsupport,
    concreteCOEWMatrix_eq_one_add_Z A hcpos.ne']

theorem concreteCOERMatrix_isSymm_of_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (concreteCOERMatrix N K A).IsSymm := by
  let C := unscaleCOECorner K A
  have hH : (supportH C).PosDef := by
    unfold coeCornerSupport at hsupport
    change (1 - C.conjTranspose * C).PosDef
    simpa only [C] using hsupport
  have hC : C.IsSymm := by simpa only [C] using hsymm
  unfold concreteCOERMatrix concreteCOET
  dsimp only
  exact (supportT_isSymm C hC hH).smul _

theorem concreteCOEY_trace_im_eq_zero_of_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (Matrix.trace (concreteCOEY N K A)).im = 0 := by
  let C := unscaleCOECorner K A
  have hH : (supportH C).PosDef := by
    unfold coeCornerSupport at hsupport
    change (1 - C.conjTranspose * C).PosDef
    simpa only [C] using hsupport
  unfold concreteCOEY concreteCOEZ
  dsimp only
  exact trace_scaled_supportZ_im_zero C hH (concreteCOEExponent N K)

/-- `Y=cZ` is Hermitian on the open COE matrix-ball support. -/
theorem concreteCOEY_isHermitian_of_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (concreteCOEY N K A).IsHermitian := by
  let C := unscaleCOECorner K A
  have hH : (supportH C).PosDef := by
    unfold coeCornerSupport at hsupport
    change (1 - C.conjTranspose * C).PosDef
    simpa only [C] using hsupport
  unfold concreteCOEY concreteCOEZ
  dsimp only
  exact real_smul_supportZ_isHermitian C hH (concreteCOEExponent N K)

theorem concreteCOEY_sq_trace_im_eq_zero_of_support
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (Matrix.trace
      (concreteCOEY N K A * concreteCOEY N K A)).im = 0 := by
  let C := unscaleCOECorner K A
  have hH : (supportH C).PosDef := by
    unfold coeCornerSupport at hsupport
    change (1 - C.conjTranspose * C).PosDef
    simpa only [C] using hsupport
  unfold concreteCOEY concreteCOEZ
  dsimp only
  exact trace_scaled_supportZ_sq_im_zero C hH
    (concreteCOEExponent N K)

theorem concreteCOERMatrix_sq_trace_re
    {N K : ℕ} (A : ConcreteMatrixState N)
    (hcpos : 0 < concreteCOEExponent N K)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    (Matrix.trace
      (concreteCOERMatrix N K A *
        (concreteCOERMatrix N K A).conjTranspose)).re =
      concreteCOETraceOne N K A + concreteCOETraceTwo N K A /
        concreteCOEExponent N K := by
  rw [concreteCOERMatrix_mul_conjTranspose_eq_Y_mul_W A hcpos hsupport]
  rw [show concreteCOEY N K A * concreteCOEWMatrix N K A =
      concreteCOEWMatrix N K A * concreteCOEY N K A by
    unfold concreteCOEWMatrix
    noncomm_ring]
  exact concreteCOEWMatrix_mul_Y_trace_re A (ne_of_gt hcpos)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
