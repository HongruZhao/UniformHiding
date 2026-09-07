import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeSupportOperatorBound
import Mathlib.Tactic

/-!
# Support Gram identities for the H13 bilinear factors

The projective factorization of the mixed H13 words is useful only after its
matrix arguments are put into the symmetric `R, Rᴴ` form required by the
bilinear projective estimate.  This file records that deterministic support
algebra.  In particular, all four symmetric matrices that occur in the H13
mixed words have Gram traces which are polynomials of degree at most four in
the positive support statistic `Z`.
-/

open Matrix
open scoped ComplexOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 2400000

/-- The unscaled H13 output statistic is positive semidefinite on support. -/
theorem h13LedgerZ_posSemidef
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (h13LedgerZ C).PosSemidef := by
  let H := h13LedgerInputGap C
  have hH : H.PosDef := by
    unfold coeCornerSupport at hsupport
    simpa only [H, h13LedgerInputGap] using hsupport
  have hZ := hH.inv.posSemidef.mul_mul_conjTranspose_same C
  simpa only [H, h13LedgerInputGap, h13LedgerZ] using hZ

/-- Consequently the H13 output statistic is Hermitian. -/
theorem h13LedgerZ_isHermitian
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (h13LedgerZ C).IsHermitian :=
  (h13LedgerZ_posSemidef C hsupport).isHermitian

/-- Push-through writes `Z` as `T Cᴴ`. -/
theorem h13LedgerZ_eq_T_mul_cornerStar
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    h13LedgerZ C = h13LedgerT C * C.conjTranspose := by
  unfold h13LedgerZ h13LedgerT
  rw [h13Ledger_outputInv_mul_corner_eq_corner_mul_inputInv C hsupport]

/-- The first nontrivial H13 bilinear argument `Z T` is symmetric. -/
theorem h13LedgerZ_mul_T_isSymm
    {N : ℕ} (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    (h13LedgerZ C * h13LedgerT C).IsSymm := by
  have hT : (h13LedgerT C).transpose = h13LedgerT C :=
    (h13LedgerT_isSymm C hC hsupport).eq
  rw [h13LedgerZ_eq_T_mul_cornerStar C hsupport]
  unfold Matrix.IsSymm
  simp only [Matrix.transpose_mul, hT, hC.conjTranspose.eq]
  noncomm_ring

/-- The `((I+Z)T)` argument in the common mixed words is symmetric. -/
theorem h13LedgerOneAddZ_mul_T_isSymm
    {N : ℕ} (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    ((1 + h13LedgerZ C) * h13LedgerT C).IsSymm := by
  have hT := h13LedgerT_isSymm C hC hsupport
  have hZT := h13LedgerZ_mul_T_isSymm C hC hsupport
  rw [show (1 + h13LedgerZ C) * h13LedgerT C =
      h13LedgerT C + h13LedgerZ C * h13LedgerT C by noncomm_ring]
  exact hT.add hZT

/-- The `((I+2Z)T)` argument in the common mixed words is symmetric. -/
theorem h13LedgerOneAddTwoZ_mul_T_isSymm
    {N : ℕ} (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    ((1 + 2 • h13LedgerZ C) * h13LedgerT C).IsSymm := by
  have hT := h13LedgerT_isSymm C hC hsupport
  have hZT := h13LedgerZ_mul_T_isSymm C hC hsupport
  rw [show (1 + 2 • h13LedgerZ C) * h13LedgerT C =
      h13LedgerT C + 2 • (h13LedgerZ C * h13LedgerT C) by
        simp only [two_nsmul, Matrix.add_mul, Matrix.one_mul]]
  exact hT.add (hZT.smul 2)

/-- The input-side factor `I+2 Zᵀ` is Hermitian. -/
theorem h13LedgerOneAddTwoZTranspose_isHermitian
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (1 + 2 • (h13LedgerZ C).transpose).IsHermitian := by
  have hZt := (h13LedgerZ_isHermitian C hsupport).transpose
  simpa only [two_nsmul] using
    Matrix.isHermitian_one.add (hZt.add hZt)

/-- The final double-transpose H13 argument
`T (I+2 Zᵀ)` is symmetric. -/
theorem h13LedgerT_mul_oneAddTwoZTranspose_isSymm
    {N : ℕ} (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    (h13LedgerT C * (1 + 2 • (h13LedgerZ C).transpose)).IsSymm := by
  let T := h13LedgerT C
  let Z := h13LedgerZ C
  have hT : T.IsSymm := by
    simpa only [T] using h13LedgerT_isSymm C hC hsupport
  have hZT : (Z * T).IsSymm := by
    simpa only [Z, T] using h13LedgerZ_mul_T_isSymm C hC hsupport
  have hcomm : T * Z.transpose = Z * T := by
    have h := hZT.eq
    simp only [Matrix.transpose_mul, hT.eq] at h
    exact h
  rw [show T * (1 + 2 • Z.transpose) =
      T + 2 • (T * Z.transpose) by
        simp only [two_nsmul, Matrix.mul_add, Matrix.mul_one]]
  rw [hcomm]
  exact hT.add (hZT.smul 2)

/-- The input-side Gram matrix of `T` is the transpose beta-prime
polynomial. -/
theorem h13LedgerTStar_mul_T_eq_ZTranspose_mul_oneAddZTranspose
    {N : ℕ} (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    (h13LedgerT C).conjTranspose * h13LedgerT C =
      (h13LedgerZ C).transpose * (1 + (h13LedgerZ C).transpose) := by
  have hGram := h13LedgerT_mul_conjTranspose_eq_Z_mul_one_add_Z C hsupport
  have hT := h13LedgerT_isSymm C hC hsupport
  have hTs := hT.conjTranspose
  have h := congrArg Matrix.transpose hGram
  simp only [Matrix.transpose_mul, Matrix.transpose_add,
    Matrix.transpose_one, hT.eq, hTs.eq] at h
  rw [h]
  noncomm_ring

/-- Exact Gram polynomial for the common symmetric argument `Z T`. -/
theorem h13LedgerZMulT_gram_eq
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (h13LedgerZ C * h13LedgerT C) *
        (h13LedgerZ C * h13LedgerT C).conjTranspose =
      h13LedgerZ C ^ 3 * (1 + h13LedgerZ C) := by
  have hZ := h13LedgerZ_isHermitian C hsupport
  have hGram := h13LedgerT_mul_conjTranspose_eq_Z_mul_one_add_Z C hsupport
  rw [Matrix.conjTranspose_mul, hZ.eq]
  rw [show h13LedgerZ C * h13LedgerT C *
        ((h13LedgerT C).conjTranspose * h13LedgerZ C) =
      h13LedgerZ C *
        (h13LedgerT C * (h13LedgerT C).conjTranspose) *
          h13LedgerZ C by noncomm_ring]
  rw [hGram]
  noncomm_ring

/-- Exact Gram polynomial for `((I+Z)T)`. -/
theorem h13LedgerOneAddZMulT_gram_eq
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    ((1 + h13LedgerZ C) * h13LedgerT C) *
        ((1 + h13LedgerZ C) * h13LedgerT C).conjTranspose =
      h13LedgerZ C * (1 + h13LedgerZ C) ^ 3 := by
  have hZ := h13LedgerZ_isHermitian C hsupport
  have hGram := h13LedgerT_mul_conjTranspose_eq_Z_mul_one_add_Z C hsupport
  rw [Matrix.conjTranspose_mul, Matrix.isHermitian_one.add hZ |>.eq]
  rw [show (1 + h13LedgerZ C) * h13LedgerT C *
        ((h13LedgerT C).conjTranspose * (1 + h13LedgerZ C)) =
      (1 + h13LedgerZ C) *
        (h13LedgerT C * (h13LedgerT C).conjTranspose) *
          (1 + h13LedgerZ C) by noncomm_ring]
  rw [hGram]
  noncomm_ring

/-- Exact Gram polynomial for `((I+2Z)T)`. -/
theorem h13LedgerOneAddTwoZMulT_gram_eq
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    ((1 + 2 • h13LedgerZ C) * h13LedgerT C) *
        ((1 + 2 • h13LedgerZ C) * h13LedgerT C).conjTranspose =
      h13LedgerZ C * (1 + h13LedgerZ C) *
        (1 + 2 • h13LedgerZ C) ^ 2 := by
  have hZ := h13LedgerZ_isHermitian C hsupport
  have hA : (1 + 2 • h13LedgerZ C).IsHermitian := by
    simpa only [two_nsmul] using
      Matrix.isHermitian_one.add (hZ.add hZ)
  have hGram := h13LedgerT_mul_conjTranspose_eq_Z_mul_one_add_Z C hsupport
  rw [Matrix.conjTranspose_mul, hA.eq]
  rw [show (1 + 2 • h13LedgerZ C) * h13LedgerT C *
        ((h13LedgerT C).conjTranspose * (1 + 2 • h13LedgerZ C)) =
      (1 + 2 • h13LedgerZ C) *
        (h13LedgerT C * (h13LedgerT C).conjTranspose) *
          (1 + 2 • h13LedgerZ C) by noncomm_ring]
  rw [hGram]
  noncomm_ring

/-- The two degree-four symmetric arguments in the common and final mixed
words have the same Gram trace. -/
theorem trace_h13LedgerTOneAddTwoZTranspose_gram_eq
    {N : ℕ} (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    Matrix.trace
        ((h13LedgerT C * (1 + 2 • (h13LedgerZ C).transpose)) *
          (h13LedgerT C *
            (1 + 2 • (h13LedgerZ C).transpose)).conjTranspose) =
      Matrix.trace
        (h13LedgerZ C * (1 + h13LedgerZ C) *
          (1 + 2 • h13LedgerZ C) ^ 2) := by
  let T := h13LedgerT C
  let Z := h13LedgerZ C
  let U : ConcreteMatrixState N := 1 + 2 • Z.transpose
  have hU : U.IsHermitian := by
    simpa only [U, Z] using
      h13LedgerOneAddTwoZTranspose_isHermitian C hsupport
  have hInput := h13LedgerTStar_mul_T_eq_ZTranspose_mul_oneAddZTranspose
    C hC hsupport
  calc
    Matrix.trace ((T * U) * (T * U).conjTranspose) =
        Matrix.trace ((T * U * U) * T.conjTranspose) := by
      rw [Matrix.conjTranspose_mul, hU.eq]
      congr 1
      noncomm_ring
    _ = Matrix.trace (T.conjTranspose * (T * U * U)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((T.conjTranspose * T) * U * U) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace
        (Z.transpose * (1 + Z.transpose) *
          (1 + 2 • Z.transpose) ^ 2) := by
      rw [show T.conjTranspose * T =
          Z.transpose * (1 + Z.transpose) by
        simpa only [T, Z] using hInput]
      dsimp only [U]
      noncomm_ring
    _ = Matrix.trace
        (Z * (1 + Z) * (1 + 2 • Z) ^ 2) := by
      rw [show Z.transpose * (1 + Z.transpose) *
          (1 + 2 • Z.transpose) ^ 2 =
          (Z * (1 + Z) * (1 + 2 • Z) ^ 2).transpose by
        simp only [two_nsmul, Matrix.transpose_mul, Matrix.transpose_add,
          Matrix.transpose_one, Matrix.transpose_pow]
        noncomm_ring]
      exact Matrix.trace_transpose _

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
