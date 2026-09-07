import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_BilinearSupportGram
import Mathlib.Tactic

/-!
# Scalar trace ledger for the H13 bilinear Gram matrices

This file expands the exact support Gram identities into the four positive
trace powers consumed by the A4 beta-prime moment package.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 2400000

/-- The basic `T` factor uses only the first two trace powers. -/
theorem trace_h13LedgerT_gram_re_eq
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (Matrix.trace
      (h13LedgerT C * (h13LedgerT C).conjTranspose)).re =
      (Matrix.trace (h13LedgerZ C)).re +
        (Matrix.trace (h13LedgerZ C ^ 2)).re := by
  rw [h13LedgerT_mul_conjTranspose_eq_Z_mul_one_add_Z C hsupport]
  rw [show h13LedgerZ C * (1 + h13LedgerZ C) =
      h13LedgerZ C + h13LedgerZ C ^ 2 by noncomm_ring]
  simp only [Matrix.trace_add, Complex.add_re]

/-- The `ZT` factor uses the third and fourth trace powers. -/
theorem trace_h13LedgerZMulT_gram_re_eq
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (Matrix.trace
      ((h13LedgerZ C * h13LedgerT C) *
        (h13LedgerZ C * h13LedgerT C).conjTranspose)).re =
      (Matrix.trace (h13LedgerZ C ^ 3)).re +
        (Matrix.trace (h13LedgerZ C ^ 4)).re := by
  rw [h13LedgerZMulT_gram_eq C hsupport]
  rw [show h13LedgerZ C ^ 3 * (1 + h13LedgerZ C) =
      h13LedgerZ C ^ 3 + h13LedgerZ C ^ 4 by noncomm_ring]
  simp only [Matrix.trace_add, Complex.add_re]

/-- The `((I+Z)T)` factor has binomial coefficients `1,3,3,1`. -/
theorem trace_h13LedgerOneAddZMulT_gram_re_eq
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (Matrix.trace
      (((1 + h13LedgerZ C) * h13LedgerT C) *
        ((1 + h13LedgerZ C) * h13LedgerT C).conjTranspose)).re =
      (Matrix.trace (h13LedgerZ C)).re +
        3 * (Matrix.trace (h13LedgerZ C ^ 2)).re +
        3 * (Matrix.trace (h13LedgerZ C ^ 3)).re +
        (Matrix.trace (h13LedgerZ C ^ 4)).re := by
  rw [h13LedgerOneAddZMulT_gram_eq C hsupport]
  rw [show h13LedgerZ C * (1 + h13LedgerZ C) ^ 3 =
      h13LedgerZ C +
        3 • h13LedgerZ C ^ 2 +
        3 • h13LedgerZ C ^ 3 +
        h13LedgerZ C ^ 4 by
      simp only [three_nsmul]
      noncomm_ring]
  simp only [three_nsmul, Matrix.trace_add, Complex.add_re]
  ring

/-- Both degree-four mixed arguments have the common coefficient ledger
`1,5,8,4`. -/
theorem trace_h13LedgerOneAddTwoZMulT_gram_re_eq
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (Matrix.trace
      ((((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) * h13LedgerT C) *
        (((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
          h13LedgerT C).conjTranspose)).re =
      (Matrix.trace (h13LedgerZ C)).re +
        5 * (Matrix.trace (h13LedgerZ C ^ 2)).re +
        8 * (Matrix.trace (h13LedgerZ C ^ 3)).re +
        4 * (Matrix.trace (h13LedgerZ C ^ 4)).re := by
  rw [h13LedgerOneAddTwoZMulT_gram_eq C hsupport]
  rw [show h13LedgerZ C * (1 + h13LedgerZ C) *
        ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) ^ 2 =
      h13LedgerZ C +
        (h13LedgerZ C ^ 2 + h13LedgerZ C ^ 2 +
          h13LedgerZ C ^ 2 + h13LedgerZ C ^ 2 +
          h13LedgerZ C ^ 2) +
        (h13LedgerZ C ^ 3 + h13LedgerZ C ^ 3 +
          h13LedgerZ C ^ 3 + h13LedgerZ C ^ 3 +
          h13LedgerZ C ^ 3 + h13LedgerZ C ^ 3 +
          h13LedgerZ C ^ 3 + h13LedgerZ C ^ 3) +
        (h13LedgerZ C ^ 4 + h13LedgerZ C ^ 4 +
          h13LedgerZ C ^ 4 + h13LedgerZ C ^ 4) by
      simp only [two_nsmul]
      noncomm_ring]
  simp only [Matrix.trace_add, Complex.add_re]
  ring

/-- The final double-transpose symmetric argument has the same scalar ledger
as `((I+2Z)T)`. -/
theorem trace_h13LedgerTOneAddTwoZTranspose_gram_re_eq
    {N : ℕ} (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    (Matrix.trace
      ((h13LedgerT C *
          ((1 : ConcreteMatrixState N) + 2 • (h13LedgerZ C).transpose)) *
        (h13LedgerT C *
          ((1 : ConcreteMatrixState N) +
            2 • (h13LedgerZ C).transpose)).conjTranspose)).re =
      (Matrix.trace (h13LedgerZ C)).re +
        5 * (Matrix.trace (h13LedgerZ C ^ 2)).re +
        8 * (Matrix.trace (h13LedgerZ C ^ 3)).re +
        4 * (Matrix.trace (h13LedgerZ C ^ 4)).re := by
  rw [trace_h13LedgerTOneAddTwoZTranspose_gram_eq C hC hsupport]
  rw [← h13LedgerOneAddTwoZMulT_gram_eq C hsupport]
  exact trace_h13LedgerOneAddTwoZMulT_gram_re_eq C hsupport

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
