import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_BilinearSupportTraceLedger
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_DoubleTransposeSixWordProjectiveExpansion
import Mathlib.Tactic

/-!
# Positive support factors in the simplified H13 mixed word

After the six support words have been reduced to one mixed word, its scalar
projective expansion uses only the four matrices

`A = I + 2 Z`, `B = T T^*`, `P = A B`, and `G = T^* A T`.

This module records positivity, commutation, and trace identities for those
matrices.  In particular, all three linear projective terms at order `N^-2`
have the same positive trace envelope `Tr(P)`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 2400000

/-- The support polynomial `I + 2 Z` is positive semidefinite. -/
theorem h13LedgerOneAddTwoZ_posSemidef
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C).PosSemidef := by
  have hZ := h13LedgerZ_posSemidef C hsupport
  simpa only [two_nsmul] using Matrix.PosSemidef.one.add (hZ.add hZ)

/-- The output Gram `T T^*` is positive semidefinite. -/
theorem h13LedgerTGram_posSemidef
    {N : ℕ} (C : ConcreteMatrixState N) :
    (h13LedgerT C * (h13LedgerT C).conjTranspose).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

/-- The product `(I+2Z) T T^*` is the positive polynomial
`Z + 3 Z^2 + 2 Z^3`. -/
theorem h13LedgerOneAddTwoZ_mul_TGram_eq_positivePolynomial
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
        (h13LedgerT C * (h13LedgerT C).conjTranspose) =
      h13LedgerZ C + 3 • h13LedgerZ C ^ 2 +
        2 • h13LedgerZ C ^ 3 := by
  rw [h13LedgerT_mul_conjTranspose_eq_Z_mul_one_add_Z C hsupport]
  simp only [two_nsmul, three_nsmul]
  noncomm_ring

/-- Consequently `(I+2Z) T T^*` is positive semidefinite. -/
theorem h13LedgerOneAddTwoZ_mul_TGram_posSemidef
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
      (h13LedgerT C * (h13LedgerT C).conjTranspose)).PosSemidef := by
  have hZ := h13LedgerZ_posSemidef C hsupport
  have h3 : (3 • h13LedgerZ C ^ 2).PosSemidef := by
    simpa only [three_nsmul] using
      (hZ.pow 2).add ((hZ.pow 2).add (hZ.pow 2))
  have h2 : (2 • h13LedgerZ C ^ 3).PosSemidef := by
    simpa only [two_nsmul] using (hZ.pow 3).add (hZ.pow 3)
  rw [h13LedgerOneAddTwoZ_mul_TGram_eq_positivePolynomial C hsupport]
  exact (hZ.add h3).add h2

/-- The same two support polynomials commute in the reverse order. -/
theorem h13LedgerTGram_mul_oneAddTwoZ_eq
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    (h13LedgerT C * (h13LedgerT C).conjTranspose) *
        ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) =
      ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
        (h13LedgerT C * (h13LedgerT C).conjTranspose) := by
  rw [h13LedgerT_mul_conjTranspose_eq_Z_mul_one_add_Z C hsupport]
  simp only [two_nsmul]
  noncomm_ring

/-- The input-side congruence `T^* (I+2Z) T` is positive semidefinite. -/
theorem h13LedgerTStar_mul_oneAddTwoZ_mul_T_posSemidef
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    ((h13LedgerT C).conjTranspose *
      ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
      h13LedgerT C).PosSemidef := by
  have hA := h13LedgerOneAddTwoZ_posSemidef C hsupport
  simpa only [Matrix.mul_assoc] using
    hA.conjTranspose_mul_mul_same (h13LedgerT C)

/-- Transposition preserves positivity for the input-side congruence. -/
theorem h13LedgerTStar_mul_oneAddTwoZ_mul_T_transpose_posSemidef
    {N : ℕ} (C : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    ((h13LedgerT C).conjTranspose *
      ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
      h13LedgerT C).transpose.PosSemidef :=
  (h13LedgerTStar_mul_oneAddTwoZ_mul_T_posSemidef C hsupport).transpose

/-- The congruence and the commuting output product have the same trace. -/
theorem trace_h13LedgerTStar_mul_oneAddTwoZ_mul_T_eq_outputProduct
    {N : ℕ} (C : ConcreteMatrixState N) :
    Matrix.trace
        ((h13LedgerT C).conjTranspose *
          ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
          h13LedgerT C) =
      Matrix.trace
        (((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
          (h13LedgerT C * (h13LedgerT C).conjTranspose)) := by
  calc
    Matrix.trace
        ((h13LedgerT C).conjTranspose *
          ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
          h13LedgerT C) =
        Matrix.trace
          (((h13LedgerT C).conjTranspose *
              ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C)) *
            h13LedgerT C) := by
      congr 1
    _ = Matrix.trace
        (h13LedgerT C *
          ((h13LedgerT C).conjTranspose *
            ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C))) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace
        (((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
          (h13LedgerT C * (h13LedgerT C).conjTranspose)) := by
      rw [show h13LedgerT C *
          ((h13LedgerT C).conjTranspose *
            ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C)) =
          (h13LedgerT C * (h13LedgerT C).conjTranspose) *
            ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) by
          noncomm_ring]
      exact Matrix.trace_mul_comm _ _

/-- The transposed projective term in the mixed expansion is an ordinary
projective pairing of a positive-semidefinite transpose matrix. -/
theorem transposePair_h13LedgerInputCongruence_eq_projectiveTracePair
    {N : ℕ} (v : ComplexUnitSphere N) (C : ConcreteMatrixState N) :
    complexTransposeProjectiveTracePair v
        ((h13LedgerT C).conjTranspose *
          ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
          h13LedgerT C) =
      complexProjectiveTracePair v
        ((h13LedgerT C).conjTranspose *
          ((1 : ConcreteMatrixState N) + 2 • h13LedgerZ C) *
          h13LedgerT C).transpose := by
  exact (complexProjectiveTracePair_transpose_eq_transposePair_h13 _ _).symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
