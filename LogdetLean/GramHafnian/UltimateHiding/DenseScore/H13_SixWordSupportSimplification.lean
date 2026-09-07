import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_FullSixWordProjectivePolynomial
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_BilinearSupportGram
import Mathlib.Tactic

/-!
# Exact support simplification of the six H13 words

Linearity combines the two pure words into one and the three common
mixed-transpose words into twice one word.  The final double-transpose word
is the transpose-cyclic copy of that same mixed word.  Thus the full kernel
is exactly

`pure(W, I+2Z, Z) + 3 mixed(T, T^*, I+2Z)`.

This identity is the small coefficient ledger used by the final projective
contraction.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 2400000

/-- The two pure words combine into one word with middle factor `I+2Z`. -/
theorem h13PureSixWordProjectiveExpansion_eq_single_h13
    {N : ℕ} (v : ComplexUnitSphere N) (Z : ConcreteMatrixState N) :
    h13PureSixWordProjectiveExpansion v (1 + Z) Z =
      h13CenteredTripleTraceProjectiveExpansion v
        (1 + Z) (1 + 2 • Z) Z := by
  let Q := concreteCenteredOrbitalDirection N v
  let E : ConcreteMatrixState N → ConcreteMatrixState N := fun X =>
    Q * (1 + Z) * Q * X * Q * Z
  have hpure := h13PureSixWord_eq_projectiveExpansion v (1 + Z) Z
  have hsingle := trace_centeredDirection_threeWord_expansion_h13
    v (1 + Z) (1 + 2 • Z) Z
  have hmat : E Z + E (1 + Z) = E (1 + 2 • Z) := by
    dsimp only [E]
    simp only [two_nsmul]
    noncomm_ring
  have htrace := congrArg Matrix.trace hmat
  calc
    h13PureSixWordProjectiveExpansion v (1 + Z) Z =
        Matrix.trace (E Z) + Matrix.trace (E (1 + Z)) := by
      simpa only [E, Q] using hpure.symm
    _ = Matrix.trace (E (1 + 2 • Z)) := by
      simpa only [Matrix.trace_add] using htrace
    _ = h13CenteredTripleTraceProjectiveExpansion v
        (1 + Z) (1 + 2 • Z) Z := by
      simpa only [E, Q] using hsingle

/-- The three common mixed words combine into twice the word with final
factor `I+2Z`. -/
theorem h13CommonMixedSixWordProjectiveExpansion_eq_two_single_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (T Ts Z : ConcreteMatrixState N) :
    h13CommonMixedSixWordProjectiveExpansion v
        (1 + Z) (1 + 2 • Z) T Ts Z =
      2 * h13CenteredTripleMixedTransposeExpansion v T Ts (1 + 2 • Z) := by
  let Q := concreteCenteredOrbitalDirection N v
  let Qt := Q.transpose
  let E : ConcreteMatrixState N → ConcreteMatrixState N := fun X =>
    Q * T * Qt * Ts * Q * X
  have hmat : E Z + E (1 + Z) + E (1 + 2 • Z) =
      2 • E (1 + 2 • Z) := by
    dsimp only [E]
    simp only [two_nsmul]
    noncomm_ring
  have htrace := congrArg Matrix.trace hmat
  unfold h13CommonMixedSixWordProjectiveExpansion
  rw [← trace_centeredDirection_mixedTranspose_threeWord_expansion_h13
    v T Ts Z]
  rw [← trace_centeredDirection_mixedTranspose_threeWord_expansion_h13
    v T Ts (1 + Z)]
  rw [← trace_centeredDirection_mixedTranspose_threeWord_expansion_h13
    v T Ts (1 + 2 • Z)]
  simpa only [E, Q, Qt, Matrix.trace_add, two_smul, two_mul] using htrace

/-- The final double-transpose trace is the transpose-cyclic copy of the
common mixed trace. -/
theorem trace_centeredDirection_final_eq_common_mixed_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (T A : ConcreteMatrixState N) (hT : T.IsSymm) :
    Matrix.trace
        (concreteCenteredOrbitalDirection N v * T *
          (concreteCenteredOrbitalDirection N v).transpose * A.transpose *
          (concreteCenteredOrbitalDirection N v).transpose * T.conjTranspose) =
      Matrix.trace
        (concreteCenteredOrbitalDirection N v * T *
          (concreteCenteredOrbitalDirection N v).transpose * T.conjTranspose *
          concreteCenteredOrbitalDirection N v * A) := by
  let Q := concreteCenteredOrbitalDirection N v
  let Qt := Q.transpose
  let Ts := T.conjTranspose
  have hTs : Ts.IsSymm := by
    simpa only [Ts] using hT.conjTranspose
  calc
    Matrix.trace (Q * T * Qt * A.transpose * Qt * Ts) =
        Matrix.trace ((Q * T * Qt) * (A.transpose * Qt * Ts)) := by
      congr 1
      noncomm_ring
    _ = Matrix.trace ((A.transpose * Qt * Ts) * (Q * T * Qt)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Q * T * Qt * Ts * Q * A).transpose := by
      rw [show (Q * T * Qt * Ts * Q * A).transpose =
          A.transpose * Qt * Ts * Q * T * Qt by
        simp only [Matrix.transpose_mul, hT.eq, hTs.eq]
        dsimp only [Qt]
        simp only [Matrix.transpose_transpose]
        noncomm_ring]
      congr 1
      noncomm_ring
    _ = Matrix.trace (Q * T * Qt * Ts * Q * A) :=
      Matrix.trace_transpose _

/-- At the projective-expansion level, the final word equals the common word
when its middle factor is the transpose of the common final factor. -/
theorem h13CenteredTripleDoubleTransposeExpansion_eq_mixed_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (T A : ConcreteMatrixState N) (hT : T.IsSymm) :
    h13CenteredTripleDoubleTransposeExpansion
        v T A.transpose T.conjTranspose =
      h13CenteredTripleMixedTransposeExpansion
        v T T.conjTranspose A := by
  rw [← h13FinalSixWord_eq_projectiveExpansion]
  rw [← trace_centeredDirection_mixedTranspose_threeWord_expansion_h13]
  exact trace_centeredDirection_final_eq_common_mixed_h13 v T A hT

/-- On support, all six H13 words reduce to one pure expansion plus three
copies of one mixed expansion. -/
theorem h13FullSixWordProjectiveExpansion_support_simplified_h13
    {N : ℕ} (v : ComplexUnitSphere N)
    (C : ConcreteMatrixState N) (hC : C.IsSymm)
    (hsupport : coeCornerSupport C) :
    h13FullSixWordProjectiveExpansion v C =
      h13CenteredTripleTraceProjectiveExpansion v
          (1 + h13LedgerZ C) (1 + 2 • h13LedgerZ C) (h13LedgerZ C) +
        3 * h13CenteredTripleMixedTransposeExpansion v
          (h13LedgerT C) (h13LedgerT C).conjTranspose
          (1 + 2 • h13LedgerZ C) := by
  let Z := h13LedgerZ C
  let T := h13LedgerT C
  let A : ConcreteMatrixState N := 1 + 2 • Z
  have hT : T.IsSymm := by
    simpa only [T] using h13LedgerT_isSymm C hC hsupport
  have hU : 1 + 2 • ((h13LedgerT C).conjTranspose * C) = A.transpose := by
    rw [h13LedgerTStar_mul_corner_eq_Z_transpose C hC hsupport]
    simp only [A, Z, two_nsmul, Matrix.transpose_add, Matrix.transpose_one]
  unfold h13FullSixWordProjectiveExpansion
  dsimp only
  rw [h13PureSixWordProjectiveExpansion_eq_single_h13]
  rw [h13CommonMixedSixWordProjectiveExpansion_eq_two_single_h13]
  rw [hU]
  rw [h13CenteredTripleDoubleTransposeExpansion_eq_mixed_h13 v T A hT]
  dsimp only [T, A, Z]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
