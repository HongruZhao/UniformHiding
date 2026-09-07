import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_DoubleTransposeSixWordProjectiveExpansion
import Mathlib.Tactic

/-!
# Full scalar projective polynomial for the H13 support ledger

This file joins the pure, one-transpose and double-transpose expansions.  On
the open matrix ball the entire differentiated third-score kernel is now an
explicit scalar projective polynomial.  Multiplication by the first centered
trace has total projective degree at most four.

This is the canonical algebraic handoff for a projective-first H13 estimate:
no matrix derivative or unexpanded centered trace word remains.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

set_option maxHeartbeats 2400000

/-- Scalar projective expansion of all six support-normal-form H13 words. -/
def h13FullSixWordProjectiveExpansion
    {N : ℕ} (v : ComplexUnitSphere N)
    (C : ConcreteMatrixState N) : ℂ :=
  let Z := h13LedgerZ C
  let T := h13LedgerT C
  let Ts := (h13LedgerT C).conjTranspose
  let W : ConcreteMatrixState N := 1 + Z
  let A : ConcreteMatrixState N := 1 + 2 • Z
  let U : ConcreteMatrixState N := 1 + 2 • (Ts * C)
  h13PureSixWordProjectiveExpansion v W Z +
    h13CommonMixedSixWordProjectiveExpansion v W A T Ts Z +
    h13CenteredTripleDoubleTransposeExpansion v T U Ts

/-- Exact full expansion of the six-word kernel at a centered projective
direction. -/
theorem h13ThirdTraceKernelSixWord_centered_eq_projectiveExpansion
    {N : ℕ} (v : ComplexUnitSphere N)
    (C : ConcreteMatrixState N) :
    h13ThirdTraceKernelSixWord
        (concreteCenteredOrbitalDirection N v) C =
      h13FullSixWordProjectiveExpansion v C := by
  let Q := concreteCenteredOrbitalDirection N v
  let Z := h13LedgerZ C
  let T := h13LedgerT C
  let Ts := (h13LedgerT C).conjTranspose
  let W : ConcreteMatrixState N := 1 + Z
  let A : ConcreteMatrixState N := 1 + 2 • Z
  let U : ConcreteMatrixState N := 1 + 2 • (Ts * C)
  have hpure :
      Matrix.trace (Q * W * Q * Z * Q * Z) +
          Matrix.trace (Q * W * Q * W * Q * Z) =
        h13PureSixWordProjectiveExpansion v W Z := by
    simpa only [Q] using h13PureSixWord_eq_projectiveExpansion v W Z
  have hcommon :
      Matrix.trace (Q * T * Q.transpose * Ts * Q * Z) +
          Matrix.trace (Q * W * Q * T * Q.transpose * Ts) +
          Matrix.trace (Q * A * Q * T * Q.transpose * Ts) =
        h13CommonMixedSixWordProjectiveExpansion v W A T Ts Z := by
    simpa only [Q] using
      h13CommonMixedSixWord_eq_projectiveExpansion v W A T Ts Z
  have hfinal : Matrix.trace (Q * T * Q.transpose * U * Q.transpose * Ts) =
      h13CenteredTripleDoubleTransposeExpansion v T U Ts := by
    simpa only [Q] using h13FinalSixWord_eq_projectiveExpansion v T U Ts
  unfold h13ThirdTraceKernelSixWord
  change
    Matrix.trace (Q * W * Q * Z * Q * Z) +
        Matrix.trace (Q * T * Q.transpose * Ts * Q * Z) +
        Matrix.trace (Q * W * Q * W * Q * Z) +
        Matrix.trace (Q * W * Q * T * Q.transpose * Ts) +
        Matrix.trace (Q * A * Q * T * Q.transpose * Ts) +
        Matrix.trace (Q * T * Q.transpose * U * Q.transpose * Ts) = _
  unfold h13FullSixWordProjectiveExpansion
  simp only [Z, T, Ts, W, A, U]
  rw [hfinal]
  linear_combination hpure + hcommon

/-- The complete real scalar polynomial for the H13 derivative-free ledger.
Its first factor has projective degree at most one and its second factor at
most three. -/
def h13FullOneThreeProjectivePolynomial
    {N : ℕ} (v : ComplexUnitSphere N)
    (C Y : ConcreteMatrixState N) : ℝ :=
  -2 *
    (complexProjectiveTracePair v Y -
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace Y).re *
    (h13FullSixWordProjectiveExpansion v C).re

/-- On support, the literal derivative-free H13 ledger is exactly the full
degree-at-most-four scalar projective polynomial. -/
theorem h13OneThreeTraceWordLedger_centered_eq_fullProjectivePolynomial
    {N : ℕ} (v : ComplexUnitSphere N)
    (C Y : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    h13OneThreeTraceWordLedger
        (concreteCenteredOrbitalDirection N v) C Y =
      h13FullOneThreeProjectivePolynomial v C Y := by
  unfold h13OneThreeTraceWordLedger
  rw [h13ThirdTraceKernelVelocity_support_sixWord _ C hsupport]
  rw [h13ThirdTraceKernelSixWord_centered_eq_projectiveExpansion]
  rw [trace_concreteCenteredOrbitalDirection_mul]
  unfold h13FullOneThreeProjectivePolynomial
  unfold complexCenteredProjectiveTracePair
  norm_num [Complex.mul_re]
  ring

/-- Restoring the deterministic coefficient in the literal score identity
gives `16 c` times the same degree-at-most-four polynomial. -/
theorem negEightExponent_mul_h13Ledger_eq_fullProjectivePolynomial
    {N K : ℕ} (v : ComplexUnitSphere N)
    (C Y : ConcreteMatrixState N)
    (hsupport : coeCornerSupport C) :
    -8 * concreteCOEExponent N K *
        h13OneThreeTraceWordLedger
          (concreteCenteredOrbitalDirection N v) C Y =
      16 * concreteCOEExponent N K *
        ((complexProjectiveTracePair v Y -
          (((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace Y).re *
          (h13FullSixWordProjectiveExpansion v C).re) := by
  rw [h13OneThreeTraceWordLedger_centered_eq_fullProjectivePolynomial
    v C Y hsupport]
  unfold h13FullOneThreeProjectivePolynomial
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
