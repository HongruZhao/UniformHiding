import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeTraceWordLedger
import Mathlib.Tactic

/-!
# Total-degree-four certificate for the H13 trace-word ledger

The exact H13 ledger is cubic in its direction in the third-score factor and
linear in the first-score factor.  This file records that statement as literal
homogeneity identities; it contains no probability estimate.
-/

open Matrix
open scoped Matrix ComplexConjugate

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

theorem h13LedgerCornerVelocity_smul {N : ℕ} (z : ℂ)
    (Q C : ConcreteMatrixState N) :
    h13LedgerCornerVelocity (z • Q) C =
      z • h13LedgerCornerVelocity Q C := by
  unfold h13LedgerCornerVelocity
  simp only [Matrix.smul_mul, Matrix.transpose_smul, Matrix.mul_smul,
    ← smul_add, smul_neg]

theorem h13LedgerCornerStarVelocity_smul {N : ℕ} (z : ℂ)
    (Q C : ConcreteMatrixState N) :
    h13LedgerCornerStarVelocity (z • Q) C =
      z • h13LedgerCornerStarVelocity Q C := by
  unfold h13LedgerCornerStarVelocity
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    ← smul_add, smul_neg]

theorem h13LedgerInputGapVelocity_smul {N : ℕ} (z : ℂ)
    (Q C : ConcreteMatrixState N) :
    h13LedgerInputGapVelocity (z • Q) C =
      z • h13LedgerInputGapVelocity Q C := by
  unfold h13LedgerInputGapVelocity
  rw [h13LedgerCornerVelocity_smul, h13LedgerCornerStarVelocity_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, smul_neg]

theorem h13LedgerOutputGapVelocity_smul {N : ℕ} (z : ℂ)
    (Q C : ConcreteMatrixState N) :
    h13LedgerOutputGapVelocity (z • Q) C =
      z • h13LedgerOutputGapVelocity Q C := by
  unfold h13LedgerOutputGapVelocity
  rw [h13LedgerCornerVelocity_smul, h13LedgerCornerStarVelocity_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_add, smul_neg]

theorem h13LedgerInputResolventVelocity_smul {N : ℕ} (z : ℂ)
    (Q C : ConcreteMatrixState N) :
    h13LedgerInputResolventVelocity (z • Q) C =
      z • h13LedgerInputResolventVelocity Q C := by
  unfold h13LedgerInputResolventVelocity
  rw [h13LedgerInputGapVelocity_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem h13LedgerOutputResolventVelocity_smul {N : ℕ} (z : ℂ)
    (Q C : ConcreteMatrixState N) :
    h13LedgerOutputResolventVelocity (z • Q) C =
      z • h13LedgerOutputResolventVelocity Q C := by
  unfold h13LedgerOutputResolventVelocity
  rw [h13LedgerOutputGapVelocity_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem h13LedgerZVelocity_smul {N : ℕ} (z : ℂ)
    (Q C : ConcreteMatrixState N) :
    h13LedgerZVelocity (z • Q) C = z • h13LedgerZVelocity Q C := by
  unfold h13LedgerZVelocity
  rw [h13LedgerCornerVelocity_smul,
    h13LedgerInputResolventVelocity_smul,
    h13LedgerCornerStarVelocity_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_add]

theorem h13LedgerTVelocity_smul {N : ℕ} (z : ℂ)
    (Q C : ConcreteMatrixState N) :
    h13LedgerTVelocity (z • Q) C = z • h13LedgerTVelocity Q C := by
  unfold h13LedgerTVelocity
  rw [h13LedgerOutputResolventVelocity_smul,
    h13LedgerCornerVelocity_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_add]

theorem h13LedgerTStarVelocity_smul {N : ℕ} (z : ℂ)
    (Q C : ConcreteMatrixState N) :
    h13LedgerTStarVelocity (z • Q) C =
      z • h13LedgerTStarVelocity Q C := by
  unfold h13LedgerTStarVelocity
  rw [h13LedgerCornerStarVelocity_smul,
    h13LedgerOutputResolventVelocity_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_add]

/-- The differentiated third-score trace kernel is exactly cubic in `Q`. -/
theorem h13ThirdTraceKernelVelocity_smul {N : ℕ} (z : ℂ)
    (Q C : ConcreteMatrixState N) :
    h13ThirdTraceKernelVelocity (z • Q) C =
      z ^ 3 * h13ThirdTraceKernelVelocity Q C := by
  unfold h13ThirdTraceKernelVelocity
  rw [h13LedgerZVelocity_smul, h13LedgerTVelocity_smul,
    h13LedgerTStarVelocity_smul]
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.trace_smul, smul_eq_mul]
  ring

/-- The complete derivative-free `ell_1 ell_3` ledger has total degree four
in every real rescaling of the centered projective direction. -/
theorem h13OneThreeTraceWordLedger_real_smul {N : ℕ} (r : ℝ)
    (Q C Y : ConcreteMatrixState N) :
    h13OneThreeTraceWordLedger (r • Q) C Y =
      r ^ 4 * h13OneThreeTraceWordLedger Q C Y := by
  have hrQ : r • Q = ((r : ℂ)) • Q :=
    RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  rw [hrQ]
  unfold h13OneThreeTraceWordLedger
  rw [h13ThirdTraceKernelVelocity_smul]
  have hrpow : ((r : ℂ) ^ 3) = ((r ^ 3 : ℝ) : ℂ) := by norm_num
  rw [hrpow]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, mul_zero]
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
