import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_StrongProjectiveEnvelopeBound
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11H13_ProjectiveFirstReduction
import Mathlib.Tactic

/-!
# Scaled H14 radial envelope for H13

The public H13 constant has very large numerical slack.  This module records
the elementary fact that any nonnegative scalar multiple of the already
proved H14 radial envelope remains integrable, with its strong expectation
bound scaled by the same factor.  It is a foundations-only fallback for the
fixed-sphere coefficient collection; it introduces no new probabilistic or
scientific input.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- A scalar multiple of the closed H14 matrix envelope. -/
def h13ScaledH14ProjectiveEnvelope (scale : ℝ) (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  scale * h14ProjectiveCancellationEnvelope N K A

theorem h13ScaledH14ProjectiveEnvelope_nonneg
    (scale : ℝ) (hscale : 0 ≤ scale) (N K : ℕ)
    (A : ConcreteMatrixState N) :
    0 ≤ h13ScaledH14ProjectiveEnvelope scale N K A := by
  unfold h13ScaledH14ProjectiveEnvelope
  exact mul_nonneg hscale (h14ProjectiveCancellationEnvelope_nonneg N K A)

/-- Strong matrix-law estimate for the scaled envelope. -/
theorem h13ScaledH14ProjectiveEnvelope_momentPackage_strong_A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (scale : ℝ) (hscale : 0 ≤ scale) :
    Integrable (h13ScaledH14ProjectiveEnvelope scale N K)
        (higherScoreMatrixLaw N K) ∧
      (16 * N ≤ K →
        (∫ A, h13ScaledH14ProjectiveEnvelope scale N K A
            ∂(higherScoreMatrixLaw N K)) ≤
          (scale * h14StrongProjectiveEnvelopeConstant) * (N : ℝ) ^ 2) := by
  have H := h14ProjectiveCancellationEnvelope_momentPackage_strong_A2A3
    hN hgap
  have hInt : Integrable
      (fun A : ConcreteMatrixState N ↦
        scale * h14ProjectiveCancellationEnvelope N K A)
      (higherScoreMatrixLaw N K) := H.1.const_mul scale
  constructor
  · change Integrable
      (fun A : ConcreteMatrixState N ↦
        scale * h14ProjectiveCancellationEnvelope N K A)
      (higherScoreMatrixLaw N K)
    exact hInt
  · intro hdense
    have hbound := mul_le_mul_of_nonneg_left (H.2 hdense) hscale
    rw [show h13ScaledH14ProjectiveEnvelope scale N K =
        fun A : ConcreteMatrixState N ↦
          scale * h14ProjectiveCancellationEnvelope N K A by rfl]
    rw [integral_const_mul]
    calc
      scale *
          (∫ A, h14ProjectiveCancellationEnvelope N K A
            ∂(higherScoreMatrixLaw N K)) ≤
        scale *
          (h14StrongProjectiveEnvelopeConstant * (N : ℝ) ^ 2) := hbound
      _ = (scale * h14StrongProjectiveEnvelopeConstant) * (N : ℝ) ^ 2 := by
        ring

/-- The scaled envelope supplies the ordinary paper-facing matrix package
whenever its explicit strong constant fits the common H13 budget. -/
theorem h13ScaledH14TraceEnvelopeL1Package_A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (scale : ℝ) (hscale : 0 ≤ scale)
    (hbudget : scale * h14StrongProjectiveEnvelopeConstant ≤
      centeredLogScoreFourthMomentConstant) :
    HigherScoreTraceEnvelopeL1Package N K
      (h13ScaledH14ProjectiveEnvelope scale N K) := by
  have H := h13ScaledH14ProjectiveEnvelope_momentPackage_strong_A2A3
    hN hgap scale hscale
  refine
    { integrable := H.1
      integral_le := ?_ }
  intro hdense
  exact (H.2 hdense).trans
    (mul_le_mul_of_nonneg_right hbudget (sq_nonneg (N : ℝ)))

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
