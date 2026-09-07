import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_ScaledH14Envelope
import Mathlib.Tactic

/-!
# Relaxed H13 projective-envelope transport

The literal H14 envelope has fixed-sphere coefficient `2^12`.  Multiplying it
by `16` gives coefficient `2^16`, leaving ample room for the separated H13
Holder ledger while remaining vastly below the paper-facing fourth-moment
constant after matrix-law integration.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- H13-specific relaxed envelope: `16` times the closed H14 envelope. -/
def h13RelaxedProjectiveEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  h13ScaledH14ProjectiveEnvelope 16 N K A

/-- Explicit strong expectation constant retained for the H11 lower-Bell
budget. -/
def h13RelaxedProjectiveEnvelopeStrongConstant : ℝ :=
  16 * h14StrongProjectiveEnvelopeConstant

theorem h13RelaxedProjectiveEnvelope_nonneg
    (N K : ℕ) (A : ConcreteMatrixState N) :
    0 ≤ h13RelaxedProjectiveEnvelope N K A := by
  unfold h13RelaxedProjectiveEnvelope
  exact h13ScaledH14ProjectiveEnvelope_nonneg 16 (by norm_num) N K A

/-- The relaxed envelope is exactly a `2^16` multiple of the normalized
trace-one/trace-two basis used by H14. -/
theorem h13RelaxedProjectiveEnvelope_eq_twoPow16_basis
    (N K : ℕ) (A : ConcreteMatrixState N) :
    h13RelaxedProjectiveEnvelope N K A =
      (2 : ℝ) ^ 16 *
        ((concreteCOETraceOne N K A ^ 2 +
            |concreteCOETraceTwo N K A|) / (N : ℝ) ^ 2 +
          concreteCOETraceOne N K A ^ 4 /
            ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
          concreteCOETraceTwo N K A ^ 2 /
            ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)) := by
  unfold h13RelaxedProjectiveEnvelope h13ScaledH14ProjectiveEnvelope
    h14ProjectiveCancellationEnvelope
  norm_num
  ring

/-- Approved A2--A3 transport and the already checked radial recurrences give
the explicit strong expectation estimate. -/
theorem h13RelaxedProjectiveEnvelope_momentPackage_strong_A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    Integrable (h13RelaxedProjectiveEnvelope N K)
        (higherScoreMatrixLaw N K) ∧
      (16 * N ≤ K →
        (∫ A, h13RelaxedProjectiveEnvelope N K A
            ∂(higherScoreMatrixLaw N K)) ≤
          h13RelaxedProjectiveEnvelopeStrongConstant * (N : ℝ) ^ 2) := by
  have H := h13ScaledH14ProjectiveEnvelope_momentPackage_strong_A2A3
    hN hgap 16 (by norm_num)
  change
    Integrable (h13ScaledH14ProjectiveEnvelope 16 N K)
        (higherScoreMatrixLaw N K) ∧
      (16 * N ≤ K →
        (∫ A, h13ScaledH14ProjectiveEnvelope 16 N K A
            ∂(higherScoreMatrixLaw N K)) ≤
          (16 * h14StrongProjectiveEnvelopeConstant) * (N : ℝ) ^ 2)
  exact H

/-- Paper-facing matrix package for the relaxed envelope. -/
theorem h13RelaxedTraceEnvelopeL1Package_A2A3
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    HigherScoreTraceEnvelopeL1Package N K
      (h13RelaxedProjectiveEnvelope N K) := by
  have hbudget : (16 : ℝ) * h14StrongProjectiveEnvelopeConstant ≤
      centeredLogScoreFourthMomentConstant := by
    norm_num [h14StrongProjectiveEnvelopeConstant,
      h14BetaPrimeProjectiveLowerMomentConstant,
      denseClassicalMomentConstant, centeredLogScoreFourthMomentConstant]
  change HigherScoreTraceEnvelopeL1Package N K
    (h13ScaledH14ProjectiveEnvelope 16 N K)
  exact h13ScaledH14TraceEnvelopeL1Package_A2A3
    hN hgap 16 (by norm_num) hbudget

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
