import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_Proof
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_ProjectiveCancellationAlgebra
import Mathlib.Tactic

/-!
# Centered ell-two and trace-zero projective cancellation for H14

This module is strictly intermediate.  It records the exact centered
`ell₂` sandwich representation, removes scalar matrix parts before applying
the exact projective fourth-moment identity, and isolates the remaining
fixed-matrix fourth contraction as an explicit CONDITIONAL contract.

No literal H14 endpoint is invoked or concluded.  In particular, the false
raw `O(N^2)` beta-prime trace-two mean bound is absent.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.CurrentPRL

/-! ## Exact centered ell-two representation -/

/-- PROVED intermediate: the literal centered second log score is exactly
the sum of the two centered projective sandwiches, before any absolute-value
estimate. -/
theorem concreteCenteredEll_two_eq_projectiveSandwiches_h14_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 2 N K (A, v) =
      -4 *
        ((complexCenteredProjectiveSandwich v
            (concreteCOEWMatrix N K A) (concreteCOEY N K A)).re +
          (complexCenteredProjectiveConjugateSandwich v
            (concreteCOERMatrix N K A)).re) :=
  centeredLogScore_two_eq_centeredSandwiches_internal
    hN hgap A v hsymm hsupport

/-- PROVED intermediate squared form, still before any projective or radial
majorization. -/
theorem concreteCenteredEll_two_square_eq_projectiveSandwichSquare_h14_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N) (v : ComplexUnitSphere N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    concreteCenteredEll 2 N K (A, v) ^ 2 =
      h14CenteredSandwichSecondSquare N K A v :=
  centeredLogScore_two_square_eq_h14CenteredSandwichSecondSquare_internal
    hN hgap A v hsymm hsupport

/-! ## Scalar removal before the fourth projective moment -/

/-- Scalar-free part of a matrix. -/
def h14ProjectiveTraceZeroPart {N : ℕ} (A : ConcreteMatrixState N) :
    ConcreteMatrixState N :=
  A - (((((N : ℝ)⁻¹ : ℝ) : ℂ) * Matrix.trace A) •
    (1 : ConcreteMatrixState N))

theorem trace_h14ProjectiveTraceZeroPart
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    Matrix.trace (h14ProjectiveTraceZeroPart A) = 0 := by
  have hNr : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hcast : (((N : ℝ)⁻¹ : ℝ) : ℂ) * (N : ℂ) = 1 := by
    exact_mod_cast inv_mul_cancel₀ hNr
  unfold h14ProjectiveTraceZeroPart
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
  simp only [Fintype.card_fin, smul_eq_mul]
  calc
    Matrix.trace A - (((N : ℝ)⁻¹ : ℝ) : ℂ) *
        Matrix.trace A * (N : ℂ) =
        Matrix.trace A - Matrix.trace A *
          ((((N : ℝ)⁻¹ : ℝ) : ℂ) * (N : ℂ)) := by ring
    _ = 0 := by rw [hcast]; ring

/-- Centering the trace pairing is definitionally the uncentered pairing
against the trace-zero part. -/
theorem complexProjectiveTracePair_h14ProjectiveTraceZeroPart
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) :
    complexProjectiveTracePair v (h14ProjectiveTraceZeroPart A) =
      complexCenteredProjectiveTracePair v A := by
  have hNr : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  rw [complexProjectiveTracePair_eq_trace]
  unfold h14ProjectiveTraceZeroPart complexCenteredProjectiveTracePair
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, trace_complexRankOneProjection]
  simp only [smul_eq_mul]
  rw [← complexProjectiveTracePair_eq_trace]
  ring

/-- The centered fourth projective pairing is integrable, obtained by
removing the scalar part before invoking the order-four tensor theorem. -/
theorem integrable_complexCenteredProjectiveTracePair_fourth_h14
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    Integrable (fun v : ComplexUnitSphere N ↦
      complexCenteredProjectiveTracePair v A ^ 4)
      (complexUnitSphereProbabilityMeasure N) := by
  let A0 := h14ProjectiveTraceZeroPart A
  have hInt := integrable_complexProjectiveTracePair_fourth hN A0
  apply hInt.congr
  filter_upwards [] with v
  rw [show A0 = h14ProjectiveTraceZeroPart A by rfl,
    complexProjectiveTracePair_h14ProjectiveTraceZeroPart hN v A]

/-- PROVED intermediate: exact trace-zero fourth-moment cancellation for a
centered projective pairing.  The identity is applied as a complex equality
before any absolute value is taken, so the fixed-point cycle types vanish
exactly. -/
theorem integral_complexCenteredProjectiveTracePair_fourth_eq_traceZero_h14
    {N : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    (∫ v : ComplexUnitSphere N,
      complexCenteredProjectiveTracePair v A ^ 4
      ∂(complexUnitSphereProbabilityMeasure N)) =
      ((((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2) *
        ((N : ℝ) + 3))⁻¹ : ℝ) : ℂ) *
        (3 * Matrix.trace
            (h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A) ^ 2 +
          6 * Matrix.trace
            (h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A *
              h14ProjectiveTraceZeroPart A)) := by
  let A0 := h14ProjectiveTraceZeroPart A
  have htr : Matrix.trace A0 = 0 := by
    simpa only [A0] using trace_h14ProjectiveTraceZeroPart hN A
  calc
    (∫ v : ComplexUnitSphere N,
      complexCenteredProjectiveTracePair v A ^ 4
        ∂(complexUnitSphereProbabilityMeasure N)) =
        ∫ v : ComplexUnitSphere N,
          complexProjectiveTracePair v A0 ^ 4
          ∂(complexUnitSphereProbabilityMeasure N) := by
      apply integral_congr_ae
      filter_upwards [] with v
      rw [complexProjectiveTracePair_h14ProjectiveTraceZeroPart hN v A]
    _ = _ := by
      simpa only [A0] using
        integral_complexProjectiveTracePair_fourth_of_trace_zero_h14
          hN A0 htr

/-! ## The remaining fixed-matrix contraction boundary -/

/-- The coefficient-level fixed-matrix envelope obtained when the four
projective factors are contracted before any absolute values. -/
def h14ProjectiveCancellationSharpEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  1536 * (concreteCOETraceOne N K A ^ 2 / (N : ℝ) ^ 2) +
    1280 * (concreteCOETraceTwo N K A / (N : ℝ) ^ 2) +
    3072 * (concreteCOETraceOne N K A ^ 4 /
      ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)) +
    2560 * (concreteCOETraceTwo N K A ^ 2 /
      ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))

/-- The looser positive envelope used by the beta-prime expectation layer. -/
def h14ProjectiveCancellationEnvelope (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  4096 *
    ((concreteCOETraceOne N K A ^ 2 +
        |concreteCOETraceTwo N K A|) / (N : ℝ) ^ 2 +
      concreteCOETraceOne N K A ^ 4 /
        ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2) +
      concreteCOETraceTwo N K A ^ 2 /
        ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2))

/-- Pure scalar closure: the sharp coefficient ledger is dominated by the
positive `4096` envelope. -/
theorem h14ProjectiveCancellationSharpEnvelope_le_envelope
    {N K : ℕ} (hN : 1 ≤ N) (A : ConcreteMatrixState N) :
    h14ProjectiveCancellationSharpEnvelope N K A ≤
      h14ProjectiveCancellationEnvelope N K A := by
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hn2 : 0 < (N : ℝ) ^ 2 := sq_pos_of_pos hn
  have hratio : concreteCOETraceTwo N K A / (N : ℝ) ^ 2 ≤
      |concreteCOETraceTwo N K A| / (N : ℝ) ^ 2 := by
    exact (div_le_div_iff₀ hn2 hn2).2
      (mul_le_mul_of_nonneg_right (le_abs_self _) hn2.le)
  have hOne :
      1536 * (concreteCOETraceOne N K A ^ 2 / (N : ℝ) ^ 2) ≤
        4096 * (concreteCOETraceOne N K A ^ 2 / (N : ℝ) ^ 2) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hTwo :
      1280 * (concreteCOETraceTwo N K A / (N : ℝ) ^ 2) ≤
        4096 * (|concreteCOETraceTwo N K A| / (N : ℝ) ^ 2) := by
    calc
      _ ≤ 1280 * (|concreteCOETraceTwo N K A| / (N : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ ≤ _ :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hThree :
      3072 * (concreteCOETraceOne N K A ^ 4 /
        ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)) ≤
        4096 * (concreteCOETraceOne N K A ^ 4 /
          ((N : ℝ) ^ 4 * concreteCOEExponent N K ^ 2)) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hFour :
      2560 * (concreteCOETraceTwo N K A ^ 2 /
        ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)) ≤
        4096 * (concreteCOETraceTwo N K A ^ 2 /
          ((N : ℝ) ^ 2 * concreteCOEExponent N K ^ 2)) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  unfold h14ProjectiveCancellationSharpEnvelope
    h14ProjectiveCancellationEnvelope
  rw [add_div]
  nlinarith

/-- **CONDITIONAL, non-endpoint, fixed-matrix contract.**  This is the
smallest remaining deterministic contraction: expand the two exact
sandwiches into four centered projective factors, apply the preceding
trace-zero fourth identity (and its polarization) before absolute values,
and collect the displayed coefficients.  It contains no beta-prime law,
H6 transport, score endpoint, or dimension-uniform probability estimate. -/
def H14CenteredEllTwoProjectiveContractionContract (N K : ℕ) : Prop :=
  ∀ (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)),
    Integrable (h14CenteredSandwichSecondSquare N K A)
        (complexUnitSphereProbabilityMeasure N) ∧
      (∫ v, ‖h14CenteredSandwichSecondSquare N K A v‖
          ∂(complexUnitSphereProbabilityMeasure N)) ≤
        h14ProjectiveCancellationSharpEnvelope N K A

/-- CONDITIONAL fixed-matrix package with the positive envelope.  All score
algebra, trace-zero cancellation, and coefficient weakening around the single
explicit contraction contract are internal. -/
theorem h14_fixedMatrix_projectiveCancellation_package_conditional
    {N K : ℕ}
    (Hcontract : H14CenteredEllTwoProjectiveContractionContract N K)
    (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    Integrable (h14CenteredSandwichSecondSquare N K A)
        (complexUnitSphereProbabilityMeasure N) ∧
      (∫ v, ‖h14CenteredSandwichSecondSquare N K A v‖
          ∂(complexUnitSphereProbabilityMeasure N)) ≤
        h14ProjectiveCancellationEnvelope N K A := by
  rcases Hcontract hN hgap A hsymm hsupport with ⟨hInt, hSharp⟩
  exact ⟨hInt,
    hSharp.trans (h14ProjectiveCancellationSharpEnvelope_le_envelope hN A)⟩

#print axioms concreteCenteredEll_two_eq_projectiveSandwiches_h14_internal
#print axioms concreteCenteredEll_two_square_eq_projectiveSandwichSquare_h14_internal
#print axioms trace_h14ProjectiveTraceZeroPart
#print axioms integral_complexCenteredProjectiveTracePair_fourth_eq_traceZero_h14
#print axioms h14ProjectiveCancellationSharpEnvelope_le_envelope
#print axioms h14_fixedMatrix_projectiveCancellation_package_conditional

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
