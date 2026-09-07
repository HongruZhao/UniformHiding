import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.SecondEntryMomentCorollaries
import Mathlib.Tactic

/-!
# U08 cubic trace-two mean adapter for H14 projective cancellation

This module exposes the proved probability calculation in exactly the cubic
rational shape consumed by U10's projective-cancellation algebra.  It does not
reprove U10's ordered-field estimate and does not assert the false raw
`O(N^2)` mean bound.

The final theorem is explicitly CONDITIONAL only on U10's already proved,
dimension-free ordered-field lemma.  Its parameter is strictly algebraic and
contains no probability statement, score statement, or H3--H18 endpoint.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

/-- The literal beta-prime trace-two formal mean used by the H14 consumer. -/
def betaPrimeYTraceTwoFormalMeanU08 (N K : ℕ) : ℝ :=
  ∫ u, betaPrimeYTraceTwo N K u ∂(betaPrimeTraceFourLaw N K)

/-- PROVED intermediate probability producer.  In the dense regime, the
literal beta-prime trace-two formal mean is exactly the cubic rational
expression expected by U10's pure algebra lemma. -/
theorem betaPrimeYTraceTwoFormalMeanU08_eq_h14_cubic_formula_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    betaPrimeYTraceTwoFormalMeanU08 N K =
      (N : ℝ) * ((N : ℝ) + 1) * concreteCOEExponent N K *
          (2 * ((N : ℝ) + 1) * concreteCOEExponent N K +
            (N : ℝ) ^ 2 + (N : ℝ) + 2) /
        ((concreteCOEExponent N K + 1) *
          (concreteCOEExponent N K - 2)) := by
  have hgap : 2 * N + 8 ≤ K := by omega
  unfold betaPrimeYTraceTwoFormalMeanU08
  rw [betaPrimeYTraceTwo_integral_eq_ledger_internal hgap]
  rfl

/-- PROVED intermediate adapter surface.  It supplies the exact probability
identity together with precisely the two ordered-field side conditions needed
by U10's cubic ledger estimate. -/
theorem betaPrimeYTraceTwoFormalMeanU08_h14_cubic_ledger_adapter_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    betaPrimeYTraceTwoFormalMeanU08 N K =
        (N : ℝ) * ((N : ℝ) + 1) * concreteCOEExponent N K *
            (2 * ((N : ℝ) + 1) * concreteCOEExponent N K +
              (N : ℝ) ^ 2 + (N : ℝ) + 2) /
          ((concreteCOEExponent N K + 1) *
            (concreteCOEExponent N K - 2)) ∧
      1 ≤ (N : ℝ) ∧
      13 * (N : ℝ) ≤ concreteCOEExponent N K := by
  refine ⟨betaPrimeYTraceTwoFormalMeanU08_eq_h14_cubic_formula_internal
      hN hdense, ?_, thirteen_mul_dimension_le_concreteCOEExponent_of_dense
      hN hdense⟩
  exact_mod_cast hN

/-- CONDITIONAL cross-worker splice.  Instantiate `hledgerBound` with U10's
kernel-checked
`h14_betaPrimeYTraceTwoMeanLedgerFormula_abs_le_twenty_cube`; no U10 algebra
is duplicated here.  This cubic estimate is an intermediate input to the
trace-zero projective cancellation route, not the literal H14 endpoint. -/
theorem betaPrimeYTraceTwoFormalMeanU08_abs_le_twenty_cube_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K)
    (hledgerBound :
      ∀ {p c : ℝ}, 1 ≤ p → 13 * p ≤ c →
        |p * (p + 1) * c *
              (2 * (p + 1) * c + p ^ 2 + p + 2) /
            ((c + 1) * (c - 2))| ≤
          20 * p ^ 3) :
    |betaPrimeYTraceTwoFormalMeanU08 N K| ≤
      20 * (N : ℝ) ^ 3 := by
  rcases betaPrimeYTraceTwoFormalMeanU08_h14_cubic_ledger_adapter_internal
      hN hdense with ⟨hmean, hp, hc⟩
  rw [hmean]
  exact hledgerBound hp hc

#print axioms betaPrimeYTraceTwoFormalMeanU08_eq_h14_cubic_formula_internal
#print axioms betaPrimeYTraceTwoFormalMeanU08_h14_cubic_ledger_adapter_internal
#print axioms betaPrimeYTraceTwoFormalMeanU08_abs_le_twenty_cube_conditional

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
