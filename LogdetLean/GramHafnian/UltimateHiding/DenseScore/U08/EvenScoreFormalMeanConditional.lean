import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartSecondEntryMomentConditional
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.BetaPrimeTraceTwoCounterexample
import Mathlib.Tactic

/-!
# CONDITIONAL even-score formal means from the reusable second-moment ledger

This module is the probability-only bridge requested by the H12/H14
consumer.  It introduces no axiom.  Its two explicit theorem parameters are
strictly lower-level than either consumer conclusion:

* the denominator-only inverse-Wishart product of two entries, and
* the two finite standard-Gaussian numerator Wick contractions.

The first contract is isolated in
`InverseWishartSecondEntryMomentConditional`; the second is stated below as
two uncentered source integral identities.  From them, the exact traceless
formal mean is identified with the axiom-free rational ledger and the dense
`N^3` bound follows.

The raw trace-two mean is also identified with its ledger.  That ledger is
genuinely cubic, consistently with the unconditional counterexample in
`BetaPrimeTraceTwoCounterexample`; therefore no `O(N^2)` raw-mean theorem is
asserted here.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

/-- The literal formal mean used by the downstream H12 contract.  The U10
definition `betaPrimeTracelessQuadraticFormalMean` unfolds to this expression. -/
def betaPrimeTracelessQuadraticFormalMeanU08 (N K : ℕ) : ℝ :=
  (∫ u, betaPrimeYTraceTwo N K u ∂(betaPrimeTraceFourLaw N K)) -
    (N : ℝ)⁻¹ *
      (∫ u, betaPrimeYTraceOne N K u ^ 2
        ∂(betaPrimeTraceFourLaw N K))

/-- **CONDITIONAL finite-Gaussian input.**  The two elementary Wick/Fubini
identities for the independent numerator Wishart matrix.  The right sides
retain the literal denominator Gaussian integrals, so this contract contains
no inverse-Wishart moment assertion and no H8/H10/H12/H14 conclusion. -/
structure BetaPrimeSecondOrderFiniteWickFormula (N K : ℕ) : Prop where
  traceTwo_source_integral_eq :
    (∫ source, betaPrimeTraceTwoSource N K source
      ∂(realBetaPrimeGaussianSourceLaw N K)) =
      ((N + 1 : ℕ) : ℝ) * ((N + 2 : ℕ) : ℝ) *
          (∫ H, Matrix.trace ((scaledInverseWishartMatrix N K H) ^ 2)
            ∂(standardRealGaussianMatrixMeasure (K - N) N)) +
        ((N + 1 : ℕ) : ℝ) *
          (∫ H, Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2
            ∂(standardRealGaussianMatrixMeasure (K - N) N))
  traceOneSquare_source_integral_eq :
    (∫ source, betaPrimeTraceOneSource N K source ^ 2
      ∂(realBetaPrimeGaussianSourceLaw N K)) =
      ((N + 1 : ℕ) : ℝ) ^ 2 *
          (∫ H, Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2
            ∂(standardRealGaussianMatrixMeasure (K - N) N)) +
        2 * ((N + 1 : ℕ) : ℝ) *
          (∫ H, Matrix.trace ((scaledInverseWishartMatrix N K H) ^ 2)
            ∂(standardRealGaussianMatrixMeasure (K - N) N))

/-- The square of the exposed first trace has exactly the literal source
integral after the already proved measurable pushforward. -/
theorem betaPrimeYTraceOneSquare_integral_eq_source_internal (N K : ℕ) :
    (∫ u, betaPrimeYTraceOne N K u ^ 2
      ∂(betaPrimeTraceFourLaw N K)) =
      ∫ source, betaPrimeTraceOneSource N K source ^ 2
        ∂(realBetaPrimeGaussianSourceLaw N K) := by
  have htrace : Measurable (betaPrimeYTraceOne N K) := by
    unfold betaPrimeYTraceOne
    exact measurable_const.mul (measurable_pi_apply _)
  unfold betaPrimeTraceFourLaw
  rw [integral_map
    (measurable_realBetaPrimeTracePowerVector_internal 4 N K).aemeasurable
    (htrace.pow_const 2).aestronglyMeasurable]
  rfl

/-- The finite Wick formula and denominator entry formula identify the actual
raw trace-two integral with the exact rational ledger. -/
theorem betaPrimeYTraceTwo_integral_eq_ledger_conditional
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K)
    (Hmom : ScaledInverseWishartSecondEntryMomentFormula N K)
    (HWick : BetaPrimeSecondOrderFiniteWickFormula N K) :
    (∫ u, betaPrimeYTraceTwo N K u ∂(betaPrimeTraceFourLaw N K)) =
      betaPrimeYTraceTwoMeanLedger (N : ℝ)
        (concreteCOEExponent N K) := by
  rw [betaPrimeYTraceTwo_integral_eq_source_internal,
    HWick.traceTwo_source_integral_eq,
    scaledInverseWishartTraceTwo_integral_eq_ledger_conditional hgap Hmom,
    scaledInverseWishartTraceOneSquare_integral_eq_ledger_conditional hgap Hmom]
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
    betaPrimeYTraceTwoMeanLedger_contraction
      (N : ℝ) (concreteCOEExponent N K)

/-- Exact identification of the downstream H12 formal mean with the
traceless rational ledger. -/
theorem betaPrimeTracelessQuadraticFormalMeanU08_eq_ledger_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hmom : ScaledInverseWishartSecondEntryMomentFormula N K)
    (HWick : BetaPrimeSecondOrderFiniteWickFormula N K) :
    betaPrimeTracelessQuadraticFormalMeanU08 N K =
      betaPrimeTracelessQuadraticMeanLedger (N : ℝ)
        (concreteCOEExponent N K) := by
  have hNne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  unfold betaPrimeTracelessQuadraticFormalMeanU08
  rw [betaPrimeYTraceTwo_integral_eq_source_internal,
    betaPrimeYTraceOneSquare_integral_eq_source_internal,
    HWick.traceTwo_source_integral_eq,
    HWick.traceOneSquare_source_integral_eq,
    scaledInverseWishartTraceTwo_integral_eq_ledger_conditional hgap Hmom,
    scaledInverseWishartTraceOneSquare_integral_eq_ledger_conditional hgap Hmom]
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
    betaPrimeTracelessQuadraticMeanLedger_contraction
      (N : ℝ) (concreteCOEExponent N K) hNne

/-- The exact dense H12 mean contract, conditional only on the reusable
denominator entry tensor and the finite numerator Wick identities. -/
theorem abs_betaPrimeTracelessQuadraticFormalMeanU08_le_denseConstant_conditional
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K)
    (Hmom : ScaledInverseWishartSecondEntryMomentFormula N K)
    (HWick : BetaPrimeSecondOrderFiniteWickFormula N K) :
    16 * N ≤ K →
      |betaPrimeTracelessQuadraticFormalMeanU08 N K| ≤
        denseClassicalMomentConstant * (N : ℝ) ^ 3 := by
  intro hdense
  rw [betaPrimeTracelessQuadraticFormalMeanU08_eq_ledger_conditional
    hN hgap Hmom HWick]
  exact abs_betaPrimeTracelessQuadraticMeanLedger_le_denseConstant
    (by exact_mod_cast hN)
    (thirteen_mul_dimension_le_concreteCOEExponent_of_dense hN hdense)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
