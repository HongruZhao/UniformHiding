import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.InverseWishartSecondEntryStein

/-!
# Unconditional contractions of the inverse-Wishart second-entry tensor

This module combines the proved Stein tensor with the previously checked
finite Gaussian Wick layer.  It contains denominator means and the valid
traceless H12-scale corollary only; the disproved raw H14 `N^2` route is not
reintroduced.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08

noncomputable section

theorem scaledInverseWishartTraceTwo_integral_eq_ledger_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    (∫ H, Matrix.trace ((scaledInverseWishartMatrix N K H) ^ 2)
      ∂(standardRealGaussianMatrixMeasure (K - N) N)) =
      scaledInverseWishartTraceTwoMeanLedger (N : ℝ)
        (concreteCOEExponent N K) :=
  scaledInverseWishartTraceTwo_integral_eq_ledger_conditional hgap
    (scaledInverseWishartSecondEntryMomentFormula_internal hgap)

theorem scaledInverseWishartTraceOneSquare_integral_eq_ledger_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    (∫ H, Matrix.trace (scaledInverseWishartMatrix N K H) ^ 2
      ∂(standardRealGaussianMatrixMeasure (K - N) N)) =
      scaledInverseWishartTraceOneSquareMeanLedger (N : ℝ)
        (concreteCOEExponent N K) :=
  scaledInverseWishartTraceOneSquare_integral_eq_ledger_conditional hgap
    (scaledInverseWishartSecondEntryMomentFormula_internal hgap)

theorem betaPrimeYTraceTwo_integral_eq_ledger_internal
    {N K : ℕ} (hgap : 2 * N + 8 ≤ K) :
    (∫ u, betaPrimeYTraceTwo N K u ∂(betaPrimeTraceFourLaw N K)) =
      betaPrimeYTraceTwoMeanLedger (N : ℝ)
        (concreteCOEExponent N K) :=
  betaPrimeYTraceTwo_integral_eq_ledger_conditional hgap
    (scaledInverseWishartSecondEntryMomentFormula_internal hgap)
    (betaPrimeSecondOrderFiniteWickFormula_internal hgap)

theorem betaPrimeTracelessQuadraticFormalMeanU08_eq_ledger_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    betaPrimeTracelessQuadraticFormalMeanU08 N K =
      betaPrimeTracelessQuadraticMeanLedger (N : ℝ)
        (concreteCOEExponent N K) :=
  betaPrimeTracelessQuadraticFormalMeanU08_eq_ledger_conditional
    hN hgap
    (scaledInverseWishartSecondEntryMomentFormula_internal hgap)
    (betaPrimeSecondOrderFiniteWickFormula_internal hgap)

/-- Valid probability contract for U10's H12 assembly in the sharp dense
regime. -/
theorem abs_betaPrimeTracelessQuadraticFormalMeanU08_le_denseConstant_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    16 * N ≤ K →
      |betaPrimeTracelessQuadraticFormalMeanU08 N K| ≤
        denseClassicalMomentConstant * (N : ℝ) ^ 3 :=
  abs_betaPrimeTracelessQuadraticFormalMeanU08_le_denseConstant_conditional
    hN hgap
    (scaledInverseWishartSecondEntryMomentFormula_internal hgap)
    (betaPrimeSecondOrderFiniteWickFormula_internal hgap)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
