import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10_ExactCenteredVarianceClosure

/-!
# Kernel-derived compatibility projections for H8 and H10

The historical H8/H10 declarations remain available for source compatibility.
This module exposes identically shaped centered `L^2` packages and projections
from the all-dimensional exact trace-recurrence proof, so paper-facing modules
can avoid the two legacy scientific declarations.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- All-dimensional proved replacement for the historical centered
`(Tr Y)^2` package (H8). -/
theorem betaPrimeYTraceOneSquare_centered_two_momentPackage_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
        (fun u ↦ betaPrimeYTraceOne N K u ^ 2 -
          ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm
            (fun u ↦ betaPrimeYTraceOne N K u ^ 2 -
              ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
            2 (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ) ^ 3) :=
  U08.betaPrimeYTraceOneSquare_centered_two_momentPackage_internal hN hgap

theorem betaPrimeYTraceOneSquare_centered_memLp_two_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
      (fun u ↦ betaPrimeYTraceOne N K u ^ 2 -
        ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
      2 (betaPrimeTraceFourLaw N K) :=
  (betaPrimeYTraceOneSquare_centered_two_momentPackage_proved_allDimensions
    hN hgap).1

theorem betaPrimeYTraceOneSquare_centered_lpNorm_two_le_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm
        (fun u ↦ betaPrimeYTraceOne N K u ^ 2 -
          ∫ z, betaPrimeYTraceOne N K z ^ 2 ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ≤
      denseClassicalMomentConstant * (N : ℝ) ^ 3 :=
  (betaPrimeYTraceOneSquare_centered_two_momentPackage_proved_allDimensions
    hN (by omega)).2 hdense

/-- All-dimensional proved replacement for the historical centered
`Tr(Y^2)` package (H10). -/
theorem betaPrimeYTraceTwo_centered_two_momentPackage_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
        (fun u ↦ betaPrimeYTraceTwo N K u -
          ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ∧
      (16 * N ≤ K →
        lpNorm
            (fun u ↦ betaPrimeYTraceTwo N K u -
              ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
            2 (betaPrimeTraceFourLaw N K) ≤
          denseClassicalMomentConstant * (N : ℝ) ^ 2) :=
  U08.betaPrimeYTraceTwo_centered_two_momentPackage_internal hN hgap

theorem betaPrimeYTraceTwo_centered_memLp_two_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp
      (fun u ↦ betaPrimeYTraceTwo N K u -
        ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
      2 (betaPrimeTraceFourLaw N K) :=
  (betaPrimeYTraceTwo_centered_two_momentPackage_proved_allDimensions
    hN hgap).1

theorem betaPrimeYTraceTwo_centered_lpNorm_two_le_proved_allDimensions
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm
        (fun u ↦ betaPrimeYTraceTwo N K u -
          ∫ z, betaPrimeYTraceTwo N K z ∂betaPrimeTraceFourLaw N K)
        2 (betaPrimeTraceFourLaw N K) ≤
      denseClassicalMomentConstant * (N : ℝ) ^ 2 :=
  (betaPrimeYTraceTwo_centered_two_momentPackage_proved_allDimensions
    hN (by omega)).2 hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
