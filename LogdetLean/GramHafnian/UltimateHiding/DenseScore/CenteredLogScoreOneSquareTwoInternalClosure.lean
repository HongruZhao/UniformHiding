import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredLogScoreOneSquareTwoDerived
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H14_ExactMomentClosure
import Mathlib.Tactic

/-!
# Internal mixed first/second centered-score closure

This module instantiates the axiom-free Young-inequality reducer with the
proved H14 second-square package.  Keeping the instantiation downstream of
H14 lets the H14 integration proof import the score-measurability lemmas
without creating an import cycle.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Backward-compatible closure using the proved second-square package. -/
theorem centeredLogScore_oneSquareTwo_momentPackage_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 2 *
      concreteCenteredEll 2 N K p) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 2 *
          concreteCenteredEll 2 N K p) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) :=
  centeredLogScore_oneSquareTwo_momentPackage_of_twoSquare hN hgap
    (centeredLogScore_twoSquare_momentPackage_proved_A1A2A3 hN hgap)

theorem centeredLogScore_oneSquareTwo_memLp_one_internal
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (fun p ↦ concreteCenteredEll 1 N K p ^ 2 *
      concreteCenteredEll 2 N K p) 1
      (concreteCenteredScoreProductLaw N K) :=
  (centeredLogScore_oneSquareTwo_momentPackage_internal hN hgap).1

theorem centeredLogScore_oneSquareTwo_lpNorm_one_le_internal
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    lpNorm (fun p ↦ concreteCenteredEll 1 N K p ^ 2 *
      concreteCenteredEll 2 N K p) 1
        (concreteCenteredScoreProductLaw N K) ≤
      centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2 :=
  (centeredLogScore_oneSquareTwo_momentPackage_internal hN (by omega)).2 hdense

end


end LogdetLean.GramHafnian.UltimateHiding.DenseScore
