import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeRelaxedProjectiveClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_BellLowerPackageFromRelaxedH13

/-!
# Literal all-dimensional H11 closure

The completed relaxed-strong H13 product package feeds the already proved
fourth-density normalization, support sign, and lower Bell-monomial assembly.
No residual deterministic or probabilistic premise remains.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Literal public H11 endpoint under the approved A1--A4 inputs. -/
theorem centeredLogScore_four_momentPackage_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hgap : 2 * N + 8 ≤ K) :
    MemLp (concreteCenteredEll 4 N K) 1
        (concreteCenteredScoreProductLaw N K) ∧
      (16 * N ≤ K →
        lpNorm (concreteCenteredEll 4 N K) 1
            (concreteCenteredScoreProductLaw N K) ≤
          centeredLogScoreFourthMomentConstant * (N : ℝ) ^ 2) :=
  centeredLogScore_four_momentPackage_of_relaxedH13 hN hgap
    (centeredLogScore_oneThree_momentPackage_relaxed_strong_proved_A1A2A3A4
      hN hgap)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
