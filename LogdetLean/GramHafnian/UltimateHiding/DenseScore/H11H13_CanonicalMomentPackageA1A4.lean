import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11H13_CanonicalFourthScoreRewireCore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H13_OneThreeRelaxedProjectiveClosure
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H11_FourthMomentClosureA1A4
import Mathlib.Tactic

/-!
# No-premise H11/H13 canonical moment-family adapter

This is the narrow adapter between the two completed all-dimensional moment
proofs and the already compiled downstream fourth-score consumer core.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

/-- Concrete H11/H13 moment package in every dense dimension. -/
theorem concreteCenteredH11H13MomentPackage_proved_A1A2A3A4
    {N K : ℕ} (hN : 1 ≤ N) (hdense : 16 * N ≤ K) :
    ConcreteCenteredH11H13MomentPackage N K := by
  have hgap : 2 * N + 8 ≤ K := by omega
  exact concreteCenteredH11H13MomentPackage_of_momentPackages hdense
    (centeredLogScore_oneThree_momentPackage_proved_A1A2A3A4 hN hgap)
    (centeredLogScore_four_momentPackage_proved_A1A2A3A4 hN hgap)

/-- Dimension-uniform no-premise producer consumed by the canonical score
certificate and paper-facing hiding reducers. -/
theorem concreteCenteredH11H13MomentPackageFamily_proved_A1A2A3A4 :
    ConcreteCenteredH11H13MomentPackageFamily := by
  intro N K hN hdense
  exact concreteCenteredH11H13MomentPackage_proved_A1A2A3A4 hN hdense

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
