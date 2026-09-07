import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredLikelihood
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.FourthBellMomentClosure

/-!
# Dimension-one sanity for the literal centered fourth score

This small referee module checks the decisive degeneracy test for the
fourth-order route.  In dimension one `Q_v = 0`, so both the literal fourth
density derivative and the fourth Bell polynomial in the literal log
derivatives vanish.  No probabilistic or external input is used.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The fourth Bell polynomial in the literal centered log derivatives is
zero in dimension one. -/
theorem concreteCenteredDensityBellFour_fin_one_eq_zero
    (K : ℕ) (v : ComplexUnitSphere 1) (A : ConcreteMatrixState 1) :
    densityBellFour
      (concreteCenteredLogScore 1 1 K v A)
      (concreteCenteredLogScore 2 1 K v A)
      (concreteCenteredLogScore 3 1 K v A)
      (concreteCenteredLogScore 4 1 K v A) = 0 := by
  rw [concreteCenteredLogScore_fin_one_eq_zero (by omega : 1 ≤ 1),
    concreteCenteredLogScore_fin_one_eq_zero (by omega : 1 ≤ 2),
    concreteCenteredLogScore_fin_one_eq_zero (by omega : 1 ≤ 3),
    concreteCenteredLogScore_fin_one_eq_zero (by omega : 1 ≤ 4)]
  simp [densityBellFour]

/-- The literal fourth density derivative agrees with its Bell expression in
dimension one because both sides vanish identically. -/
theorem concreteCenteredDensityScore_four_eq_bell_fin_one
    (K : ℕ) (v : ComplexUnitSphere 1) (A : ConcreteMatrixState 1) :
    concreteCenteredDensityScore 4 1 K v A =
      densityBellFour
        (concreteCenteredLogScore 1 1 K v A)
        (concreteCenteredLogScore 2 1 K v A)
        (concreteCenteredLogScore 3 1 K v A)
        (concreteCenteredLogScore 4 1 K v A) := by
  rw [concreteCenteredDensityScore_fin_one_eq_zero (by omega : 1 ≤ 4),
    concreteCenteredDensityBellFour_fin_one_eq_zero]

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
