import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteRankOneCubicIdentification
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCubicWDefinitions

/-!
# Definition-only averaged rank-one cubic density

The exact projective identity needs this closed expression but not its later
`L^1` estimate.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Closed projective average of the rank-one third density score. -/
def concreteAveragedRankOneCubicDensity (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  averagedCubicNonWExpression (N : ℝ) (concreteCOEExponent N K)
      (concreteProjectiveMeanS N K A)
      (concreteProjectiveMeanSSquare N K A)
      (concreteProjectiveMeanSCube N K A) +
    averagedCubicWTraceExpression (N : ℝ) (concreteCOEExponent N K)
      (concreteCOETraceZW N K A)
      (concreteCOETraceZTraceZW N K A)
      (concreteCOETraceZTwoW N K A)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
