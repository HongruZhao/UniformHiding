import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteAveragedRankOneCubicDefinitions
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteMixedCubicDefinitions
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCentralCubicDefinitions

/-!
# Definition-only averaged centered cubic density

The exact H7 adapter needs the signed density itself, but none of the later
moment bounds.  Keeping the definition here prevents a proof-only consumer
from importing those dormant estimates.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The signed density on the right of the exact centered cubic identity. -/
def concreteAveragedCenteredCubicDensity (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  concreteAveragedRankOneCubicDensity N K A -
    (3 / (N : ℝ)) * concreteMixedScalarQuadraticDensity N K A -
    (1 / (N : ℝ) ^ 3) * concreteCentralDensityScoreThree N K A

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
