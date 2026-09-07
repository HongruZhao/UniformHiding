import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveSecondMoment
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ProjectiveContractions
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.COESupportAlgebra

/-!
# Explicit centered rank-one density scores

This module contains the algebraic target formulas for the first and second
centered COE density scores.  Keeping the definitions below the analytic
identification modules avoids an import cycle between those proofs and the
remaining quarantined boundary inputs.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Complex first density-score formula in the centered direction `Q_v`. -/
def concreteCenteredRankOneFirstDensityScoreComplex
    (N K : ℕ) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) : ℂ :=
  2 * complexCenteredProjectiveTracePair v (concreteCOEY N K A)

/-- Real first density-score formula used by the event path. -/
def concreteCenteredRankOneFirstDensityScore
    (N K : ℕ) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) : ℝ :=
  (concreteCenteredRankOneFirstDensityScoreComplex N K v A).re

/-- Complex second density-score formula in the centered direction `Q_v`. -/
def concreteCenteredRankOneSecondDensityScoreComplex
    (N K : ℕ) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) : ℂ :=
  4 *
    (complexCenteredProjectiveTracePair v (concreteCOEY N K A) ^ 2 -
      complexCenteredProjectiveSandwich v
        (concreteCOEWMatrix N K A) (concreteCOEY N K A) -
      complexCenteredProjectiveConjugateSandwich v
        (concreteCOERMatrix N K A))

/-- Real second density-score formula used by the event path. -/
def concreteCenteredRankOneSecondDensityScore
    (N K : ℕ) (v : ComplexUnitSphere N)
    (A : ConcreteMatrixState N) : ℝ :=
  (concreteCenteredRankOneSecondDensityScoreComplex N K v A).re

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
