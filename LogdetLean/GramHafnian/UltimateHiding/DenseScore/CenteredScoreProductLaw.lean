import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredLikelihood
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Centered score product law

This axiom-free release module isolates the common COE/projective product
measure from the historical external moment package that originally housed
the definition.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.LocalAnticoncentration

/-- The scaled COE corner law paired with the uniform complex projective
direction law. -/
def concreteCenteredScoreProductLaw (N K : ℕ) :=
  (concreteScaledCOECornerLaw
      canonicalUnitaryHaarProbabilityFamily N K).prod
    (complexUnitSphereProbabilityMeasure N)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
