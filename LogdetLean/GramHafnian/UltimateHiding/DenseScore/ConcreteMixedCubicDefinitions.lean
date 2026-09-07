import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCenteredQuadraticScore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.MixedScalarQuadraticClosure

/-!
# Mixed central-quadratic cubic definitions

This definition-only layer separates the literal H7 mixed polynomial from
its optional moment bounds.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Scalar derivative of the normalized centered quadratic density. -/
def concreteCentralDerivativeCenteredQuadraticDensity (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  4 / ((N : ℝ) * ((N : ℝ) + 1)) *
    centralDerivativeQuadraticTraceBracket
      (N : ℝ) (concreteCOEExponent N K)
      (concreteCOETraceOne N K A)
      (concreteCOETraceTwo N K A)
      (concreteCOETraceThree N K A)

/-- Signed density representing the mixed operator `X_I(D₂ μ)`. -/
def concreteMixedScalarQuadraticDensity (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  concreteCentralLogScoreOne N K A *
      concreteCenteredQuadraticDensity N K A -
    concreteCentralDerivativeCenteredQuadraticDensity N K A

end


end LogdetLean.GramHafnian.UltimateHiding.DenseScore
