import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCOEStatistics

/-!
# Definition-only trace coordinates for the cubic bilinear term

These three rational trace expressions are used by the exact projective
contraction independently of their later moment bounds.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- `Tr[Z(I+Z)]`, expressed through `Tr Y` and `Tr Y^2`. -/
def concreteCOETraceZW (N K : ℕ) (A : ConcreteMatrixState N) : ℝ :=
  concreteCOETraceOne N K A / concreteCOEExponent N K +
    concreteCOETraceTwo N K A / concreteCOEExponent N K ^ 2

/-- `Tr Z * Tr[Z(I+Z)]`. -/
def concreteCOETraceZTraceZW (N K : ℕ) (A : ConcreteMatrixState N) : ℝ :=
  concreteCOETraceOne N K A ^ 2 / concreteCOEExponent N K ^ 2 +
    (concreteCOETraceOne N K A * concreteCOETraceTwo N K A) /
      concreteCOEExponent N K ^ 3

/-- `Tr[Z^2(I+Z)]`. -/
def concreteCOETraceZTwoW (N K : ℕ) (A : ConcreteMatrixState N) : ℝ :=
  concreteCOETraceTwo N K A / concreteCOEExponent N K ^ 2 +
    concreteCOETraceThree N K A / concreteCOEExponent N K ^ 3

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
