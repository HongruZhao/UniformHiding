import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCOEStatistics

/-!
# Definition-only centered trace coordinates for the cubic score

This module isolates the six algebraic coordinates used by the exact
projective-moment calculation.  It has no moment, differentiability, or
external-result input.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

def concreteCOECenteredMatrixTraceOne (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  concreteCOETraceOne N K A - (N : ℝ) * ((N : ℝ) + 1)

def concreteCOECenteredMatrixTraceTwo (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  concreteCOETraceTwo N K A -
    2 * ((N : ℝ) + 1) * concreteCOETraceOne N K A +
    (N : ℝ) * ((N : ℝ) + 1) ^ 2

def concreteCOECenteredMatrixTraceThree (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  concreteCOETraceThree N K A -
    3 * ((N : ℝ) + 1) * concreteCOETraceTwo N K A +
    3 * ((N : ℝ) + 1) ^ 2 * concreteCOETraceOne N K A -
    (N : ℝ) * ((N : ℝ) + 1) ^ 3

/-- Closed first projective moment of `s_v=Tr(P_v S)`. -/
def concreteProjectiveMeanS (N K : ℕ) (A : ConcreteMatrixState N) : ℝ :=
  concreteCOECenteredMatrixTraceOne N K A / (N : ℝ)

/-- Closed second projective moment of `s_v`. -/
def concreteProjectiveMeanSSquare (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  (concreteCOECenteredMatrixTraceOne N K A ^ 2 +
    concreteCOECenteredMatrixTraceTwo N K A) /
      ((N : ℝ) * ((N : ℝ) + 1))

/-- Closed third projective moment of `s_v`. -/
def concreteProjectiveMeanSCube (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  (concreteCOECenteredMatrixTraceOne N K A ^ 3 +
      3 * concreteCOECenteredMatrixTraceOne N K A *
        concreteCOECenteredMatrixTraceTwo N K A +
      2 * concreteCOECenteredMatrixTraceThree N K A) /
    ((N : ℝ) * ((N : ℝ) + 1) * ((N : ℝ) + 2))

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
