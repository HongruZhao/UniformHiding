import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7CentralScalar
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCentralScore
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ConcreteCubicNonWDefinitions

/-!
# Central cubic score definitions

The central-line H7 calculus needs only these two explicit polynomials.  They
are isolated from the optional moment-bound consumers so exact H7 does not
inherit dormant classical moment declarations through a broad source import.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Third logarithmic score for scalar transpose congruence. -/
def concreteCentralLogScoreThree (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  32 * (concreteCOETraceOne N K A +
    3 * concreteCOETraceTwo N K A / concreteCOEExponent N K +
    2 * concreteCOETraceThree N K A / concreteCOEExponent N K ^ 2)

/-- Third central density Bell polynomial. -/
def concreteCentralDensityScoreThree (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  densityBellThree
    (concreteCentralLogScoreOne N K A)
    (concreteCentralLogScoreTwo N K A)
    (concreteCentralLogScoreThree N K A)

/-- The centered first trace times `Tr Y`. -/
def concreteCentralSOneTraceOne (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  concreteCOECenteredMatrixTraceOne N K A * concreteCOETraceOne N K A

/-- The centered first trace times `Tr Y²`. -/
def concreteCentralSOneTraceTwo (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  concreteCOECenteredMatrixTraceOne N K A * concreteCOETraceTwo N K A

/-- Exact six-term trace expansion of the third central density score. -/
theorem concreteCentralDensityScoreThree_expansion
    {N K : ℕ} (A : ConcreteMatrixState N) :
    concreteCentralDensityScoreThree N K A =
      8 * concreteCOECenteredMatrixTraceOne N K A ^ 3 -
      48 * concreteCentralSOneTraceOne N K A -
      (48 / concreteCOEExponent N K) *
        concreteCentralSOneTraceTwo N K A +
      32 * concreteCOETraceOne N K A +
      (96 / concreteCOEExponent N K) * concreteCOETraceTwo N K A +
      (64 / concreteCOEExponent N K ^ 2) *
        concreteCOETraceThree N K A := by
  simp only [concreteCentralDensityScoreThree, densityBellThree,
    concreteCentralLogScoreOne, concreteCentralLogScoreTwo,
    concreteCentralLogScoreThree, concreteCOECenteredMatrixTraceOne,
    concreteCentralSOneTraceOne, concreteCentralSOneTraceTwo]
  ring

end


end LogdetLean.GramHafnian.UltimateHiding.DenseScore
