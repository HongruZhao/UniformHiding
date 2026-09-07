import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_A2Prime_A1TraceTransport
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.ClassicalMomentBoundsExternal

/-!
# Concrete beta-prime trace coordinates

This small definition-only module exposes the four beta-prime trace
coordinates on the concrete COE matrix state.  It is intentionally separate
from the optional moment-transfer bundles, so consumers of the coordinates do
not import dormant classical moment assumptions.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- First beta-prime trace coordinate on the concrete COE state. -/
def concreteBetaPrimeYTraceOne (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  betaPrimeYTraceOne N K (concreteCOETracePowerVector 4 N K A)

/-- Second beta-prime trace coordinate on the concrete COE state. -/
def concreteBetaPrimeYTraceTwo (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  betaPrimeYTraceTwo N K (concreteCOETracePowerVector 4 N K A)

/-- Third beta-prime trace coordinate on the concrete COE state. -/
def concreteBetaPrimeYTraceThree (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  betaPrimeYTraceThree N K (concreteCOETracePowerVector 4 N K A)

/-- Fourth beta-prime trace coordinate on the concrete COE state. -/
def concreteBetaPrimeYTraceFour (N K : ℕ)
    (A : ConcreteMatrixState N) : ℝ :=
  betaPrimeYTraceFour N K (concreteCOETracePowerVector 4 N K A)

/-- Coordinate one is literally the concrete `Tr Y`. -/
@[simp] theorem concreteBetaPrimeYTraceOne_eq_concreteCOETraceOne
    (N K : ℕ) (A : ConcreteMatrixState N) :
    concreteBetaPrimeYTraceOne N K A = concreteCOETraceOne N K A := by
  unfold concreteBetaPrimeYTraceOne betaPrimeYTraceOne
    concreteCOETracePowerVector concreteCOETraceOne concreteCOEY
    concreteRealTrace
  simp [pow_succ, Complex.mul_re]

/-- Coordinate two is literally the concrete `Tr Y^2`. -/
@[simp] theorem concreteBetaPrimeYTraceTwo_eq_concreteCOETraceTwo
    (N K : ℕ) (A : ConcreteMatrixState N) :
    concreteBetaPrimeYTraceTwo N K A = concreteCOETraceTwo N K A := by
  unfold concreteBetaPrimeYTraceTwo betaPrimeYTraceTwo
    concreteCOETracePowerVector concreteCOETraceTwo concreteCOEY
    concreteRealTrace
  simp [pow_succ, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_smul, Complex.mul_re]

/-- Coordinate three is literally the concrete `Tr Y^3`. -/
@[simp] theorem concreteBetaPrimeYTraceThree_eq_concreteCOETraceThree
    (N K : ℕ) (A : ConcreteMatrixState N) :
    concreteBetaPrimeYTraceThree N K A = concreteCOETraceThree N K A := by
  unfold concreteBetaPrimeYTraceThree betaPrimeYTraceThree
    concreteCOETracePowerVector concreteCOETraceThree concreteCOEY
    concreteRealTrace
  simp [pow_succ, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_smul, Complex.mul_re]
  left
  ring

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
