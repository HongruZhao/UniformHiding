import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7CentralLogdetJets
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7CentralLineConditional

/-!
# Unconditional H7 central-line closure

This module discharges the three explicit trace-jet parameters of the earlier
conditional assembly using the literal determinant calculation in
`H7CentralLogdetJets`.  It does not import or use the original H7 external
declaration.
-/

open Function
open scoped Matrix Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

theorem h7_concreteCOEExponent_ne_zero_of_boundary
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K) :
    concreteCOEExponent N K ≠ 0 := by
  have hcast : (2 : ℝ) * (N : ℝ) + 1 < (K : ℝ) := by
    exact_mod_cast (show 2 * N + 1 < K by omega)
  unfold concreteCOEExponent
  linarith

theorem h7CentralLogModel_jet_one_derived
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    iteratedDeriv 1 (h7CentralLogModel K A) 0 =
      concreteCentralLogScoreOne N K A := by
  apply h7CentralLogModel_jet_one_CONDITIONAL hboundary A hsupport
  exact h7CentralLogDeterminantRatio_jet_one A hsupport
    (h7_concreteCOEExponent_ne_zero_of_boundary hboundary)

theorem h7CentralLogModel_jet_two_derived
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    iteratedDeriv 2 (h7CentralLogModel K A) 0 =
      concreteCentralLogScoreTwo N K A := by
  apply h7CentralLogModel_jet_two_CONDITIONAL hboundary A hsupport
  exact h7CentralLogDeterminantRatio_jet_two A hsupport
    (h7_concreteCOEExponent_ne_zero_of_boundary hboundary)

theorem h7CentralLogModel_jet_three_derived
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    iteratedDeriv 3 (h7CentralLogModel K A) 0 =
      concreteCentralLogScoreThree N K A := by
  apply h7CentralLogModel_jet_three_CONDITIONAL hboundary A hsupport
  exact h7CentralLogDeterminantRatio_jet_three A hsupport
    (h7_concreteCOEExponent_ne_zero_of_boundary hboundary)

/-- The third derivative of the literal central likelihood is the explicit
central cubic density score. -/
theorem h7CentralLikelihoodCore_iteratedDeriv_three_derived
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    iteratedDeriv 3 (h7CentralLikelihoodCore K A) 0 =
      concreteCentralDensityScoreThree N K A := by
  have hc := h7_concreteCOEExponent_ne_zero_of_boundary hboundary
  exact h7CentralLikelihoodCore_iteratedDeriv_three_CONDITIONAL
    hboundary A hsupport
    (h7CentralLogDeterminantRatio_jet_one A hsupport hc)
    (h7CentralLogDeterminantRatio_jet_two A hsupport hc)
    (h7CentralLogDeterminantRatio_jet_three A hsupport hc)

/-- Central diagonal identification for the literal coordinate likelihood. -/
theorem h16CoordinateLikelihoodCore_central_iteratedDeriv_three_derived
    {N K : ℕ} (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    iteratedDeriv 3
        (fun t : ℝ => h16CoordinateLikelihoodCore K A
          (t • concreteMatrixRealCoordinates (1 : ConcreteMatrixState N))) 0 =
      concreteCentralDensityScoreThree N K A := by
  rw [h16CoordinateLikelihoodCore_central_line]
  exact h7CentralLikelihoodCore_iteratedDeriv_three_derived
    hboundary A hsupport

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
