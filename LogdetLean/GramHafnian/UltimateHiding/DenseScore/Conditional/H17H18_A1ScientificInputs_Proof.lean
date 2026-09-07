import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H5_FriedmanMelloA1Adapter
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H17_U06ScientificInputs_Proof

/-!
# CONDITIONAL H17/H18 after discharging exact H5 from approved A1

U01's checked Friedman--Mello adapter supplies the entire
`H16ExactH5Family`.  U06's determinant-local
`H16CenteredWeakFactsScientificInputsFamily` remains the sole explicit
scientific parameter.  Thus the two exact-quantifier projective endpoints
below are reduced conditional theorems, not unconditional H17/H18 proofs.
-/

open TopologicalSpace MeasureTheory Set Filter
open scoped Topology

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- Approved Friedman--Mello A1, after U01's separately proved project
mapping, supplies U06's exact universally closed H5 family. -/
theorem h16ExactH5Family_from_friedmanMello1985_A1 :
    H16ExactH5Family := by
  intro n k hn h2nk
  exact
    friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_of_A1
      hn h2nk

/-- `CONDITIONAL` / `REDUCED`: literal H18 after exact H5 has been
discharged by approved A1.  The determinant-local U06 scientific-input
family is the only remaining premise. -/
theorem coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_from_U01_A1_U06_scientificInputs
    (H : H16CenteredWeakFactsScientificInputsFamily)
    {N K r : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (hr : r ≤ 4) (event : Set (ConcreteMatrixState N))
    (hevent : MeasurableSet event) (y : ℝ) :
    iteratedDeriv r
        (concreteProjectiveAveragedCenteredCOEEventPath N K event) y =
      ∫ v : ComplexUnitSphere N,
        iteratedDeriv r
          (concreteCenteredRankOneCOEEventPath K v event) y
          ∂(complexUnitSphereProbabilityMeasure N) := by
  exact
    coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_from_U06_scientificInputs_exactH5
      h16ExactH5Family_from_friedmanMello1985_A1 H
      hN hboundary hr event hevent y

/-- `CONDITIONAL` / `REDUCED`: literal H17 after exact H5 has been
discharged by approved A1.  The determinant-local U06 scientific-input
family is the only remaining premise. -/
theorem coeCorner_centeredProjective_eventPath_contDiff_four_H17_from_U01_A1_U06_scientificInputs
    (H : H16CenteredWeakFactsScientificInputsFamily)
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (event : Set (ConcreteMatrixState N)) (hevent : MeasurableSet event) :
    ContDiff ℝ 4
      (concreteProjectiveAveragedCenteredCOEEventPath N K event) := by
  exact
    coeCorner_centeredProjective_eventPath_contDiff_four_H17_from_U06_scientificInputs_exactH5
      h16ExactH5Family_from_friedmanMello1985_A1 H
      hN hboundary event hevent

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
