import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16MatrixExponentialContinuity
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.CenteredFlowGeometry
import Mathlib.Tactic

/-!
# Continuity of the centered matrix-exponential curve

The generic matrix-exponential topology bridge is unnecessary for the H16
centered direction.  The project already proves an exact closed formula for
`exp (t Q_v)` in terms of the rank-one orbital factor.  That formula is
entrywise continuous in `t`, which proves the required coordinate-topology
continuity without choosing a new matrix norm.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open NormedSpace
open LogdetLean.GramHafnian.UltimateHiding.Dense

theorem continuous_concreteOrbitalFactor_fixedDirection
    {N : ℕ} (v : ComplexUnitSphere N) :
    Continuous (fun t : ℝ ↦ concreteOrbitalFactor N t v) := by
  unfold concreteOrbitalFactor
  fun_prop

/-- The exact deterministic continuity premise consumed by the centered
`L1` pullback-orbit module. -/
theorem h16MatrixExponentialCurveContinuous_centered
    {N : ℕ} (hN : 1 ≤ N) (v : ComplexUnitSphere N) :
    H16MatrixExponentialCurveContinuous N
      (concreteCenteredOrbitalDirection N v) := by
  apply (continuous_concreteOrbitalFactor_fixedDirection v).congr
  intro t
  exact (matrix_exp_centeredOrbitalDirection_eq_concreteOrbitalFactor
    hN t v).symm

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
