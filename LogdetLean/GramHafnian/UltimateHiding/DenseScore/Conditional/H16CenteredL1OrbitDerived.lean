import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredL1Orbit
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredMatrixExponentialContinuity

/-!
# Strong continuity of every centered literal-jet orbit in `L1`

This removes the auxiliary matrix-exponential continuity parameter from the
fixed-direction theorem by using the exact centered closed form.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

theorem continuous_h16CenteredJetLpOfWeak_fixedDirection
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary)
    (r : Fin 5) (v : ComplexUnitSphere N) :
    Continuous (fun t : ℝ ↦ h16CenteredJetLpOfWeak W r v t) :=
  continuous_h16CenteredJetLpOfWeak_fixedDirection_of_matrixExp
    W r v (h16MatrixExponentialCurveContinuous_centered hN v)

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
