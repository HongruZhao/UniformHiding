import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16BoundaryTraceVanishing
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredJetBasic
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.Conditional.H16CenteredTransportL1Interface

/-!
# H16 determinant-specific analytic core

This file names the two direct-IBP conclusions that remain after the proved
scalar exponent calculus.  They are strictly below the final zero-extension
structure: they contain no `L1` curve, derivative chain, `ContDiff`, iterated
derivative, compact-time envelope, projective integration, event, or H5.
-/

open MeasureTheory

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

/-- The independent finite-dimensional Jacobian identity, separated from
the determinant-boundary analysis. -/
abbrev H16CenteredCoordinateComplexJacobianFamily (N : ℕ) : Prop :=
  ∀ (v : ComplexUnitSphere N) (t : ℝ),
    H16CenteredCoordinateComplexJacobianOne v t

/-- Exact fourth base-jet integrability.  This permits the sharp
`q^(-1/2)` singularity and asserts no boundary value or continuity. -/
abbrev H16CenteredBaseJetFourIntegrable (N K : ℕ) : Prop :=
  ∀ v : ComplexUnitSphere N,
    Integrable (h16CenteredTransportJet N K 4 v 0)
      (complexSymmetricCoordinateVolume N)

/-- The four global zero-extension weak-generator identities obtained after
the epsilon-boundary traces of orders zero through three vanish. -/
abbrev H16CenteredWeakGeneratorChain (N K : ℕ) : Prop :=
  ∀ (r : Fin 4) (v : ComplexUnitSphere N),
    COEWeakGeneratorIdentity
      (h16CenteredTransportJet N K r.castSucc v 0)
      (h16CenteredTransportJet N K r.succ v 0)
      (h16CenteredCoordinateVectorField v)

/-- Small determinant-boundary core remaining from direct Gauss--Green on
the spectral exhaustion.  This is not endpoint-equivalent. -/
structure H16CenteredDirectIBPAnalyticCore
    (N K : ℕ) (_hN : 1 ≤ N) (_hboundary : 2 * N + 8 ≤ K) : Prop where
  baseJetFour_integrable : H16CenteredBaseJetFourIntegrable N K
  weakGenerator_chain : H16CenteredWeakGeneratorChain N K

/-- Any completed weak-generator facts contain the smaller direct-IBP core.
This projection records that the blocker excludes every later Bochner and
projective conclusion. -/
theorem H16CenteredDirectIBPAnalyticCore.ofWeakFacts
    {N K : ℕ} {hN : 1 ≤ N} {hboundary : 2 * N + 8 ≤ K}
    (W : COECenteredOrderFourWeakGeneratorFacts N K hN hboundary) :
    H16CenteredDirectIBPAnalyticCore N K hN hboundary where
  baseJetFour_integrable := fun v ↦ W.jet_integrable 4 v 0
  weakGenerator_chain := W.weak_generator_chain

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
