import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7MixedProjectiveDerived
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7RankOneDeterminant
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H7WitnessConditional

/-!
# Exact kernel proof of H7

The source module already owns the external declaration with the requested
basename, so Lean cannot redeclare that global constant.  This proof is placed
in the `H7Exact` namespace while preserving its basename, every binder, and
the literal conclusion type.  It does not invoke the external declaration.
-/

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

noncomputable section

open LogdetLean.GramHafnian.UltimateHiding.Dense

namespace H7Exact

/-- Exact H7 endpoint, with the original quantifiers and conclusion.  The
endpoint constructs data rather than a proposition, hence it is a definition
just like the checked conditional assembler it closes. -/
noncomputable def coeCorner_cubicDifferentialWitness_external_derived
    {N K : ℕ} (hN : 1 ≤ N) (hboundary : 2 * N + 8 ≤ K)
    (A : ConcreteMatrixState N)
    (hsymm : (unscaleCOECorner K A).IsSymm)
    (hsupport : coeCornerSupport (unscaleCOECorner K A)) :
    ConcreteCubicDifferentialWitness N K A :=
  h7Witness_of_three_residual_identities_CONDITIONAL
    hN hboundary A hsymm hsupport
    (fun v ↦
      h16CoordinateLikelihoodCore_rankOne_iteratedDeriv_three_derived
        v A hsymm hsupport)
    (h16CoordinateLikelihoodCore_central_iteratedDeriv_three_derived
      hboundary A hsupport)
    (h7ProjectiveMixedMean_derived
      hN hboundary A hsymm hsupport)

end H7Exact

end

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
