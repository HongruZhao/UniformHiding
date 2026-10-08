import LogdetLean.GramHafnian.UltimateHiding.DenseScore.H6_CanonicalGapWeylReduction
import A2.WeylIntegrationProof

noncomputable section
namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- Exact original data-valued A2 declaration, now constructed unconditionally. -/
def A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration
    (N : ℕ) (hN : 1 ≤ N) : TakagiWeylSymmetricIntegrationLaw N :=
  A2_takagi_weyl_integration N hN

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
