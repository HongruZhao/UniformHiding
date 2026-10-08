import A2.WeylIntegrationTargetAssembly
import A2.TakagiChartDerivative
import A2.TakagiChartSmooth

noncomputable section

namespace LogdetLean.GramHafnian.UltimateHiding.DenseScore

/-- The exact raw Takagi--Weyl integration law, constructed from the proved
Euclidean orbit Jacobian, regular orbit fiber, and literal coordinate volume. -/
def takagiWeylSymmetricIntegrationLaw (N : ℕ) :
    TakagiWeylSymmetricIntegrationLaw N :=
  takagiWeylSymmetricIntegrationLaw_of_orbit_derivative N
    (@takagiCayleyOrbitChartDerivative N)
    (fun U x hpos ↦ contDiffAt_takagiCayleyOrbitChart U x hpos)
    (fun U x hpos ↦ hasFDerivAt_takagiCayleyOrbitChart U x hpos)
    (fun U x hpos ↦ abs_det_takagiCayleyOrbitChartDerivative U x hpos)

/-- The complete original A2 target, with the original dimension range and
arbitrary measurable permutation-invariant tests. -/
def A2_takagi_weyl_integration : Target :=
  fun N _hN ↦ takagiWeylSymmetricIntegrationLaw N

end LogdetLean.GramHafnian.UltimateHiding.DenseScore
