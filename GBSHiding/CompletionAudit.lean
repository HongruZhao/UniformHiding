import GBSHiding.Completion
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Version 1.4.0: check exact foundations-only transitive dependency sets,
including the two retained signed-measure endpoints. -/
def verifyHidingCompletionAxioms : CommandElabM Unit := do
  let foundations : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``GBSHiding.orderedDisjointPatternProductHidingAllInputs,
    ``GBSHiding.orderedDisjointMaxScoreCdfTransferAllInputs,
    ``GBSHiding.orderedDisjointHeavyCountBinomialTransferAllInputs,
    ``GBSHiding.corollary3_3_route1_optimized,
    ``GBSHiding.corollary3_3_route1_public,
    ``GBSHiding.averageTV_uniformLabel_mean,
    ``GBSHiding.averageTV_uniformLabel_markov,
    ``GBSHiding.collisionFreeSamplerRelative_averageTV,
    ``GBSHiding.collisionFreeSamplerRelativeOptimized_averageTV,
    ``GBSHiding.pairMass_hasSum_one,
    ``GBSHiding.photonPairPMF_add,
    ``GBSHiding.squeezedInputPairCount_eq,
    ``GBSHiding.squeezedInputPairCount_sector_mass,
    ``GBSHiding.singleMode_pair_mass,
    ``GBSHiding.squeezedInputPairCount_generatingFunction,
    ``GBSHiding.squeezedInputPhotonCount_even,
    ``GBSHiding.squeezedInputPhotonCount_odd,
    ``GBSHiding.photonTensorMatrix_unitary,
    ``GBSHiding.passiveOptics_preserves_bosonicSymmetry,
    ``GBSHiding.passiveOptics_preserves_photonNumberLaw,
    ``GBSHiding.proposition4_1_output_sector_probability,
    ``GBSHiding.proposition4_1_reference_scale,
    ``GBSHiding.proposition4_1_maximizer,
    ``GBSHiding.pairMass_eq_optimal_iff,
    ``GBSHiding.squeezing_mean_match_iff,
    ``GBSHiding.meanMatchedSqueezing,
    ``GBSHiding.logGammaStirlingError_halfNat_bound,
    ``GBSHiding.proposition4_1_uniform_log_error,
    ``GBSHiding.proposition4_1_uniform_relative_error,
    ``GBSHiding.proposition4_1_stirling_isBigO,
    ``GBSHiding.finitePopulationFactor_bounds,
    ``GBSHiding.finitePopulationFactor_tendsto_one,
    ``GBSHiding.proposition4_1_reference_scale_isTheta,
    ``LogdetLean.GramHafnian.ThreePaper.Verification.signedKernelContinuousLinearMap_norm_le_one,
    ``LogdetLean.GramHafnian.ThreePaper.Verification.ConcreteCongruenceKernelAdapter.congruenceKernel_eq_hide_commute_derivative] do
    let expected := foundations
    let actual ← Lean.collectAxioms decl
    let unexpected := actual.filter fun ax => !expected.contains ax
    let missing := expected.filter fun ax => !actual.contains ax
    unless unexpected.isEmpty && missing.isEmpty do
      throwError "{decl}: unexpected axioms {unexpected}; missing expected axioms {missing}"
    logInfo m!"PASS {decl}: exactly {actual.size} axioms: {actual}"

run_cmd verifyHidingCompletionAxioms

#check GBSHiding.orderedDisjointMaxScoreCdfTransferAllInputs
#check GBSHiding.orderedDisjointHeavyCountBinomialTransferAllInputs
#check GBSHiding.corollary3_3_route1_public
#check GBSHiding.collisionFreeSamplerRelative_averageTV
#check GBSHiding.collisionFreeSamplerRelativeOptimized_averageTV
#check GBSHiding.proposition4_1_output_sector_probability
#check GBSHiding.proposition4_1_reference_scale
#check GBSHiding.proposition4_1_maximizer
#check GBSHiding.proposition4_1_uniform_relative_error
#check GBSHiding.proposition4_1_stirling_isBigO
#check GBSHiding.proposition4_1_reference_scale_isTheta
#check LogdetLean.GramHafnian.ThreePaper.Verification.ConcreteCongruenceKernelAdapter.congruenceKernel_eq_hide_commute_derivative
