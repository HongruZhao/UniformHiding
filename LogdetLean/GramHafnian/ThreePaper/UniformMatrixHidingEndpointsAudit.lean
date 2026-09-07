import LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding
import LogdetLean.GramHafnian.ThreePaper.Verification.HidingOutsideCDPaperFacing
import LogdetLean.GramHafnian.ThreePaper.Verification.HidingLemmaIII2SignedMeasure
import LogdetLean.GramHafnian.ThreePaper.Verification.HidingLemmaIII2ConcreteSignedAction
import LogdetLean.GramHafnian.ThreePaper.Verification.HidingLemmaIII3PaperFacing
import LogdetLean.GramHafnian.ThreePaper.Verification.HidingAppendixCPaperFacing
import LogdetLean.GramHafnian.ThreePaper.Verification.HidingExternalInputsPaperFacing
import LogdetLean.GramHafnian.ThreePaper.Verification.HidingTraceVarianceCentered
import LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08.H8H10_ExactTraceRecurrenceAdapter

/-!
# Exact executable label audit for the matrix-law uniform-hiding paper

Every active mathematical label in the manuscript is paired below with the
declaration whose type is the displayed statement. A multi-line definition
may require several checks, one for each displayed clause. No check is used
merely because it resembles the paper statement: normalizations, ambient
matrix types, hypotheses, quantifiers, constants, and the eventwise total
variation convention agree literally. For Lemma III.2 the generic signed
Markov kernel action, its sharp contraction, its positive measure
compatibility, and the concrete transpose congruence instantiation are all
constructed below the kernel. The derivative check therefore has no
unsupplied contractivity field or concrete adapter hypothesis.

Section, appendix, figure, table, and historical-discussion navigation labels
do not assert mathematical propositions and are intentionally not represented
by `#check` commands.
-/

open MeasureTheory ProbabilityTheory

namespace LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding.PaperEndpointsAudit

open LogdetLean.GramHafnian
open LogdetLean.GramHafnian.LocalAnticoncentration
open LogdetLean.GramHafnian.MatrixLawEndpoints
open LogdetLean.GramHafnian.UltimateHiding
open LogdetLean.GramHafnian.UltimateHiding.Dense
open LogdetLean.GramHafnian.UltimateHiding.DenseScore
open LogdetLean.GramHafnian.UltimateHiding.DenseScore.U08
open LogdetLean.GramHafnian.UltimateHiding.DenseLocalStep
open LogdetLean.GramHafnian.UltimateHiding.Sparse
open LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding
open LogdetLean.GramHafnian.ThreePaper.Verification

/-! ## Headline theorem and transpose-Gram structure -/

#check hidingRemainder
  -- eq:hiding-remainder
#check normalizedMatrixLaw
  -- thm:uniform-product-hiding; eq:uniform-product-hiding
#check eq_uniform_product_hiding_unscaled
  -- eq:uniform-product-hiding-unscaled
#check certifiedHidingError_of_ambient
  -- eq:certified-ambient-size

#check rectangularTransposeGram
#check normalizeTransposeGram
#check normalizedTransposeGramMatrix
#check complexGLTransposeCongruence
  -- the three clauses of eq:hide-projection
#check eq_hide_covariance
  -- prop:transpose-gram-covariance; eq:hide-covariance

/-! ## Haar recursion, radial transport, and evaluated dense step -/

#check concreteHaarAmbientLaw
#check concreteHaarAmbientLaw_eq_map_normalizedBlock
  -- eq:hide-mu-definition
#check normalizedGaussianTransposeGramLaw
  -- eq:hide-nu-definition
#check concreteHaarOneColumnRecursion_eq_map_product_A1A2A3A4
#check concreteOneColumnParameterLaw_eq_beta_prod_sphere
#check oneColumnParameterDictionary
  -- lem:hide-recursion; eq:hide-recursion-measure
#check concreteHaarOneColumnRecursion_event_A1A2A3A4
  -- eq:hide-recursion
#check oneColumnParameterDictionary
#check concreteOneColumnParameterLaw_eq_beta_prod_sphere
  -- eq:hide-ab, including the independent beta/sphere product law
#check normalizedHaarTransposeGram_targetConvergence_A1A2A3A4
  -- eq:hide-target-convergence

#check eq_hide_congruence_action
  -- eq:hide-congruence-action
#check concreteCenteredOrbitalDirection
#check concreteOrbitalMatrixKernel
  -- eq:hide-orbital-kernel
#check IsUnitaryConjugationInvariant.preservesUnitaryCongruenceInvariant
#check congruenceMeasureActions_commute_of_unitary_invariant
#check glComplex_unitary_oneColumn_orbital_commutation_from_gelfand
  -- lem:hide-commute; eq:hide-commute
#check VariationMarkovOperator.eq_hide_commute_contraction
  -- abstract functional analytic core
#check VariationMarkovOperator.eq_hide_commute_derivative
  -- abstract functional analytic core
#check signedKernelAction_contractive
#check signedKernelContinuousLinearMap_norm_le_one
#check ConcreteCongruenceKernelAdapter.congruenceUpdateKernel_comp_eq_congruenceMeasureAction
#check ConcreteCongruenceKernelAdapter.congruenceSignedKernelAction_toSignedMeasure
#check ConcreteCongruenceKernelAdapter.congruenceKernelVariationMarkovOperator_contractive
  -- eq:hide-commute-contraction, concrete T_lambda
#check ConcreteCongruenceKernelAdapter.congruenceKernel_eq_hide_commute_derivative
  -- eq:hide-commute-derivative, concrete T_lambda and K_s
#check concreteHaarAmbientLaw_radialFactorization_fromCOE
  -- eq:hide-radial
#check concreteScaledCOECornerLaw
  -- eq:hide-base
#check eq_hide_radial_one_column_commute
  -- eq:hide-radial-one-column-commute
#check eq_hide_radial_TV
  -- eq:hide-radial-TV; an independent eventwise probability-TV endpoint,
  -- not a formal corollary of the signed variation module.

#check concreteCentralEventPath
#check concreteProjectiveAveragedCenteredCOEEventPath
  -- eq:hide-event-paths
#check hidingLemmaIII3_eventwise_A1A2A3A4
  -- lem:hide-scores
#check HidingLemmaIII3EventwiseScores.centralSmooth
#check HidingLemmaIII3EventwiseScores.scalarFirst
#check HidingLemmaIII3EventwiseScores.scalarSecond
  -- eq:hide-scale-score
#check HidingLemmaIII3EventwiseScores.orbitalSmooth
#check HidingLemmaIII3EventwiseScores.orbitalFirst
#check HidingLemmaIII3EventwiseScores.orbitalSecond
#check HidingLemmaIII3EventwiseScores.orbitalThird
  -- eq:hide-orbital-score
#check oneColumn_logarithm_split
  -- eq:hide-split
#check normalizedHaarTransposeGram_oneColumnTVLE_615172_A1A2A3A4
  -- prop:hide-one-step; eq:hide-one-step
#check normalizedDenseProductHidingTVLE_615172_A1A2A3A4
  -- eq:dense-product-hiding

/-! ## Rectangular branch and the sparse/dense stitch -/

#check toReal_klDiv_sqrtScaledHaarBlock_le_three_quarters_A1A2A3A4
#check sqrtScaledHaarBlock_probabilityTotalVariationLE_A1A2A3A4
  -- lem:hide-sparse; eq:hide-sparse-hyp
#check toReal_klDiv_sqrtScaledHaarBlock_le_three_quarters_A1A2A3A4
  -- eq:hide-sparse-KL
#check sqrtScaledHaarBlock_probabilityTotalVariationLE_A1A2A3A4
  -- eq:hide-finite-sparse
#check normalizedSparseStitchTVLE_68_A1A2A3A4
  -- eq:hide-sparse-stitch
#check normalizedTransposeGram_probabilityTotalVariationLE_sparse_A1A2A3A4
  -- eq:hide-target-rate
#check eq_rectangular_rn_density_ae
  -- eq:rectangular-rn-density

/-! ## Appendix C: exact COE density and boundary differentiation -/

#check friedmanMello1985_unscaledCOECornerLaw_eq_determinantDensity_of_A1
  -- eq:hide-coe-density
#check concreteScaledCOECornerLaw
#check unscaleCOECorner
#check concreteUnscaledCOECornerLaw
  -- eq:hide-coe-scaling
#check concreteCOEExponent
#check concreteCOEZ
#check concreteCOEY
  -- eq:hide-YZ
#check concreteCOEWMatrix_eq_one_add_Z
#check concreteCOERMatrix_eq_sqrt_exponent_smul_one_add_Z_mul_unscale
#check concreteCOERMatrix_mul_conjTranspose_eq_Y_mul_one_add_Z
  -- eq:hide-omega-R
#check coeTakagiMuirhead_traceVector_betaPrime_A1A2PrimeA3
  -- eq:hide-beta-prime
#check integral_h9ScaledInverseTrace
  -- eq:hide-inverse-wishart-mean
#check coe_boundary_exponent_ge_seven_halves
#check coe_boundary_exponent_sub_fin4_pos
#check coe_boundary_exponent_sub_four_gt_neg_one
  -- eq:hide-boundary-exponents
#check integrable_coe_boundary_rpow_sub_four
  -- eq:hide-boundary-integrability
#check h16CenteredCoordinateComplexJacobianFamily
  -- eq:hide-centered-jacobian
#check concreteProjectiveAveragedCenteredCOEEventPath
#check concreteProjectiveAveragedCenteredCOEEventPath_eq_orbitalAction
  -- eq:hide-centered-event-path
#check coeCorner_centeredProjective_eventPath_contDiff_four_H17_proved_from_A1
  -- lem:coe-boundary-regularity
#check eq_hide_fourth_secant_from_A1
  -- eq:hide-fourth-secant
#check transposeCongruenceFlow_baseTime_shift
  -- eq:hide-centered-flow-group
#check coeCorner_centeredProjective_eventPath_derivative_interchange_at_H18_proved_from_A1
  -- eq:hide-centered-derivative-interchange

/-! ## Appendix D: projective scores and finite constant ledger -/

#check h8H10ExactTraceRecurrenceSystem_internal
  -- eq:hide-inverse-wishart-recurrence-system
#check eq_hide_inverse_gradient
  -- eq:hide-inverse-gradient
#check integral_complexCenteredProjectiveTracePair_mul
  -- eq:hide-projective-contraction
#check densityBellFour
  -- eq:hide-fourth-bell-polynomial
#check h11COEBlockUnwrapper
#check h11COEBlockMiddle
#check h11COEBlockUnwrapper_mul_centeredFlow_mul_unwrapper
#check map_star_eq_transpose_of_isHermitian_h11
  -- eq:hide-centered-block-factorization
#check h11COEBlockGapDiagonal
#check h11COEBlock_product_identity_posDef
#check h11COEBlockCayley_posDef_of_support
  -- eq:hide-coe-block-product
#check h11_iteratedDeriv_four_log_det_re_exp_affine
#check h11BlockFourthJacobiMatrix
#check trace_h11BlockFourthJacobiMatrix_half_one_add
  -- eq:hide-fourth-jacobi-reduction
#check trace_involution_fourth_gap_eq_sum_squares
  -- eq:hide-fourth-involution-sos
#check four_trace_X_cube_JXJ_le_trace_XJ_four_add_three_trace_X_four
  -- eq:hide-fourth-involution-young
#check four_trace_E_cube_Rsq_E_Rsq_le_of_grading_square_root
  -- eq:hide-fourth-cayley-bridge
#check trace_h11COEBlockFourthJacobiMatrix_re_nonpos
  -- eq:hide-fourth-jacobi-sign
#check concreteCenteredLogDeterminantJet_four_nonpos
  -- eq:hide-fourth-logdet-jet-sign
#check fourthBellLower_posPart_le_sos
  -- eq:hide-fourth-sos
#check eq_hide_fourth_ell_one_fourth_moment_A1A2A3A4
  -- eq:hide-fourth-ell-one-fourth-moment
#check eq_hide_fourth_ell_two_square_moment_A1A2A3
  -- eq:hide-fourth-ell-two-square-moment
#check eq_hide_fourth_ell_one_three_moment_A1A2A3A4
  -- eq:hide-fourth-ell-one-three-moment
#check combinedSharperLowerBellPositiveConstant_eq
  -- eq:hide-fourth-positive-constant
#check two_mul_combinedSharperLowerBellPositiveConstant_le_full
  -- eq:hide-fourth-ceiling
#check combinedSharperFullFourthDensityScoreConstant_eq
  -- eq:hide-fourth-constant
#check concreteCenteredLikelihoodCore
#check concreteCenteredLogScore
#check concreteCenteredDensityScore
#check concreteCenteredLikelihoodCore_zero_on_support
#check coeCorner_centeredDensityScore_four_eq_Bell_external_derived
  -- eq:hide-fourth-density-score-definition
#check concreteCenteredDensityScoreFourProduct_lpNorm_one_le_combinedSharper
  -- eq:hide-fourth-density-L1

#check concreteCenteredQuadraticDensity
#check centeredQuadraticTraceBracket
#check averagedCenteredQuadratic_exact_contraction
  -- eq:hide-quadratic-density
#check exactVarianceOrbitalScoreTwoConstant
  -- eq:hide-quadratic-constant
#check concreteCenteredQuadraticDensity_lpNorm_one_le_exactVariance
  -- eq:hide-quadratic-L1

#check concreteAveragedCenteredCubicDensity_extract_traceThree
  -- eq:hide-cubic-trace-decomposition
#check concreteAveragedCenteredCubicTraceThreeRemainder_lpNorm_one_le_ultraNGeTwo
  -- eq:hide-cubic-residual-L1
#check ultraNGeTwoRawTraceThreeRemainderConstant
  -- eq:hide-cubic-residual-definition
#check ultraNGeTwoRawTraceThreeRemainderConstant_eq
  -- eq:hide-cubic-residual-value
#check two_mul_ultraNGeTwoRawTraceThreeRemainderConstant_le
  -- eq:hide-cubic-ceiling
#check ultraNGeTwoAveragedCenteredCubicNormalizationConstant_eq
  -- eq:hide-cubic-constant
#check integral_concreteAveragedCenteredCubicDensity_eq_zero_internal
  -- eq:hide-cubic-zero-mass
#check concreteAveragedCenteredCubicDensity_lpNorm_one_le_ultraNGeTwo
  -- eq:hide-cubic-L1
#check hiding_S_moments_literal_commonConstant
  -- eq:hide-S-moments

#check abs_iteratedDeriv_one_concreteBaseCentralEventPath_le_exactVariance
  -- eq:hide-central-first-event
#check abs_iteratedDeriv_two_concreteBaseCentralEventPath_le_exactVariance
  -- eq:hide-central-second-event
#check iteratedDeriv_one_concreteSharedBetaOrbitalEventPath_eq_zero
  -- eq:hide-orbital-first-event
#check abs_iteratedDeriv_two_concreteSharedBetaOrbitalEventPath_le_exactVariance
  -- eq:hide-orbital-second-event
#check abs_iteratedDeriv_four_concreteSharedBetaOrbitalEventPath_le_combinedSharper
  -- eq:coe-fourth-event-bound
#check abs_iteratedDeriv_three_concreteSharedBetaOrbitalEventPath_le_combinedSharper
  -- eq:hide-propagated-third-certificate

#check abs_iteratedDeriv_one_concreteBaseCentralEventPath_le_exactVariance
#check abs_iteratedDeriv_two_concreteBaseCentralEventPath_le_exactVariance
  -- eq:hide-lemma-three-scalar-closure
#check concrete_projectiveAveraged_centered_first_derivative_eq_zero
#check concrete_projectiveAveraged_centered_second_derivative_eq_density_indicator_integral_H14Rewire
#check concreteCenteredQuadraticDensity_lpNorm_one_le_exactVariance
  -- eq:hide-lemma-three-orbital-low-closure
#check hidingLemmaIII3_orbitalThird_zero
#check concreteAveragedCenteredCubicDensity_lpNorm_one_le_ultraNGeTwo
#check ultraNGeTwoAveragedCenteredCubicNormalizationConstant_eq
  -- eq:hide-lemma-three-cubic-origin
#check abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_combinedSharper
#check combinedSharperFullFourthDensityScoreConstant_eq
  -- eq:hide-lemma-three-fourth-uniform
#check abs_iteratedDeriv_three_le_at_of_fourth
#check abs_iteratedDeriv_three_le_at_inverse_dimension_of_fourth
#check hidingLemmaIII3_orbitalThird
  -- eq:hide-lemma-three-cubic-propagation

#check integral_oneColumnRankOneLog_eq_internal
  -- eq:hide-beta-log-mean
#check integral_sq_oneColumnRankOneLog_eq_internal
  -- eq:hide-beta-log-second-moment
#check integral_abs_cube_oneColumnRankOneLog_eq_internal
  -- eq:hide-beta-log-third-moment
#check abs_integral_oneColumnCenteredScalarLog_le_concrete
  -- eq:hide-c-mean
#check integral_oneColumnCenteredScalarLog_sq_le_concrete
  -- eq:hide-c-moments
#check integral_oneColumnRankOneLog_sq_le_concrete
  -- eq:hide-b-second-moment
#check integral_abs_oneColumnRankOneLog_cube_le_concrete
  -- eq:hide-b-moment
#check oneColumnScalarTaylorBudget_le_concrete
#check oneColumnOrbitalTaylorBudget_le_concrete
#check oneColumnLogBadProbability_le_six
  -- eq:hide-tail
#check oneColumnLogBadProbability_le_telescopingRate_concrete
  -- eq:hide-tail-telescoping
#check concreteCentralMixture_endpoint
#check concreteSharedBetaOrbitalEventPath_zero_sameBeta
#check concreteSharedBetaGood_endpoint
#check probabilityTVLE_of_random_scalar_eventPath
#check probabilityTVLE_of_correlated_centered_eventPath
  -- eq:hide-one-step-eventwise-taylor
#check probabilityTVLE_concreteSharedBetaGood_full
#check probabilityTVLE_triangle
#check HidingOneColumnComponentTVBounds.scalar
#check HidingOneColumnComponentTVBounds.orbital
#check HidingOneColumnComponentTVBounds.bad
#check eq_hide_one_step_taylor_decomposition_A1A2A3A4
#check normalizedHaarTransposeGram_oneColumnTVLE_615138_A1A2A3A4
  -- eq:hide-one-step-taylor-decomposition
#check concreteCanonicalHidingSquaredConstant_eq
#check probabilityTVLE_of_random_scalar_eventPath
#check oneColumnScalarTaylorBudget_le_concrete
#check HidingOneColumnComponentTVBounds.scalar
  -- eq:hide-proposition-four-scalar-use
#check probabilityTVLE_of_correlated_centered_eventPath
#check oneColumnOrbitalTaylorBudget_le_concrete
#check HidingOneColumnComponentTVBounds.orbital
  -- eq:hide-proposition-four-orbital-use
#check hidingOneColumnComponentTVBounds_A1A2A3A4
#check hidingOneColumnTVLE_615138_A1A2A3A4
#check eq_hide_radial_TV
#check normalizedHaarTransposeGram_oneColumnTVLE_615172_A1A2A3A4
  -- eq:hide-proposition-four-closure

/-! ## Hiding-only applications -/

#check observableLaw
#check observableEventTransfer
#check reverseObservableEventTransfer
  -- cor:observable-hiding; eq:observable-hiding
#check observableEventTransfer
#check reverseObservableEventTransfer
  -- eq:event-transfer
#check boundedStatisticExpectationTransfer
#check markovKernelPostprocessingLaw
  -- eq:randomized-postprocessing
#check hafnianObservableLaw
  -- eq:hafnian-amplitude-hiding
#check orderedFixedPatternPanelLaw_A1A2A3A4
  -- eq:joint-pattern-hiding
#check orderedDisjointMaxScoreCdfTransfer
#check orderedDisjointHeavyCountBinomialTransfer
  -- prop:score-panel-transfer
#check orderedDisjointMaxScoreCdfTransfer
  -- eq:max-score-transfer
#check orderedDisjointHeavyCountBinomialTransfer
  -- eq:heavy-count-transfer

/-! ## The four declared external inputs and exact dictionaries -/

#check eq_external_A1
  -- eq:external-A1 (A1)
#check eq_external_A1_dictionary
  -- eq:external-A1-dictionary
#check eq_external_A2prime
  -- eq:external-A2prime (A2-prime)
#check eq_external_A3_jacobi
  -- eq:external-A3-jacobi
#check eq_external_A3_symmetric_test
  -- eq:external-A3-symmetric-test (A3)
#check eq_external_A3_dictionary
  -- eq:external-A3-dictionary
#check eq_external_A4_gap
  -- eq:external-A4-gap
#check eq_external_A4_Tg
  -- eq:external-A4-Tg
#check eq_external_A4_direct
  -- eq:external-A4-direct (A4)
#check eq_external_A4_inverse
  -- eq:external-A4-inverse (A4)
#check eq_external_A4_dictionary
  -- eq:external-A4-dictionary

/-! ## Fresh representative axiom closures -/

#print axioms normalizedMatrixLaw
#print axioms normalizedHaarTransposeGram_oneColumnTVLE_615172_A1A2A3A4
#print axioms normalizedDenseProductHidingTVLE_615172_A1A2A3A4
#print axioms congruenceMeasureActions_commute_of_unitary_invariant
#print axioms VariationMarkovOperator.eq_hide_commute_contraction
#print axioms VariationMarkovOperator.eq_hide_commute_derivative
#print axioms signedKernelActionRaw_apply
#print axioms signedKernelActionRaw_toSignedMeasure
#print axioms signedKernelAction_contractive
#print axioms signedKernelContinuousLinearMap_norm_le_one
#print axioms ConcreteCongruenceKernelAdapter.congruenceUpdateKernel_comp_eq_congruenceMeasureAction
#print axioms ConcreteCongruenceKernelAdapter.congruenceSignedKernelAction_toSignedMeasure
#print axioms ConcreteCongruenceKernelAdapter.congruenceKernelVariationMarkovOperator_contractive
#print axioms ConcreteCongruenceKernelAdapter.congruenceKernel_eq_hide_commute_derivative
#print axioms hidingLemmaIII3_eventwise_A1A2A3A4
#print axioms hidingLemmaIII3_orbitalThird_zero
#print axioms abs_iteratedDeriv_four_concreteProjectiveAveragedCenteredCOE_le_combinedSharper
#print axioms abs_iteratedDeriv_three_le_at_of_fourth
#print axioms hidingLemmaIII3_orbitalThird
#print axioms hidingOneColumnComponentTVBounds_A1A2A3A4
#print axioms hidingOneColumnTVLE_615138_A1A2A3A4
#print axioms concreteCentralMixture_endpoint
#print axioms concreteSharedBetaOrbitalEventPath_zero_sameBeta
#print axioms concreteSharedBetaGood_endpoint
#print axioms probabilityTVLE_of_random_scalar_eventPath
#print axioms probabilityTVLE_of_correlated_centered_eventPath
#print axioms probabilityTVLE_concreteSharedBetaGood_full
#print axioms probabilityTVLE_triangle
#print axioms eq_hide_one_step_taylor_decomposition_A1A2A3A4
#print axioms normalizedHaarTransposeGram_oneColumnTVLE_615138_A1A2A3A4
#print axioms coeCorner_centeredProjective_eventPath_contDiff_four_H17_proved_from_A1
#print axioms eq_hide_fourth_secant_from_A1
#print axioms transposeCongruenceFlow_baseTime_shift
#print axioms h11COEBlockUnwrapper_mul_centeredFlow_mul_unwrapper
#print axioms map_star_eq_transpose_of_isHermitian_h11
#print axioms h11COEBlock_product_identity_posDef
#print axioms h11COEBlockCayley_posDef_of_support
#print axioms h8H10ExactTraceRecurrenceSystem_internal
#print axioms trace_h11COEBlockFourthJacobiMatrix_re_nonpos
#print axioms eq_hide_fourth_ell_one_fourth_moment_A1A2A3A4
#print axioms eq_hide_fourth_ell_two_square_moment_A1A2A3
#print axioms eq_hide_fourth_ell_one_three_moment_A1A2A3A4
#print axioms concreteCenteredLikelihoodCore_zero_on_support
#print axioms coeCorner_centeredDensityScore_four_eq_Bell_external_derived
#print axioms concreteCenteredDensityScoreFourProduct_lpNorm_one_le_combinedSharper
#print axioms concreteAveragedCenteredCubicDensity_lpNorm_one_le_ultraNGeTwo
#print axioms hiding_S_moments_literal_commonConstant
#print axioms orderedFixedPatternPanelLaw_A1A2A3A4
#print axioms eq_external_A1
#print axioms eq_external_A2prime
#print axioms eq_external_A3_symmetric_test
#print axioms eq_external_A4_direct

end LogdetLean.GramHafnian.ThreePaper.UniformMatrixHiding.PaperEndpointsAudit
