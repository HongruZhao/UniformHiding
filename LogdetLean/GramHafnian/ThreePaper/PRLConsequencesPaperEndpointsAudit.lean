import LogdetLean.GramHafnian.ThreePaper.PRLConsequences
import LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison

/-!
# Executable equation audit for the streamlined PRL interaction Letter

The checks below follow all 32 active labeled displays in exact manuscript
order.  The cited Route 2 matrix comparison is represented by an explicit
hypothesis-bearing interface, never by an axiom.  The final block prints
axioms for the retained kernel endpoints and abstract transfer engines.
-/

-- 1. `eq:gbs-probability`: adopted optical model, exact algebra.
#check LogdetLean.GramHafnian.CurrentPRL.eq1_gbs_collision_free_probability

-- 2. `eq:imported-hiding`: exact Route 1 matrix-law endpoint.
#check LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.matrixLaw

-- 3. `eq:gram-hafnian-variance`: exact observable and second moment product.
#check LogdetLean.GramHafnian.CurrentPRL.eq2_model
#check LogdetLean.GramHafnian.CurrentPRL.eq3_variance_is_actual_second_moment
#check LogdetLean.GramHafnian.CurrentPRL.eq3_variance_product
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.four_mul_pairCount_iff_two_mul_ambient

-- 4. `eq:imported-anticoncentration`: exact finite-K endpoint.
#check LogdetLean.GramHafnian.ThreePaper.PRXQAnticoncentration.shiftedSmallBall

-- 5. `eq:anticoncentration-coefficients`: exact finite and limiting formulas.
#check LogdetLean.GramHafnian.CurrentPRL.paperBkn_eq_product
#check LogdetLean.GramHafnian.CurrentPRL.paperBn_eq_gamma

-- 6. `eq:uniform-anticoncentration-coefficient`: exact full range bound.
#check LogdetLean.GramHafnian.CurrentPRL.paperBkn_le_uniform

-- 7. `eq:symmetric-hiding-rate`: the exact Shou et al. matrix comparison is
-- a named theorem premise; constructing it remains the cited external input.
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.ShouSymmetricMatrixComparisonAt
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.ShouSymmetricMatrixComparisonAt.matrixLaw
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.symmetricHidingEnvelope
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.symmetricHidingEnvelope_eq_const_mul_ultimateHidingRate
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.symmetricHidingEnvelope_nonneg

-- 8. `eq:symmetric-anticoncentration`: the exact independent symmetric
-- Gaussian theorem is axiom free in the companion archive, under declaration
-- `SymmetricGaussianHafnian.symmetricHafnian_shifted_smallBall`.  The local
-- variance and coefficient definitions are checked here.
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.symmetricHafnianVariance
#check LogdetLean.GramHafnian.CurrentPRL.paperBn
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.typeHafnian_congr_offDiagonal
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.hafnian_congr_offDiagonal
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.measure_preimage_fst_eq_of_map_eq

-- 9. `eq:finite-haar-composition`.
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.finiteHaarShiftedSmallBall

-- 10. `eq:symmetric-haar-composition`: exact conditional composition.
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.routeTwoFiniteHaarShiftedSmallBall_of_shou

-- 11. `eq:reference-probability`.
#check LogdetLean.GramHafnian.CurrentPRL.gbsGaussianReferenceProbability
#check LogdetLean.GramHafnian.CurrentPRL.scaledGBSOpticalFactor
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.exactSectorScaleIdentity
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.hafnian_const_mul
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.gbsProbability_div_reference_eq_scaledHafnian

-- 12. `eq:small-denominator`.
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.gbsSmallDenominator

-- 13. `eq:symmetric-reference-probability`.
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.symmetricGaussianReferenceProbability
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.symmetricHafnianVariance

-- 14. `eq:reference-scale-ratio`.
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.dimensionProduct_eq_pow_mul_varianceRatio
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.gramReferenceProbability_eq_ratio_mul_symmetricReference

-- 15. `eq:symmetric-small-denominator`: exact conditional physical tail.
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.routeTwoPhysicalSmallDenominator_of_shou

-- 16. `eq:relative-failure-inclusion`: exact event algebra.
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.relativeFailureEvent_subset_absolute_additive_union_denominator
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.relativeFailureEvent_subset_absolute_additive_union_dividedDenominator

-- Retained prose result: exact Haar row exchangeability for every selected
-- collision-free pattern, followed by the random-label transfer.
#check LogdetLean.GramHafnian.CurrentPRL.selectedRowsUnitaryBlock_map_eq_topLeftUnitaryBlock_map
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.map_collisionFreeHafnianAmplitude_eq_scaledHaar
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.collisionFreeDarkEvent_probability_le
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.collisionFreeRandomLabelAdditiveToRelative

-- 17. `eq:additive-relative`: common absolute threshold and both route rows.
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.relativeFailureEvent_subset_absolute_additive_union_denominator
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.absoluteAdditiveToRelativeProbability_le
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.relativeFailureProbability_le_routeOneFairBound
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.relativeFailureProbability_le_routeTwoFairExplicitBound
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.relativeFailureProbability_le_bestFairBound
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.routeTwoFairAbsoluteThresholdBound_explicit
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.symmetricThreshold_eq_ratio_mul_commonThreshold
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.physicalReferences_obey_fair_scale_identity
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.routeTwoFairRelativeFailure_of_shou

-- 18. `eq:polynomial-fair-budget`.
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.polynomialRelativeThreshold
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.routeOneFairBound_of_polynomialThreshold
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.routeTwoFairBound_of_polynomialThreshold_explicit
#check LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.bothFairBounds_of_polynomialThreshold

-- 19. `eq:coefficient-comparison`.
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.finiteCoefficient_div_limit_mul_ratio
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.one_lt_coefficientComparisonPenalty
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.limit_mul_ratio_lt_finiteCoefficient

-- 20. `eq:coefficient-envelope`.
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.coefficientTriple_isBigO_ambientLogScale

-- 21. `eq:pair-count-coefficient-envelope`.
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.pairCountLogScale_implies_ambientLogScale
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.four_mul_pairScale_exponents
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.coefficientTriple_isBigO_pairLogScale

-- 22. `eq:reference-scale-ratio-limit`.
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.gramToSymmetricVarianceRatio_tendsto_one_of_ambientSquaredRate

-- 23. `eq:decisive-window`: literal simultaneous sequence certificate.
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.decisiveWindow_lowerBound_implies_ambientLogScale
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.paperBkn_mul_polynomialThreshold_tendsto_zero_of_ambientLogScale
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.symmetricHidingEnvelope_tendsto_atTop_of_subquadratic
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.decisiveWindow_certificate

-- 24. `eq:collision-free-label-space`.
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.CollisionFreeLabel
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.collisionFreeLabelSpace_card

-- 25. `eq:uniform-label-mean-tv`, for arbitrary ambient output type.
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.finiteEventTotalVariationLE
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.probabilityTotalVariationLE_to_finiteEventTotalVariationLE
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.eventwiseFiniteTV_sum_abs_le_two
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.eventwiseFiniteTV_to_uniformLabelMean

-- 26. `eq:sampler-tv-interface`, for arbitrary ambient output type.
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.eventwiseFiniteTV_to_uniformLabelMarkov
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.eventwiseFiniteTV_to_badFraction

-- 27. `eq:sampler-relative-interface`.
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.samplerRelativeConstant
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.samplerTVToRandomLabelRelative_eventwise_prl
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.collisionFreeSamplerRelative_eventwise
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.samplerRouteConstant
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.samplerRouteBudget_explicit
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.routeTwoSamplerRelative_eventwise_of_shou

-- 28. `eq:proof-tv-transfers`: exact Route 2 transfer retaining its named
-- matrix comparison premise.
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.finitePanelEventTransfer
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.routeTwoShiftedDiskTransfer_of_shou

-- 29. `eq:proof-reference-scale-ratio`.
#check LogdetLean.GramHafnian.CurrentPRL.eq3_variance_product
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.symmetricHafnianVariance
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.gramVariance_div_pow_symmetricVariance_eq_ratio

-- 30. `eq:proof-coefficient-ratio`.
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.coefficientComparisonPenalty
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.finiteCoefficient_div_limit_mul_ratio

-- 31. `eq:proof-coefficient-log-bounds`.
#check LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.coefficientLogBounds

-- 32. `eq:proof-uniform-label-mean-tv`.
#check LogdetLean.GramHafnian.ThreePaper.PRLConsequences.eventwiseFiniteTV_to_uniformLabelMean

/-! ## Axiom audit for retained endpoints -/

#print axioms LogdetLean.GramHafnian.CurrentPRL.eq1_gbs_collision_free_probability
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.four_mul_pairCount_iff_two_mul_ambient
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQUniformHiding.matrixLaw
#print axioms LogdetLean.GramHafnian.ThreePaper.PRXQAnticoncentration.shiftedSmallBall
#print axioms LogdetLean.GramHafnian.CurrentPRL.paperBkn_le_uniform
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.finiteHaarShiftedSmallBall
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.gbsSmallDenominator
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.ShouSymmetricMatrixComparisonAt.matrixLaw
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.routeTwoHafnianLawTV_of_shou
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.routeTwoShiftedDiskTransfer_of_shou
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.routeTwoFiniteHaarShiftedSmallBall_of_shou
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.routeTwoPhysicalSmallDenominator_of_shou
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.routeTwoFairRelativeFailure_of_shou
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.routeTwoSamplerRelative_eventwise_of_shou
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.typeHafnian_congr_offDiagonal
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.hafnian_congr_offDiagonal
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.measure_preimage_fst_eq_of_map_eq
#print axioms LogdetLean.GramHafnian.CurrentPRL.selectedRowsUnitaryBlock_map_eq_topLeftUnitaryBlock_map
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.map_collisionFreeHafnianAmplitude_eq_scaledHaar
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.collisionFreeDarkEvent_probability_le
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.collisionFreeRandomLabelAdditiveToRelative
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.dimensionProduct_eq_pow_mul_varianceRatio
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.gramReferenceProbability_eq_ratio_mul_symmetricReference
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.methodTwoNaturalRelativeRemainder_explicit
#print axioms LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.relativeFailureEvent_subset_absolute_additive_union_denominator
#print axioms LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.relativeFailureEvent_subset_absolute_additive_union_dividedDenominator
#print axioms LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.absoluteAdditiveToRelativeProbability_le
#print axioms LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.relativeFailureProbability_le_routeOneFairBound
#print axioms LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.relativeFailureProbability_le_routeTwoFairExplicitBound
#print axioms LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.relativeFailureProbability_le_bestFairBound
#print axioms LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.routeOneFairBound_of_polynomialThreshold
#print axioms LogdetLean.GramHafnian.ThreePaper.FairAbsoluteThresholdComparison.routeTwoFairBound_of_polynomialThreshold_explicit
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.finiteCoefficient_div_limit_mul_ratio
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.coefficientLogBounds
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.one_lt_coefficientComparisonPenalty
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.limit_mul_ratio_lt_finiteCoefficient
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.coefficientTriple_isBigO_ambientLogScale
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.coefficientTriple_isBigO_pairLogScale
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.gramToSymmetricVarianceRatio_tendsto_one_of_ambientSquaredRate
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.decisiveWindow_certificate
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.collisionFreeLabelSpace_card
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.probabilityTotalVariationLE_to_finiteEventTotalVariationLE
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.eventwiseFiniteTV_sum_abs_le_two
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.eventwiseFiniteTV_to_uniformLabelMean
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.eventwiseFiniteTV_to_uniformLabelMarkov
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.samplerTVToRandomLabelRelative_eventwise_prl
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.collisionFreeSamplerRelative_eventwise
#print axioms LogdetLean.GramHafnian.ThreePaper.PRLConsequences.gbsProbability_div_reference_eq_scaledHafnian
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.gramVariance_div_pow_symmetricVariance_eq_ratio
#print axioms LogdetLean.GramHafnian.ThreePaper.TwoMethodComparison.samplerRouteBudget_explicit
