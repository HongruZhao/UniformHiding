# Manuscript-to-Lean correspondence

The theorem numbers refer to the revised manuscript, *Uniform Hiding and Two Routes to Relative Accuracy in Gaussian Boson Sampling*. `Theorem21` means Theorem **2.1**, not Theorem 21. The names beginning `theorem3_2_route1` mean the Route 1 part of Theorem **3.2**.

This correspondence uses the 48-page arXiv preparation from 9 September 2026. The [completion ledger](FORMALIZATION_COMPLETION.md) supersedes the earlier partial-coverage entries for Proposition 4.1, Corollaries 3.3 and 4.2, and Proposition G.2. It also corrects the earlier assessment of Lemma 6.2. Route 2 is excluded from the completion.

| Manuscript claim | Public declaration / source | Verification boundary |
| --- | --- | --- |
| Theorem 2.1, normalized matrix-law TV bound for all $`1\le N,K\le M`$ | `UniformHiding.theorem2_1` | Includes $`K<N`$; four literature axioms A1–A4 plus the three foundations |
| Theorem 2.1, equivalent unnormalized product bound | `UniformHiding.theorem2_1_unscaled` | Same full range and capped constant |
| Corollary 2.2, direct quantitative consequence | `UniformHiding.corollary2_2` | $`n\ge1`$, $`2n\le M`$, $`1\le K\le M`$, $`\delta>0`$, $`M\ge n^2/\delta`$; bound $`4C_\ast\delta`$ |
| Corollary 2.2, explicit quantitative (S62) specialization | `UniformHiding.corollary2_2_s62` | $`N=2n`$, $`\delta>0`$, $`m\ge n^2/\delta`$; source-scale product laws and bound $`4C_\ast\delta`$ |
| Route 1 of Theorem 3.1, shifted Haar-hafnian disk bound | `UniformHiding.routeOneSmallBall` | Hiding plus direct use of companion `ComplexGramHafnians.theorem2_1` |
| Route 1 of Theorem 3.2, one physical additive threshold | `UniformHiding.theorem3_2_route1` | Actual joint probability measure, measurable amplitude with specified Haar marginal, positive squeezing and tolerance, $`n\ge1`$, $`4n\le K\le M`$ |
| Route 1 infimum in Theorem 3.2 | `UniformHiding.theorem3_2_route1_optimized` | All nonnegative physical additive thresholds; exact capped hiding term |
| Route 2 deduction | `UniformHiding.routeTwoConditional` | Explicit Shou matrix-comparison and symmetric small-ball hypotheses; no proof of the Route 2 hiding input |
| Symmetric Gaussian anticoncentration used mathematically by Route 2 | `ComplexGramHafnians.theorem2_3` | Three foundations only; actual-law assembly with the generic Route 2 interface is not claimed |
| Hafnian and equal-squeezing probability | `hafnian`, `gbsCollisionFreePatternProbability`, `gbsProbabilityFromScaledAmplitude` | Optical probability formula is an adopted model, not a derivation of quantum dynamics |

See [Corollary 2.2 and the cited conjecture](COROLLARY_2_2.md) for the parameter dictionary, exact source-scale measure identities, and the mathematical translation to [10, Conjecture 1 and Eq. (S62)].

## Route 1 model correspondence

Lean uses `r` for the squeezing parameter $`\xi`$. Its `n` is the pair count, so the photon count is $`N=2n`$. The companion describes a $`K\times2n`$ column matrix $`X`$; the hiding paper writes $`G=X^T`$, giving $`X^TX=GG^T`$. The literal Gaussian pushforward identification is proved in `GBSDefinitions.lean`.

Lean uses the hafnian of $`M U_{2n,K}U_{2n,K}^T`$, hence the amplitude equals $`M^n`$ times the unscaled hafnian. Its physical probability multiplies the squared norm by the optical factor divided by $`M^{2n}`$. The Gaussian reference probability is the same factor times $`\sigma_{K,n}^2`$. The exact coefficient `paperBkn K n` comes from the companion's public specification.

The marginal hypothesis `Measure.map amplitude μ = scaledHaarGramHafnianLaw H M n K` permits any joint experiment containing that Haar-distributed amplitude and estimator randomness. It is a model assumption about the experiment. It is not an assumed anticoncentration estimate or an additional global axiom. Haar invariance justifies using any fixed preselected row pattern in the mathematical paper; no adaptive pattern selection is asserted by this public theorem.

The event argument uses $`\Delta p=\widetilde p-p_S`$, $`\eta=\tau/p_1`$, and $`\eta/\rho=\tau/(\rho p_1)`$. It preserves $`\delta_1=\min(1,615172(2n)^2/M)`$ instead of silently replacing it by an uncapped error. The optimized endpoint is the infimum of the fully assembled physical-threshold bound, not merely an isolated scalar optimization certificate.

## Appendix A: justification of the four Lean axioms

The revised Appendix A documents what the formalization assumes and why the cited sources justify those assumptions. It is not a list of missing steps in the mathematical proof. It has four axiom subsections and no A.5 subsection.

[AXIOMS.md](AXIOMS.md) follows the same four-part structure for every input: **(1) exact mathematical translation of the Lean axiom, (2) source statement, (3) differences and their justification, and (4) notation correspondence**. The translation is checked against the declaration and the definitions it uses, rather than relying on a code comment calling the result verbatim. Equation labels retain the paper's numbering.

| Input | Source-to-Lean correspondence |
| --- | --- |
| [A1](AXIOMS.md#a1) | The source's transposed COE product has the same Haar law. Independent symmetric coordinates and normalization give the imported matrix-law identity, including the boundary dimension case. |
| [A2](AXIOMS.md#a2) | The flat Takagi Jacobian gives one positive finite constant for every measurable symmetric test. The globally measurable selector and arbitrary target spaces are justified explicitly. |
| [A3](AXIOMS.md#a3) | The unordered squared GSVD law is represented by a concrete Hermitian matrix; the total inverse is zero on singular samples. Global measurability is part of the imported assertion. |
| [A4](AXIOMS.md#a4) | A Wishart probability law satisfying the transform identity is supplied as a hypothesis. The paired moments use an inverse matching-Gram coefficient, identified with the cited zonal formula with its exact normalization. |

[The expanded A2 justification](A2_SOURCE_DERIVATION.md) retains the full argument from FitzGerald–Warren's unnumbered Jacobian after Eq. (70) and An–Wang–Yan's Theorem 4.2 and following remark. It checks the positive ordered chamber, diagonal sign stabilizer, one-sheeted covering, differential, exceptional null set, coordinate-volume factor, chamber factor, and arbitrary measurable tests. In the notation dictionary, the integration theorem's subgroup $`K`$ is explicitly distinguished from the paper's ambient dimension.

These source-to-axiom arguments explain why the imported mathematical statements are justified. They are not presented as separate proofs checked in Lean. The naming revision preserves the mathematical contracts of the four axioms and the public theorem endpoints under the recorded identifier substitutions.

<a id="proposition-41-partial-coverage"></a>

## Proposition 4.1: completed deductions

The former partial-coverage status is superseded by the fresh completion. All entries below have checked proofs using only the three standard foundations.

| Component | Declaration in namespace `GBSHiding`, unless specified |
| --- | --- |
| Collision-free label count | `RelativeAccuracy.collisionFreeLabelSpace_card` |
| Normalized negative-binomial input law | `squeezedInputPairCount_eq`, `squeezedInputPhotonCount_even`, `squeezedInputPhotonCount_odd` |
| Generating function | `squeezedInputPairCount_generatingFunction` |
| Passive number conservation and sector probability | `passiveOptics_preserves_photonNumberLaw`, `proposition4_1_output_sector_probability` |
| Exact reference scale, without `hTotalPhoton` | `proposition4_1_reference_scale` |
| Maximizer and unique parameter | `proposition4_1_maximizer`, `pairMass_eq_optimal_iff` |
| Equivalent squeezing condition | `squeezing_mean_match_iff` |
| Uniform error, including odd input counts | `proposition4_1_uniform_relative_error`, `proposition4_1_stirling_isBigO` |
| Finite-population limit and final inverse-square-root scale | `finitePopulationFactor_tendsto_one`, `proposition4_1_reference_scale_isTheta` |

The [completion ledger](FORMALIZATION_COMPLETION.md#proposition-41) explains the optical model and its conditional-sector representation. The single-mode coefficients and passive tensor action define the adopted model. Their normalization, convolution and preservation of number sectors are proved. The old conditional `sectorReferenceMass` remains available for compatibility; it is no longer the endpoint used to claim the completed scale identity.

## Other named manuscript statements

| Manuscript claim | Coverage |
| --- | --- |
| Corollary 3.3 | Route 1's optimized public bound tends to zero by `GBSHiding.corollary3_3_route1_public`. The Route 2 half is excluded. |
| Corollary 4.2 | `GBSHiding.collisionFreeSamplerRelative_averageTV` and `collisionFreeSamplerRelativeOptimized_averageTV` use the actual average-TV hypothesis, including zero error. Only Route 1 is included. |
| Lemma 6.1 | The existing concrete Haar–Stiefel recursion and independent beta/sphere sampling development is retained. |
| Lemma 6.2 | The signed Markov contraction and concrete variation-norm derivative transport were already present. Both are included in the fresh dependency audit; the earlier missing-coverage report was mistaken. |
| Lemma 6.3 | `hidingLemmaIII3_eventwise_A1A2A3A4` gives the actual event paths, regularity and all five derivative bounds. |
| Proposition 6.4 | Existing concrete adjacent-ambient law bounds expose the evaluated constant 615138 and its weakening to 615172 in `HidingOutsideCDPaperFacing.lean`. |
| Lemma 6.5 | The rectangular density/entropy comparison and sparse branch are already proved and retained. |
| Lemma C.1 | Existing fixed-direction integrable derivatives, event regularity and differentiation/integration exchange cover the paper's dense range. |
| Corollary G.1 | `GBSHiding.observableHidingAllInputs` and `orderedFixedPatternPanelAllInputs` cover all positive input counts. |
| Proposition G.2 | `GBSHiding.orderedDisjointMaxScoreCdfTransferAllInputs` and `orderedDisjointHeavyCountBinomialTransferAllInputs` now cover the full range, including fewer inputs than selected rows. |

## Remaining boundaries

The non-Route-2 gaps listed above are closed relative to the existing literature and optical-model boundary. Route 2's cited matrix comparison remains unformalized; its existing conditional deduction does not prove that hypothesis. The two-route minima and Route 2 envelope claim are excluded from this completion.

A1–A4 are still literature axioms. The companion main Gaussian results require only the standard foundations. Appendix A's source-to-axiom justifications, the optical model's derivation from quantum dynamics, literature comparisons, illustrations and prose are not claimed as newly checked Lean proofs. The older equation crosswalk retains its own manuscript-snapshot scope.
