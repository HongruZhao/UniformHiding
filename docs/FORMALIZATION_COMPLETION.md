# Completion of the hiding-paper formalization, excluding Route 2

The remaining non-Route-2 deductions identified for the 48-page hiding manuscript now have checked Lean proofs: Proposition 4.1's sector law, maximization and asymptotics; the average-TV form of Corollary 4.2; the optimized Route 1 conclusion of Corollary 3.3; and the full input range in Proposition G.2.

The public build and two separate Lean executions passed on 9 September 2026 in America/Chicago. The exact dependency audit checks **47 declarations**: 14 use the existing four literature axioms and the three standard foundations; 33 use only the foundations. There are **no additional project axioms**. The execution reused pinned dependency caches and rebuilt changed modules and their dependents. It was not a wholly uncached build or an independent checker run.

The source tree has 893 Lean modules: 12 new modules, two changed import/audit entrypoints, and 879 byte-identical baseline modules. All 225 companion sources and all four literature-axiom declarations are unchanged. The [execution receipt](../verification/completion_receipt.json) records source hashes, endpoint dependencies and log hashes. The [source manifest](COMPLETION_SOURCES.json) preserves the preceding entrypoints for comparison.

## Proposition 4.1

Write $`N=2n`$, $`a=K/2`$ and $`x=\tanh^2\xi`$. The single-mode pair weights are

```math
 \frac{\binom{2n}{n}}{4^n}\frac{\tanh^{2n}\xi}{\cosh\xi}.
```

Lean constructs a probability mass function from these weights, proves its total mass is one, and sums independent inputs by convolution. For every natural input count, including odd $`K`$, the resulting shape is $`K/2`$. It also proves the generating function, the even-photon probabilities, and zero odd-photon probability.

| Conclusion | Declaration in namespace `GBSHiding` |
| --- | --- |
| Single-mode weights | `singleMode_pair_mass` |
| Normalization and convolution | `pairMass_hasSum_one`, `photonPairPMF_add`, `squeezedInputPairCount_eq` |
| Generating function and photon-count law | `squeezedInputPairCount_generatingFunction`, `squeezedInputPhotonCount_even`, `squeezedInputPhotonCount_odd` |
| Passive number conservation | `photonTensorMatrix_unitary`, `passiveOptics_preserves_photonNumberLaw` |
| Preservation of bosonic symmetry | `passiveOptics_preserves_bosonicSymmetry` |
| Output sector probability | `proposition4_1_output_sector_probability` |
| Exact reference-scale identity | `proposition4_1_reference_scale` |
| Global maximum and unique parameter | `proposition4_1_maximizer`, `pairMass_eq_optimal_iff` |
| Equivalent squeezing conditions and explicit solution | `squeezing_mean_match_iff`, `meanMatchedSqueezing` |
| Uniform Stirling estimate | `proposition4_1_uniform_relative_error`, `proposition4_1_stirling_isBigO` |
| Finite-population factor and final scale | `finitePopulationFactor_bounds`, `finitePopulationFactor_tendsto_one`, `proposition4_1_reference_scale_isTheta` |

The number-preservation proof uses the actual matrix $`U^{\otimes N}`$ on the ordered tensor basis. It proves unitarity by factoring the sum over configurations into the column inner products of $`U`$. It also proves preservation of permutation-symmetric vectors, so the action restricts to the bosonic sector. Every sector's squared norm is preserved.

The output-sector endpoint permits any normalized bosonic state conditional on the input pair count. Its weights come from the independently convolved single-mode law. The conditional-state premise specifies unit norm; it does not supply a total-photon formula or a conservation assertion. Neither the new reference-scale theorem nor the output-sector theorem has the old `hTotalPhoton` premise.

The single-mode squeezed-vacuum coefficients and passive tensor action specify the adopted optical model. Their derivation from a Hamiltonian, and derivation of the full optical hafnian probability formula, remain outside this development. They are not concealed as additional Lean axioms.

At the maximum, for every $`n\ge1`$ and $`K\ge4n`$, the proved finite bound is

```math
 \left|W_{K,n}\sqrt{2\pi n(1+2n/K)}-1\right|\le\frac{2}{3n}.
```

The proof treats integer and half-integer Gamma arguments. It derives explicit logarithmic remainders using the proved integer Stirling limit and Gamma duplication, then performs the three-Gamma cancellation. The final theorem has the manuscript's reference probability on the left:

```math
 \binom M{2n}p_1=\Theta\!\left(\frac{1}{\sqrt{2n}}\right)
 \quad\text{when}\quad
 K\ge4n,\quad K\sinh^2\xi=2n,\quad (2n)^2/M\longrightarrow0.
```

The dimension and squeezing conditions are eventual hypotheses along the parameter sequences. The inverse square root is exactly $`N^{-1/2}`$. This concerns the Gaussian reference scale, not an assertion of collision suppression in the finite interferometer.

## Corollary 4.2: average TV

`collisionFreeSamplerRelative_averageTV` and `collisionFreeSamplerRelativeOptimized_averageTV` use probability mass functions on a countable full outcome space. Their hypothesis is the average-TV bound, with TV defined as half the full absolute-mass sum. They do not assume a bound for every interferometer.

The proof restricts the sum to the collision-free labels, averages over Haar interferometers, applies Markov's inequality, and supplies the actual Route 1 dark-event estimate. Its conclusion represents the relative-failure probability as the Haar integral of the uniform-label failure fraction. The optimized bound is

```math
 \min\!\left\lbrace1,\delta_1+
 2\sqrt{\frac{2B_{K,n}\epsilon_{\rm sam}}{\rho D_{M,N}p_1}}
 \right\rbrace.
```

Both endpoints include zero sampling error. The probability cap and square-root optimization are proved. Their model hypotheses identify the ideal collision-free probabilities with the adopted optical formula and the selected labels with the collision-free patterns. No small-ball conclusion remains as a hypothesis in these physical endpoints.

## Corollary 3.3 and Proposition G.2

`corollary3_3_route1_public` proves convergence to zero of the public optimized Route 1 bound. It substitutes the actual additive-failure probability and physical reference scale into the coefficient asymptotics and takes the infimum over all nonnegative thresholds. That infimum is explicitly identified with `UniformHiding.optimizedRouteOneBound`; no minimizing threshold is assumed to exist. The paper's polynomial threshold, ambient-growth and additive-failure hypotheses remain explicit.

`orderedDisjointPatternProductHidingAllInputs`, `orderedDisjointMaxScoreCdfTransferAllInputs`, and `orderedDisjointHeavyCountBinomialTransferAllInputs` give the independent-product comparison, maximum-CDF transfer and binomial-count transfer for all $`1\le K\le M`$ and $`1\le L\le M`$. They preserve the disjoint-row and measurability assumptions and permit $`K<L`$.

## Correction to the earlier coverage report

The earlier report incorrectly described Lemma 6.2's signed-measure extension and derivative transport as missing. Both were already proved and imported in the baseline. Their exact declarations are rechecked here:

- `Verification.signedKernelContinuousLinearMap_norm_le_one` gives the signed Markov action and its variation-norm contraction.
- `Verification.ConcreteCongruenceKernelAdapter.congruenceKernel_eq_hide_commute_derivative` gives the concrete orbital/congruence derivative identity and norm bound under the stated invariance and regularity hypotheses.

Here `Verification` abbreviates `LogdetLean.GramHafnian.ThreePaper.Verification`. These two endpoints use only the three foundations. They are reused proofs, not new proofs written in this update.

## Remaining boundaries

Route 2 was explicitly excluded. Its existing conditional interface remains; the symmetric-Gaussian matrix comparison and full Route 2 assembly have not been added. The two-route minima and Route 2 part of the envelope-separation statement are not newly claimed as complete.

A1–A4 remain the four disclosed literature axioms. Their source-to-axiom explanations in Appendix A are mathematical documentation, not newly formalized proofs. Optical model derivations, literature/novelty comparisons, figures and prose are not certified by a Lean build. The [paper correspondence](PAPER_COMPARISON.md) distinguishes these boundaries from the proved deductions.

## Reproduce the checks

```sh
LEAN_NUM_THREADS=4 lake build UniformHiding HidingVerification
LEAN_NUM_THREADS=4 lake env lean HidingVerification.lean
LEAN_NUM_THREADS=4 lake env lean GBSHiding/CompletionAudit.lean
python3 scripts/source_audit.py
python3 scripts/markdown_audit.py
```

Follow the root README for the pinned Lean and dependency setup. The [combined audit](../verification/completion_axiom_audit.log) checks 47 exact dependency sets; the [type log](../verification/completion_types.log) prints the main added statements. The shared core contains these completed deductions. Zenodo version 1.3.0, identified by 10.5281/zenodo.22670050, additionally includes the Appendix E and current-paper equation supplements.
