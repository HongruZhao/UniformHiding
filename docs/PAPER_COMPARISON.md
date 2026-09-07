# Manuscript-to-Lean correspondence

The theorem numbers refer to the revised manuscript, *Uniform Hiding and Two Routes to Relative Accuracy in Gaussian Boson Sampling*. `Theorem21` means Theorem **2.1**, not Theorem 21. The names beginning `theorem3_2_route1` mean the Route 1 part of Theorem **3.2**.

| Manuscript claim | Public declaration / source | Verification boundary |
| --- | --- | --- |
| Theorem 2.1, normalized matrix-law TV bound | `UniformHiding.theorem2_1` | Four literature axioms A1–A4 plus the three foundations |
| Equivalent unnormalized product bound | `GBSHiding.uniformHiding` | Same four literature axioms |
| All-input extension, including $`K<N`$ | `GBSHiding.AllInputs` | Existing measure-law proof; the principal public specification retains Theorem 2.1's stated range |
| Route 1 of Theorem 3.1, shifted Haar-hafnian disk bound | `UniformHiding.routeOneSmallBall` | Hiding plus direct use of companion `ComplexGramHafnians.theorem2_1` |
| Route 1 of Theorem 3.2, one physical additive threshold | `UniformHiding.theorem3_2_route1` | Actual joint probability measure, measurable amplitude with specified Haar marginal, positive squeezing and tolerance, $`n\ge1`$, $`4n\le K\le M`$ |
| Route 1 infimum in Theorem 3.2 | `UniformHiding.theorem3_2_route1_optimized` | All nonnegative physical additive thresholds; exact capped hiding term |
| Route 2 deduction | `UniformHiding.routeTwoConditional` | Explicit Shou matrix-comparison and symmetric small-ball hypotheses; no proof of the Route 2 hiding input |
| Symmetric Gaussian anticoncentration used mathematically by Route 2 | `ComplexGramHafnians.theorem2_3` | Three foundations only; actual-law assembly with the generic Route 2 interface is not claimed |
| Hafnian and equal-squeezing probability | `hafnian`, `gbsCollisionFreePatternProbability`, `gbsProbabilityFromScaledAmplitude` | Optical probability formula is an adopted model, not a derivation of quantum dynamics |

## Route 1 model correspondence

Lean uses `r` for the squeezing parameter $`\xi`$. Its `n` is the pair count, so the photon count is $`N=2n`$. The companion describes a $`K\times2n`$ column matrix $`X`$; the hiding paper writes $`G=X^T`$, giving $`X^TX=GG^T`$. The literal Gaussian pushforward identification is proved in `GBSDefinitions.lean`.

Lean uses the hafnian of $`M U_{2n,K}U_{2n,K}^T`$, hence the amplitude equals $`M^n`$ times the unscaled hafnian. Its physical probability multiplies the squared norm by the optical factor divided by $`M^{2n}`$. The Gaussian reference probability is the same factor times $`\sigma_{K,n}^2`$. The exact coefficient `paperBkn K n` comes from the companion's public specification.

The marginal hypothesis `Measure.map amplitude μ = scaledHaarGramHafnianLaw H M n K` permits any joint experiment containing that Haar-distributed amplitude and estimator randomness. It is a model assumption about the experiment. It is not an assumed anticoncentration estimate or an additional global axiom. Haar invariance justifies using any fixed preselected row pattern in the mathematical paper; no adaptive pattern selection is asserted by this public theorem.

The event argument uses $`\Delta p=\widetilde p-p_S`$, $`\eta=\tau/p_1`$, and $`\eta/\rho=\tau/(\rho p_1)`$. It preserves $`\delta_1=\min(1,615172(2n)^2/M)`$ instead of silently replacing it by an uncapped error. The optimized endpoint is the infimum of the fully assembled physical-threshold bound, not merely an isolated scalar optimization certificate.

## Appendix A: justification of the four Lean axioms

The revised Appendix A (7 September 2026, pages 12–18) documents what the formalization assumes and why the cited sources justify those assumptions. It is not a list of missing steps in the mathematical proof. It has four axiom subsections and no A.5 subsection.

[AXIOMS.md](AXIOMS.md) follows the same four-part structure for every input: **(1) exact mathematical translation of the Lean axiom, (2) source statement, (3) differences and their justification, and (4) notation correspondence**. The translation is checked against the declaration and the definitions it uses, rather than relying on a code comment calling the result verbatim. Equation tags retain the paper's numbering.

| Input | Source-to-Lean correspondence |
| --- | --- |
| [A1](AXIOMS.md#a1) | The source's transposed COE product has the same Haar law. Independent symmetric coordinates and normalization give the imported matrix-law identity, including the boundary dimension case. |
| [A2](AXIOMS.md#a2) | The flat Takagi Jacobian gives one positive finite constant for every measurable symmetric test. The globally measurable selector and arbitrary target spaces are justified explicitly. |
| [A3](AXIOMS.md#a3) | The unordered squared GSVD law is represented by a concrete Hermitian matrix; the total inverse is zero on singular samples. Global measurability is part of the imported assertion. |
| [A4](AXIOMS.md#a4) | A Wishart probability law satisfying the transform identity is supplied as a hypothesis. The paired moments use an inverse matching-Gram coefficient, identified with the cited zonal formula with its exact normalization. |

[The expanded A2 justification](A2_SOURCE_DERIVATION.md) retains the full argument from FitzGerald–Warren's unnumbered Jacobian after Eq. (70) and An–Wang–Yan's Theorem 4.2 and following remark. It checks the positive ordered chamber, diagonal sign stabilizer, one-sheeted covering, differential, exceptional null set, coordinate-volume factor, chamber factor, and arbitrary measurable tests. In the notation dictionary, the integration theorem's subgroup K is explicitly distinguished from the paper's ambient dimension.

These source-to-axiom arguments explain why the imported mathematical statements are justified. They are not presented as separate proofs checked in Lean. The naming revision preserves the mathematical contracts of the four axioms and the public theorem endpoints under the recorded identifier substitutions.

## Scope beyond the selected endpoints

The source tree includes supporting calculations and older application interfaces. The published archive's older equation crosswalk addresses its own manuscript snapshot; it must not be read as a claim that every equation of the current manuscript has a single unconditional endpoint.

The broader development does not fully assemble the photon-sector identity, universal uniform Stirling statement, or every sampler application. The newly assembled Route 1 threshold infimum resolves that specific optimization connection, not all sampler/optimized-certificate connections. Route 2's cited hiding theorem remains outside the formal proof. Complete formalization of every revised manuscript statement is not claimed.

Four literature axioms are required for hiding and Route 1. The companion main Gaussian theorems have no additional scientific axioms. These two statements about formalization must not be conflated.
