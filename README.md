# Uniform Hiding and Two Routes to Relative Accuracy in Gaussian Boson Sampling

Lean verification accompanying Hongru Zhao's manuscript. The main hiding theorem and the Route 1 part of the relative-accuracy theorem are proved **conditional on four explicitly cited literature axioms**. The companion Gaussian anticoncentration theorem has no additional scientific axioms.

## Results and probability conventions

Let $`U`$ be Haar distributed on the unitary group $`\mathrm{U}(M)`$, and let $`U_{N,K}`$ be its first $`N`$ rows and $`K`$ columns. Let $`G`$ be an $`N\times K`$ matrix of independent circular complex Gaussians with density $`\pi^{-1}e^{-|z|^2}`$; each real and imaginary component has variance $`1/2`$. The superscript $`T`$ denotes ordinary transpose. Total variation is $`d_{\mathrm{TV}}(\mu,\nu)=\sup_E|\mu(E)-\nu(E)|`$, with measurable $`E`$.

**Theorem 2.1 (uniform hiding).** For every $`1\le N\le M`$ and $`1\le K\le M`$,

```math
 d_{\mathrm{TV}}\!\left(\mathcal L\!\left(\frac{M}{\sqrt K}U_{N,K}U_{N,K}^{T}\right),
 \mathcal L\!\left(\frac{1}{\sqrt K}GG^{T}\right)\right)
 \le \min\!\left\lbrace 1,C_\ast\frac{N^2}{M}\right\rbrace,
 \qquad C_\ast=615172.
```

The theorem includes $`K<N`$. Multiplying both matrices by $`\sqrt K`$ gives the equivalent product form

```math
 d_{\mathrm{TV}}\!\left(\mathcal L(MU_{N,K}U_{N,K}^{T}),
 \mathcal L(GG^{T})\right)
 \le \min\!\left\lbrace 1,C_\ast\frac{N^2}{M}\right\rbrace.
```

The public declarations are `UniformHiding.theorem2_1`, with specification `UniformHiding.Theorem21`, and `UniformHiding.theorem2_1_unscaled`. The proof combines the earlier result for $`N\le K`$ with the existing rectangular comparison for $`K<N`$.

## Corollary 2.2: the quantitative hiding conjecture

Let $`n\ge1`$, $`N=2n\le M`$, $`1\le K\le M`$, and $`\delta>0`$. If $`M\ge n^2/\delta`$, Theorem 2.1 immediately gives

```math
 d_{\mathrm{TV}}\!\left(\mathcal L(MU_{2n,K}U_{2n,K}^{T}),
 \mathcal L(G_{2n,K}G_{2n,K}^{T})\right)
 \le 4C_\ast\delta=2460688\delta.
```

The public declaration is `UniformHiding.corollary2_2`, with specification `UniformHiding.Corollary22`. Its Lean proof is the direct substitution and inequality $`C_\ast(2n)^2/M\le4C_\ast\delta`$. The manuscript therefore needs no separate corollary proof.

This establishes **[10, Conjecture 1 (Formal) and Supplemental Eq. (S62)]**, in Ehrenberg et al., *Transition of Anticoncentration in Gaussian Boson Sampling*, Physical Review Letters **134**, 140601 (2025), [published article](https://doi.org/10.1103/PhysRevLett.134.140601), [full preprint and supplement](https://arxiv.org/html/2312.08433v2#S0.S5). Here [10] is the hiding manuscript's reference number.

`UniformHiding.corollary2_2_s62` gives the same quantitative bound after putting both product laws on the source's scale. The [theorem, corollary, and source correspondence](docs/COROLLARY_2_2.md) explains the block orientation, Gaussian variance, measure identities, and exact proof boundary. These results use the same four literature axioms.

## Hafnian and the physical output probability

Put $`N=2n`$. For a complex symmetric $`2n\times2n`$ matrix $`A`$, let $`\mathcal P_2(2n)`$ be the perfect matchings of $`\lbrace 1,\ldots,2n\rbrace`$. Define

```math
 \mathrm{haf}(A)=\sum_{\pi\in\mathcal P_2(2n)}\ \prod_{\lbrace i,j\rbrace \in\pi} A_{ij}.
```

The diagonal entries do not occur. For $`\xi>0`$, squeeze the first $`K`$ input modes equally by $`\xi`$ and leave the others in vacuum. For a fixed collision-free output pattern $`S\subseteq\lbrace 1,\ldots,M\rbrace`$ with $`|S|=2n`$, write

```math
 A_S=U_{S,[K]}U_{S,[K]}^T,\qquad
 p_S(U;\xi)=\frac{\tanh(\xi)^{2n}}{\cosh(\xi)^K}
              |\mathrm{haf}(A_S)|^2.
```

This is the probability of the full occupation pattern, without conditioning on the total photon number. The optical formula is the adopted model; this repository does not derive it from quantum optical dynamics. The Lean definition is `gbsCollisionFreePatternProbability` in [GBSDefinitions.lean](LogdetLean/GramHafnian/ThreePaper/GBSDefinitions.lean). With scaled amplitude $`W=M^n\mathrm{haf}(A_S)`$, `gbsProbabilityFromScaledAmplitude` is the same formula with the additional factor $`M^{-2n}`$. Haar row symmetry identifies any fixed pattern with the leading-block law; the public randomized statement specifies that amplitude marginal explicitly.

## Theorem 3.2: Route 1 is assembled

Assume $`n\ge1`$, $`4n\le K\le M`$, and $`\xi>0`$. Set

```math
 \sigma_{K,n}^2=(2n-1)!!\prod_{q=0}^{n-1}(K+2q),\qquad
 b_n=\frac{2\Gamma(n+1/2)}{\sqrt\pi\,\Gamma(n)},\qquad
 B_{K,n}=b_n\frac{K}{K-1}\prod_{j=2}^{n}\frac{K+2j-2}{K-4j+1},
```

```math
 p_1=\frac{\tanh(\xi)^{2n}}{M^{2n}\cosh(\xi)^K}\sigma_{K,n}^2,
 \qquad \delta_1=\min\left\lbrace 1,615172\frac{(2n)^2}{M}\right\rbrace .
```

For one randomized estimate $`\widetilde p`$, put $`\Delta p=\widetilde p-p_S`$, $`\gamma(\tau)=\Pr(|\Delta p|>\tau)`$ and $`F_\rho=\Pr(|\Delta p|>\rho p_S)`$. For every physical additive threshold $`\tau\ge0`$ and relative tolerance $`\rho>0`$,

```math
 F_\rho\le E_1(\tau)
 =\min\left\lbrace 1,\gamma(\tau)+B_{K,n}\frac{\tau}{\rho p_1}+\delta_1\right\rbrace ,
 \qquad F_\rho\le\inf_{\tau\ge0}E_1(\tau).
```

The public declarations are `UniformHiding.theorem3_2_route1` and `UniformHiding.theorem3_2_route1_optimized`. Their joint probability space can include estimator randomness, and they require the amplitude to have its specified Haar marginal. They do not assume that the estimator is independent of the interferometer. The normalization $`p_1`$ is a Gaussian reference, not the finite-Haar expectation.

Route 1 combines the hiding bound with the companion Gaussian anticoncentration theorem from [ComplexGramHafnians (the source version used in this release)](https://github.com/HongruZhao/ComplexGramHafnians/tree/95ab10dc594ac92207054413220ae9fd2adab08c). The connection is made by `UniformHiding.routeOneSmallBall`, which invokes `ComplexGramHafnians.theorem2_1`. The theorem and all required proof files are included in this repository. Their mathematical content is preserved; [source provenance](docs/PROVENANCE.md) explains how the included files are checked against the original sources.

## Route 2: the hiding input is not formalized

Let $`G_{\mathrm{sym}}`$ be complex symmetric, with independent entries on and above the diagonal, off-diagonal variance one and diagonal variance two. Define

```math
 p_2=\frac{\tanh(\xi)^{2n}K^n}{M^{2n}\cosh(\xi)^K}(2n-1)!!,
 \qquad R_{K,n}=\prod_{q=0}^{n-1}\left(1+\frac{2q}{K}\right),
 \qquad p_1=R_{K,n}p_2.
```

If a certified bound $`\delta_2`$ is supplied for the total variation distance from $`MK^{-1/2}U_{2n,K}U_{2n,K}^{T}`$ to $`G_{\mathrm{sym}}`$, the second route gives

```math
 F_\rho\le E_2(\tau)
 =\min\left\lbrace 1,\gamma(\tau)+b_nR_{K,n}\frac{\tau}{\rho p_1}+\delta_2\right\rbrace .
```

Under that additional comparison input, the manuscript combines the routes for the **same estimator and threshold**:

```math
 F_\rho\le\min\lbrace E_1(\tau),E_2(\tau)\rbrace,
 \qquad F_\rho\le\min\left\lbrace\inf_{\tau\ge0}E_1(\tau),\inf_{\tau\ge0}E_2(\tau)\right\rbrace.
```

The additional external input is [Shou, Gorshkov, Galitski and Miller (2026), Theorem 1.1](https://arxiv.org/html/2608.19314v1), which states an asymptotic $`O(N/\sqrt K)`$ symmetric-Gaussian hiding bound. Its implicit constant is not an explicit numerical finite-size certificate.

The repository retains `UniformHiding.routeTwoConditional` and the [Route 2 interface](LogdetLean/GramHafnian/ThreePaper/RouteTwoMatrixComparisonInterface.lean). These verify deductions **given** `ShouSymmetricMatrixComparisonAt` and the stated symmetric small-ball premise. They do not prove the Shou comparison or fully assemble the actual symmetric-Gaussian Route 2. This is the fifth external literature input in the two-route discussion, **not a fifth Lean axiom**. The unconditional symmetric-Gaussian small-ball result itself is available as `ComplexGramHafnians.theorem2_3`.

## Four literature axioms

The axiom documentation explains **what Lean assumes and why the cited sources justify it**, following the revised manuscript's Appendix A. Each of A1–A4 is presented in the same order: **(1) exact mathematical translation from Lean, (2) statement in the source, (3) differences and their justification, and (4) notation correspondence**. The source-to-axiom arguments justify the imported assumptions; they are not presented as separately checked Lean proofs.

| Input | Mathematical content | Source |
| --- | --- | --- |
| [A1](docs/AXIOMS.md#a1) | Haar principal COE corner equals its self-normalized determinant density | Friedman–Mello (1985), Eqs. (1.2), (3.7) and Appendix 1 |
| [A2](docs/AXIOMS.md#a2) | Global spectrum measurability and one positive finite constant for all measurable symmetric-test pushforwards | FitzGerald–Warren (2020), §6, p. 165, Jacobian after (70); An–Wang–Yan (2006), Thm. 4.2 and following remark |
| [A3](docs/AXIOMS.md#a3) | Globally measurable squared GSVD coordinates and their beta Jacobi law under symmetric tests | Edelman–Sutton (2008), Def. 1.1 and Prop. 1.2 |
| [A4](docs/AXIOMS.md#a4) | Paired tensor moment identities for a supplied Wishart probability law satisfying its Laplace-transform characterization | Matsumoto (2012), Thm. 3; Eq. (4.10), Lemma 5 and Eq. (5.2) identify the coefficient convention |

[AXIOMS.md](docs/AXIOMS.md) gives the full mathematical statements, source comparisons, and declaration links. [The expanded A2 justification](docs/A2_SOURCE_DERIVATION.md) checks the Takagi integration map, normalization, global selector measurability, and arbitrary measurable targets. A3 explicitly includes the coordinate definition on singular samples. A4 distinguishes its supplied-law hypothesis from its moment conclusions and explains the inverse-Gram/zonal Weingarten equivalence.

There are exactly four literature axioms. In addition, Lean uses `propext`, `Classical.choice`, and `Quot.sound`. The theorem axiom check must match that set; the imported anticoncentration endpoints must match only the three foundations. The stronger Theorem 2.1 and its quantitative corollary preserve these four mathematical contracts and add no axiom.

## Files and verification

| File | Purpose |
| --- | --- |
| [HidingStatement.lean](HidingStatement.lean) | Theorem 2.1, Corollary 2.2, source-scale (S62) specification, and Route 1 budget |
| [UniformHiding.lean](UniformHiding.lean) | Public hiding, Corollary 2.2, source-scale measure identities, and Route 1 proofs |
| [HidingVerification.lean](HidingVerification.lean) | Exact public proof dependency checks |
| [docs/PAPER_COMPARISON.md](docs/PAPER_COMPARISON.md) | Paper-to-Lean correspondence and scope limits |
| [verification/STATUS.md](verification/STATUS.md) | Dated build evidence |
| [docs/PROVENANCE.md](docs/PROVENANCE.md) | Source origin and companion dependency |

With [elan](https://github.com/leanprover/elan) installed, run:

```sh
lake exe cache get
LEAN_NUM_THREADS=4 lake build UniformHiding HidingVerification
LEAN_NUM_THREADS=4 lake env lean HidingVerification.lean
python3 scripts/source_audit.py
python3 scripts/markdown_audit.py
```

The pinned toolchain is selected automatically. A successful build checks these formal statements relative to the disclosed axioms; it does not certify every sentence in the manuscript. There is no `sorry`, `admit`, or additional project axiom in the released proof sources.

## Archive and citation

Version **1.2.0** promotes the bound for all positive input counts to Theorem 2.1 and makes Corollary 2.2 its immediate quantitative specialization. The GitHub repository and the accompanying Zenodo source package contain the same Lean statements and proofs. See [the change history](CHANGELOG.md) and [source provenance](docs/PROVENANCE.md) for the relationship to version 1.1.0.

The archive identifier for **version 1.2.0** is [10.5281/zenodo.22670050](https://doi.org/10.5281/zenodo.22670050). The preceding archives are [version 1.1.0](https://doi.org/10.5281/zenodo.22558885) and [version 1.0.0](https://doi.org/10.5281/zenodo.22122730). Cite the version actually used; see [CITATION.cff](CITATION.cff). The archive contains Lean sources and verification records, with no manuscript PDFs or LaTeX sources.

Copyright © 2026 Hongru Zhao. Licensed under GPL-3.0-only.

## Acknowledgments

The organization follows the statement/proof/verification separation used by [PrimeGaps186](https://github.com/openai/PrimeGaps186) and [ComplexGramHafnians](https://github.com/HongruZhao/ComplexGramHafnians).
