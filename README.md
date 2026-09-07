# Uniform Hiding and Two Routes to Relative Accuracy in Gaussian Boson Sampling

Lean verification accompanying Hongru Zhao's manuscript. The main hiding theorem and the Route 1 part of the relative-accuracy theorem are proved **conditional on four explicitly cited literature axioms**. The companion Gaussian anticoncentration theorem has no additional scientific axioms.

The organization follows the statement/proof/verification separation used by [PrimeGaps186](https://github.com/openai/PrimeGaps186) and [ComplexGramHafnians](https://github.com/HongruZhao/ComplexGramHafnians).

## Results and probability conventions

Let $U$ be Haar distributed on the unitary group $\mathrm{U}(M)$, and let $U_{N,K}$ be its first $N$ rows and $K$ columns. Let $G$ be an $N\times K$ matrix of independent circular complex Gaussians with density $\pi^{-1}e^{-|z|^2}$; each real and imaginary component has variance $1/2$. The superscript $T$ denotes ordinary transpose. Total variation is $d_{\mathrm{TV}}(\mu,\nu)=\sup_E|\mu(E)-\nu(E)|$, with measurable $E$.

**Theorem 2.1 (uniform hiding).** For $1\le N\le K\le M$,

```math
 d_{\mathrm{TV}}\!\left(\mathcal L\!\left(\frac{M}{\sqrt K}U_{N,K}U_{N,K}^{T}\right),
 \mathcal L\!\left(\frac{1}{\sqrt K}GG^{T}\right)\right)
 \le \min\!\left\lbrace 1,615172\frac{N^2}{M}\right\rbrace .
```

The public declaration is `UniformHiding.theorem2_1`, with specification `UniformHiding.Theorem21`. The inherited `GBSHiding.AllInputs` module also handles $K<N$ under its stated dimension conditions.

## Hafnian and the physical output probability

Put $N=2n$. For a complex symmetric $2n\times2n$ matrix $A$, let $\mathcal P_2(2n)$ be the perfect matchings of $\lbrace 1,\ldots,2n\rbrace $. Define

```math
 \mathrm{haf}(A)=\sum_{\pi\in\mathcal P_2(2n)}\ \prod_{\lbrace i,j\rbrace \in\pi} A_{ij}.
```

The diagonal entries do not occur. For $\xi>0$, squeeze the first $K$ input modes equally by $\xi$ and leave the others in vacuum. For a fixed collision-free output pattern $S\subseteq\lbrace 1,\ldots,M\rbrace $ with $|S|=2n$, write

```math
 A_S=U_{S,[K]}U_{S,[K]}^T,\qquad
 p_S(U;\xi)=\frac{\tanh(\xi)^{2n}}{\cosh(\xi)^K}
              |\mathrm{haf}(A_S)|^2.
```

This is the probability of the full occupation pattern, without conditioning on the total photon number. The optical formula is the adopted model; this repository does not derive it from quantum optical dynamics. The Lean definition is `gbsCollisionFreePatternProbability` in [PRLCommonDefinitions.lean](LogdetLean/GramHafnian/ThreePaper/PRLCommonDefinitions.lean). With scaled amplitude $W=M^n\mathrm{haf}(A_S)$, `gbsProbabilityFromScaledAmplitude` is the same formula with the additional factor $M^{-2n}$. Haar row symmetry identifies any fixed pattern with the leading-block law; the public randomized statement specifies that amplitude marginal explicitly.

## Theorem 3.2: Route 1 is assembled

Assume $n\ge1$, $4n\le K\le M$, and $\xi>0$. Set

```math
 \sigma_{K,n}^2=(2n-1)!!\prod_{q=0}^{n-1}(K+2q),\qquad
 b_n=\frac{2\Gamma(n+1/2)}{\sqrt\pi\,\Gamma(n)},\qquad
 B_{K,n}=b_n\frac{K}{K-1}\prod_{j=2}^{n}\frac{K+2j-2}{K-4j+1},
```

```math
 p_1=\frac{\tanh(\xi)^{2n}}{M^{2n}\cosh(\xi)^K}\sigma_{K,n}^2,
 \qquad \delta_1=\min\left\lbrace 1,615172\frac{(2n)^2}{M}\right\rbrace .
```

For one randomized estimate $\widetilde p$, put $\Delta p=\widetilde p-p_S$, $\gamma(\tau)=\Pr(|\Delta p|>\tau)$ and $F_\rho=\Pr(|\Delta p|>\rho p_S)$. For every physical additive threshold $\tau\ge0$ and relative tolerance $\rho>0$,

```math
 F_\rho\le E_1(\tau)
 =\min\left\lbrace 1,\gamma(\tau)+B_{K,n}\frac{\tau}{\rho p_1}+\delta_1\right\rbrace ,
 \qquad F_\rho\le\inf_{\tau\ge0}E_1(\tau).
```

The public declarations are `UniformHiding.theorem3_2_route1` and `UniformHiding.theorem3_2_route1_optimized`. Their joint probability space can include estimator randomness, and they require the amplitude to have its specified Haar marginal. They do not assume that the estimator is independent of the interferometer. The normalization $p_1$ is a Gaussian reference, not the finite-Haar expectation.

The bridge `UniformHiding.routeOneSmallBall` explicitly invokes `ComplexGramHafnians.theorem2_1`. We include an unchanged source snapshot of that companion theorem and its dependencies, pinned to commit [95ab10d](https://github.com/HongruZhao/ComplexGramHafnians/tree/95ab10dc594ac92207054413220ae9fd2adab08c). This is a **vendored source dependency**, so the build does not need access to a second private repository. [Provenance](docs/PROVENANCE.md) records the exact source hashes.

## Route 2: the hiding input is not formalized

Let $G_{\mathrm{sym}}$ be complex symmetric, with independent entries on and above the diagonal, off-diagonal variance one and diagonal variance two. Define

```math
 p_2=\frac{\tanh(\xi)^{2n}K^n}{M^{2n}\cosh(\xi)^K}(2n-1)!!,
 \qquad R_{K,n}=\prod_{q=0}^{n-1}\left(1+\frac{2q}{K}\right),
 \qquad p_1=R_{K,n}p_2.
```

If a certified bound $\delta_2$ is supplied for the total variation distance from $MK^{-1/2}U_{2n,K}U_{2n,K}^{T}$ to $G_{\mathrm{sym}}$, the second route gives

```math
 F_\rho\le E_2(\tau)
 =\min\left\lbrace 1,\gamma(\tau)+b_nR_{K,n}\frac{\tau}{\rho p_1}+\delta_2\right\rbrace .
```

Under that additional comparison input, the manuscript combines the routes for the **same estimator and threshold**:

```math
 F_\rho\le\min\lbrace E_1(\tau),E_2(\tau)\rbrace,
 \qquad F_\rho\le\min\left\lbrace\inf_{\tau\ge0}E_1(\tau),\inf_{\tau\ge0}E_2(\tau)\right\rbrace.
```

The additional external input is [Shou, Gorshkov, Galitski and Miller (2026), Theorem 1.1](https://arxiv.org/html/2608.19314v1), which states an asymptotic $O(N/\sqrt K)$ symmetric-Gaussian hiding bound. Its implicit constant is not an explicit numerical finite-size certificate.

The repository retains `UniformHiding.routeTwoConditional` and the [Route 2 interface](LogdetLean/GramHafnian/ThreePaper/RouteTwoMatrixComparisonInterface.lean). These verify deductions **given** `ShouSymmetricMatrixComparisonAt` and the stated symmetric small-ball premise. They do not prove the Shou comparison or fully assemble the actual symmetric-Gaussian Route 2. This is the fifth external literature input in the two-route discussion, **not a fifth Lean axiom**. The unconditional symmetric-Gaussian small-ball result itself is available as `ComplexGramHafnians.theorem2_3`.

## Four literature axioms

| Input | Mathematical content | Source |
| --- | --- | --- |
| A1 | COE principal-block determinant density | Friedman–Mello (1985), Eqs. (1.2), (3.7) |
| A2′ | Complex-symmetric Takagi–Weyl radial integration | Helgason (2000), Ch. I, Thm. 5.17; coordinate factors in Chen et al. (2019), App. A.2 |
| A3 | Gaussian GSVD beta-Jacobi law | Edelman–Sutton (2008), Def. 1.1 and Prop. 1.2 |
| A4 | Wishart and inverse-Wishart tensor moments | Matsumoto (2012), Thm. 3 |

[AXIOMS.md](docs/AXIOMS.md) gives the precise declarations, source links, parameter substitutions, measure conventions, and the measurable extension included in A2′. These inputs are assumed, not reproved. In addition, Lean uses `propext`, `Classical.choice`, and `Quot.sound`. The theorem axiom check must match this exact set of four literature inputs plus three foundations; the imported anticoncentration endpoints must match only the three foundations.

## Files and verification

| File | Purpose |
| --- | --- |
| [HidingStatement.lean](HidingStatement.lean) | Hiding specification and exact Route 1 error budget |
| [UniformHiding.lean](UniformHiding.lean) | Public hiding and Route 1 proofs; conditional Route 2 alias |
| [HidingVerification.lean](HidingVerification.lean) | Exact public proof dependency checks |
| [docs/PAPER_COMPARISON.md](docs/PAPER_COMPARISON.md) | Paper-to-Lean correspondence and scope limits |
| [verification/STATUS.md](verification/STATUS.md) | Dated build evidence |
| [docs/PROVENANCE.md](docs/PROVENANCE.md) | Source origin and companion dependency |

With [elan](https://github.com/leanprover/elan) installed, run:

```sh
lake exe cache get
LEAN_NUM_THREADS=4 lake build
python3 scripts/source_audit.py
```

The pinned toolchain is selected automatically. A successful build checks these formal statements relative to the disclosed axioms; it does not certify every sentence in the manuscript. There is no `sorry`, `admit`, or additional project axiom in the released proof sources.

## Archive and citation

The [published Zenodo record](https://doi.org/10.5281/zenodo.22122730) is version 1.0.0. The [version 1.1.0 draft](https://zenodo.org/uploads/22558885) is unpublished (reserved DOI `10.5281/zenodo.22558885`); it contains this source release, broader verification material, and the coverage ledger. The new upload contains no manuscript PDFs or LaTeX sources. Cite the version actually used. See [CITATION.cff](CITATION.cff).

Copyright © 2026 Hongru Zhao. Licensed under GPL-3.0-only. This repository is private during preparation.
