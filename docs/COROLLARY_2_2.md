# Theorem 2.1, Corollary 2.2, and the quantitative product-hiding conjecture

Version 1.2.0 states Theorem 2.1 for every positive row and input count that fits in the ambient matrix. The proof for the previously separated input range was already present in version 1.1.0. Corollary 2.2 is now the direct quantitative specialization of that stronger theorem. The companion proofs and the four literature axioms are unchanged.

## Theorem 2.1 in the manuscript

Let $`U`$ be Haar distributed in $`\mathrm U(M)`$. Write $`U_{N,K}`$ for the first $`N`$ rows and $`K`$ columns, and let $`G\in\mathbb C^{N\times K}`$ have independent circular complex Gaussian entries of variance one. For **every** $`1\le N\le M`$ and $`1\le K\le M`$,

```math
 d_{\mathrm{TV}}\!\left(\mathcal L(MU_{N,K}U_{N,K}^{T}),
                         \mathcal L(GG^{T})\right)
 \le \min\left\lbrace 1,615172\frac{N^2}{M}\right\rbrace .
```

The same statement holds after dividing both products by $`\sqrt K`$. Here $`T`$ means ordinary transpose, not conjugate transpose, and $`d_{\mathrm{TV}}=\sup_E|\mu(E)-\nu(E)|`$ is the probability convention. All dimensions are positive and the selected block fits in the ambient matrix; no totalized zero measure outside the allowed dimensions is used.

Corollary 2.2 takes $`n\ge1`$, $`N=2n\le M`$, $`1\le K\le M`$, $`\delta>0`$, and $`M\ge n^2/\delta`$. It immediately yields $`d_{\mathrm{TV}}\le4C_\ast\delta`$, where $`C_\ast=615172`$.

## The cited conjecture

The target is manuscript **[10, Conjecture 1 (Formal), Supplemental Eq. (S62)]**:

Adam Ehrenberg, Joseph T. Iosue, Abhinav Deshpande, Dominik Hangleiter, and Alexey V. Gorshkov, *Transition of Anticoncentration in Gaussian Boson Sampling*, Physical Review Letters **134**, 140601 (2025). [Published article](https://doi.org/10.1103/PhysRevLett.134.140601); [full preprint and supplement, Section S5](https://arxiv.org/html/2312.08433v2#S0.S5).

In the source, $`\mathcal D_U`$ is the law of $`V^TV`$ for the $`k\times2n`$ Haar block associated with a fixed collision-free pattern. The other law is $`\mathcal D_X=\mathcal L(X^TX)`$, with independent circular complex Gaussian entries of variance $`1/m`$ in $`X\in\mathbb C^{k\times2n}`$. The formal conjecture asks for $`d_{\mathrm{TV}}(\mathcal D_U,\mathcal D_X)=O(\delta)`$ for every $`1\le k\le m`$ and $`\delta>0`$ with $`m\ge n^2/\delta`$. The condition $`2n\le m`$ is implicit in a collision-free output pattern.

Our explicit constant is

```math
 d_{\mathrm{TV}}(\mathcal D_U,\mathcal D_X)
 \le 2460688\delta=4C_\ast\delta.
```

Thus Corollary 2.2 supplies the requested uniform quantitative rate in (S62). The parameter conversion below is part of the claim, since the source and the stored Lean laws initially use different scales.

## Notation and law correspondence

| Source | Hiding manuscript and Lean | Identification |
| --- | --- | --- |
| Ambient modes $`m`$ | $`M=m`$ | Same ambient dimension |
| Photon number $`2n`$ | $`N=2n`$ | Same selected dimension |
| Squeezed inputs $`k`$ | $`K=k`$ | All input counts, including $`k<2n`$ |
| $`k\times2n`$ Haar block $`V`$ | $`2n\times k`$ block $`U_{2n,k}`$ | $`V\overset{d}=U_{2n,k}^{T}`$ by Haar transposition and fixed permutations |
| Variance-$`1/m`$ factor $`X`$ | Standard factor $`G`$ | $`X=m^{-1/2}G^T`$ |
| $`V^TV`$ | $`U_{2n,k}U_{2n,k}^{T}`$ | Equal laws |
| $`X^TX`$ | $`m^{-1}GG^T`$ | Equal products after the stated substitution |

The last two laws are defined in Lean as `s62HaarProductLaw` and `s62GaussianProductLaw`. They are obtained by applying the measurable map $`A\mapsto m^{-1}A`$ to the stored laws of $`mUU^T`$ and $`GG^T`$. The two `eq_matrixLaw` theorems below prove the resulting literal matrix pushforward identities.

The explanation using the source's transposed Haar block, arbitrary fixed collision-free pattern, and rescaled Gaussian factor is a mathematical notation dictionary. The release does not add separate Lean theorems for Haar transposition invariance, permutation of the source's chosen pattern, or the entrywise variance transformation of that alternative Gaussian parametrization. Its public endpoint proves the exact bound for the explicitly defined product laws above. This distinction does not change the mathematical implication of the dictionary.

## The proof of the strengthened theorem and its immediate corollary

For $`N\le K`$, use the earlier dense and rectangular hiding proof. For $`K<N`$, the cap by one settles the case $`C_\ast N^2/M\ge1`$. In the remaining case $`M>C_\ast N^2>N+K`$, the rectangular comparison and the measurable transpose-Gram map give

```math
 d_{\mathrm{TV}}\!\left(\mathcal L(MUU^T),\mathcal L(GG^T)\right)
 \le\frac{(N+K)\sqrt{NK}}{M}
 \le\frac{2N^2}{M}
 \le C_\ast\frac{N^2}{M}.
```

This argument is the existing [all-input measure-law proof](../GBSHiding/AllInputs.lean). The public Theorem 2.1 now invokes this complete proof. In the manuscript, the same rectangular estimate is included in the theorem proof after its common trivial-range case; it is no longer deferred to Corollary 2.2.

For the quantitative specialization, positivity of $`\delta`$ gives $`n^2\le m\delta`$. Because $`m>0`$,

```math
 C_\ast\frac{(2n)^2}{m}\le4C_\ast\delta.
```

The inequality is proved over the reals in Lean. Applying the measurable scale map to both laws gives the source-scale conclusion. No limit argument, numerical sampling, or additional literature axiom is used for this specialization.

## Public declarations and verification

The public proof declarations are in [UniformHiding.lean](../UniformHiding.lean); proposition specifications and the source-scale law definitions are in [HidingStatement.lean](../HidingStatement.lean).

| Declaration in namespace `UniformHiding` | Content |
| --- | --- |
| `theorem2_1 : Theorem21` | Normalized bound for all $`1\le N,K\le M`$ |
| `theorem2_1_unscaled` | Equivalent all-input bound for $`MUU^T`$ and $`GG^T`$ |
| `corollary2_2 : Corollary22` | Immediate $`4C_\ast\delta`$ specialization at $`N=2n`$ |
| `corollary2_2_s62 : Corollary22S62` | Explicit bound on the source-scale product laws |
| `s62HaarProductLaw_eq_matrixLaw` | Identification with the literal Haar block product law |
| `s62GaussianProductLaw_eq_matrixLaw` | Identification with the literal scaled Gaussian product law |

[HidingVerification.lean](../HidingVerification.lean) checks the exact axiom sets of the theorem, corollary, and source-scale bound declarations. The earlier preparation names `corollary2_2_unscaled` and `corollary2_2_s62_scaled` remain as compatibility aliases of `theorem2_1_unscaled` and `corollary2_2`, respectively. Each uses the same four literature inputs A1–A4 and the foundations `propext`, `Classical.choice`, and `Quot.sound`. The two measure-identification lemmas use only foundations. Full citations and mathematical translations of the four imported assumptions remain in [AXIOMS.md](AXIOMS.md).

[Verification status](../verification/STATUS.md) records the new build, separate axiom audit, and source checks. [The paper comparison](PAPER_COMPARISON.md) retains the remaining coverage gaps, including the incomplete Proposition 4.1. A proof of that entire proposition is not part of this release.
