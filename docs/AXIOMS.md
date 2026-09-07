# The four literature inputs and their exact boundary

Theorem 2.1 and the assembled Route 1 conclusions depend on four project declarations. Their proofs also use the three standard foundations `propext`, `Classical.choice`, and `Quot.sound`. This is conditional formal verification: the four mathematical inputs are not proved by Lean here. `HidingVerification.lean` checks the actual proof dependency closure rather than counting textual declarations.

## A1: COE principal-block law

**Declaration:** `LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1.matrixLaw_external` in [H5_FriedmanMelloA1External.lean](../LogdetLean/GramHafnian/UltimateHiding/DenseScore/H5_FriedmanMelloA1External.lean).

**Reference:** W. A. Friedman and P. A. Mello, *Marginal Distribution of an Arbitrary Square Submatrix of the S Matrix for Dyson's Measure*, Journal of Physics A 18 (1985), 425–436. [DOI](https://doi.org/10.1088/0305-4470/18/3/018), Eqs. (1.2), (3.7).

For Haar $U\in\mathrm U(n)$, the leading $m\times m$ block $s$ of $UU^T$, with $1\le m$ and $2m\le n$, has density proportional to

```math
 \mathbf 1_{I-s^*s\gt 0}\det(I-s^*s)^{(n-2m-1)/2}
```

against Lebesgue measure on independent complex-symmetric coordinates. Normalization is the reciprocal of the density integral, not an assumed Gamma-product formula. The source convention $U^TU$ and our $UU^T$ have the same Haar law. The axiom includes this convention translation. In the hiding proof, $n=K$ and $m=N$.

## A2: flat Takagi–Weyl integration

The documentation labels this second input **A2**. The existing Lean declaration and filename retain `A2Prime` for compatibility with the verified source tree.

**Declaration:** `LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration` in [H6_A2Prime_TakagiWeylSymmetricIntegration.lean](../LogdetLean/GramHafnian/UltimateHiding/DenseScore/Literature/H6_A2Prime_TakagiWeylSymmetricIntegration.lean).

**References:** S. Helgason, *Groups and Geometric Analysis*, AMS, 2000, Chapter I, Theorem 5.17 ([DOI](https://doi.org/10.1090/surv/083)); R. C. Chen, Y. H. Kim, J. D. Lichtman, S. J. Miller, S. Sweitzer and E. Winsor, *Spectral Statistics of Non-Hermitian Random Matrix Ensembles*, Random Matrices: Theory and Applications 8 (2019), 1950005, Appendix A.2, Eqs. (A.15), (A.16), (A.19), (A.20) ([DOI](https://doi.org/10.1142/S2010326319500059), [preprint](https://arxiv.org/abs/1803.08127)).

For complex-symmetric $C$, let $\lambda_i$ be its squared Takagi singular values. For every measurable permutation-invariant test $F$, the axiom asserts

```math
 (F\circ\lambda)_{\#}(dC)=c_N F_{\#}\!\left(
 \mathbf{1}_{\lambda_i\gt 0}\prod_{i\lt j}|\lambda_i-\lambda_j|\,d\lambda\right),
 \qquad 0\lt c_N\lt \infty.
```

It also supplies measurability of the spectral map. This is the type-CI tangent-space Weyl formula with coordinate normalization. The extension from continuous compactly supported invariant tests to arbitrary measurable invariant pushforwards is **included in the assumed contract**, not separately formalized. There is no assertion equating an ordered selector with an unordered vector law. See the source module for the precise data-valued structure.

## A3: Gaussian GSVD beta-Jacobi law

**Declaration:** `LogdetLean.GramHafnian.UltimateHiding.DenseScore.A3_edelmanSutton_proposition_1_2` in [H6_A3_EdelmanSuttonProp12Conditional.lean](../LogdetLean/GramHafnian/UltimateHiding/DenseScore/H6_A3_EdelmanSuttonProp12Conditional.lean).

**Reference:** A. Edelman and B. D. Sutton, *The Beta-Jacobi Matrix Model, the CS Decomposition, and Generalized Singular Value Problems*, Foundations of Computational Mathematics 8 (2008), 259–285, Definition 1.1 and Proposition 1.2. [DOI](https://doi.org/10.1007/s10208-006-0215-9), [author manuscript](https://math.mit.edu/~edelman/publications/beta-jacobi.pdf).

For $n\ge1$, nonnegative integer parameters $a,b$, and $\beta\in\lbrace 1,2\rbrace $, the squared generalized singular values of the specified independent Gaussian pair obey the beta-Jacobi law when tested by measurable permutation-invariant functions. Its density on $(0,1)^n$ is proportional to

```math
 \prod_i\lambda_i^{\beta(a+1)/2-1}(1-\lambda_i)^{\beta(b+1)/2-1}
 \prod_{i\lt j}|\lambda_i-\lambda_j|^\beta.
```

The hiding substitution is $n=N$, $a=1$, $b=K-2N$, $\beta=1$. Reflection, odds transformations, normalization adapters and project trace transport are proved downstream. The exact declaration keeps the source parameters, not an opaque final hiding estimate.

## A4: Wishart and inverse-Wishart tensor moments

**Declaration:** `MatsumotoPaper.A4_matsumoto_theorem_3` in [MatsumotoTheorem3External.lean](../LogdetLean/GramHafnian/UltimateHiding/DenseScore/MatsumotoTheorem3External.lean).

**Reference:** S. Matsumoto, *General Moments of the Inverse Real Wishart Distribution and Orthogonal Weingarten Functions*, Journal of Theoretical Probability 25 (2012), 798–822, Theorem 3; Eq. (4.10) and Lemma 5 fix the Weingarten convention. [DOI](https://doi.org/10.1007/s10959-011-0340-0), [preprint](https://arxiv.org/abs/1004.4717).

The axiom supplies the positive and inverse tensor-moment identities for $W_d(\beta,\sigma)$, arbitrary inserted matrices and matching permutations. The admissibility condition for moment order $q$ is

```math
 \gamma=\beta-(d+1)/2\gt q-1.
```

The hiding dictionary is $d=N$, $\beta=(K-N)/2$, hence $\gamma=(K-2N-1)/2$. The order-four use requires $K\ge2N+8$. In Matsumoto's convention the Laplace transform uses $\det(I-\sigma\theta)^{-\beta}$; standard real Gaussian samples give scale $2I$. The variance-$1/2$ Gaussian realization has scale $I$. Scale conversion and project contractions are separate proved lemmas. See the source for the full tensor expressions; the symbol $q$ here avoids confusing the source moment order with the paper's hafnian pair count.

## The additional Route 2 reference is not a Lean axiom

L. Shou, A. V. Gorshkov, V. Galitski and S. H. Miller, *Proof of the Hiding Conjecture for Gaussian Boson Sampling with an Arbitrary Number of Squeezed Input Modes* (2026), [arXiv:2608.19314, Theorem 1.1](https://arxiv.org/html/2608.19314v1), gives the symmetric-Gaussian hiding rate $O(N/\sqrt K)$. The formal Route 2 interface takes an explicit comparison premise. It does not assert the existence of a certified finite constant or prove that literature theorem. This is the fifth external input in the discussion; A2 itself has two supporting bibliographic references.

## Source-check status

The source modules retain the original parameter dictionaries and manuscript Appendix A explains the same translations. For this release, the author-hosted Edelman–Sutton manuscript and the Chen, Matsumoto and Shou preprints were accessed again. The Friedman–Mello and Helgason DOI links did not expose their full texts through the available retrieval tool; their pinpoint references are retained from the existing source documentation, not described as newly independently checked. In particular, A2 is an explicitly disclosed mathematical extension of its cited integration formula.
