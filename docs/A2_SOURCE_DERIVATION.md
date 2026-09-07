# A2: from the published Jacobian to the paper and Lean statement

This document records the mathematical implication used by manuscript Appendix A and the existing Lean input **A2**. The source is sufficient for the full contract after the deductions below. A2 remains an external input in Lean: these deductions are explained mathematically here, not separately formalized. The historical filename and declaration retain `A2Prime` for compatibility.

## Exact source locations

1. **W. FitzGerald and J. Warren**, *Point-to-line last passage percolation and the invariant measure of a system of reflecting Brownian motions*, Probability Theory and Related Fields **178** (2020), 121–171. [DOI](https://doi.org/10.1007/s00440-020-00972-z), [published PDF](https://link.springer.com/content/pdf/10.1007/s00440-020-00972-z.pdf). Section 6, printed **p. 165**, gives the unnumbered Jacobian immediately after **Eq. (70)**. It concerns a complex-symmetric matrix, Lebesgue measure on its independent complex entries, and the eigenvalues of its conjugate-transpose product. Its flat radial factor is

   ```math
   dC\ \propto\ \prod_{i\lt j}|\lambda_i-\lambda_j|\,d\lambda\,d\Omega.
   ```

   The factorization used there is the Takagi factorization, with diagonal entries equal to the square roots of the eigenvalues. The formula is a flat change of variables. The distinct Gaussian parameters appearing nearby concern the subsequent parameter-dependent density, and are not hypotheses of this geometric Jacobian. A2 uses no such parameters.

2. **J. An, Z. Wang and K. Yan**, *A generalization of random matrix ensemble I. General theory*, Pacific Journal of Mathematics **228** (2006), 1–17. [DOI](https://doi.org/10.2140/pjm.2006.228.1), [publisher PDF](https://msp.org/pjm/2006/228-1/pjm-v228-n1-p01-p.pdf). **Theorem 4.2**, Eqs. (4–4)–(4–5), and the immediately following remark on printed **p. 13** give the orbit integration theorem and explicitly permit measurable integrands. The specialization to unitary congruence is verified below.

The first reference supplies the exact complex-symmetric Jacobian. The second supplies a numbered integration theorem permitting measurable functions. Neither is described as a verbatim statement of a Lean structure.

## The shared paper and Lean contract

Let $N\ge1$. Give the complex-symmetric matrix space its Lebesgue measure in the independent entries $C_{ij}\in\mathbb C$, $i\le j$, and embed this measure in the space of all complex square matrices. Call the resulting measure $dC_{\mathrm{sym}}$. Define

```math
\lambda_i^L(C)=1-\mathrm{eig}_i(I-C^*C),
\qquad
\rho_N(d\lambda)=\mathbf{1}_{(0,\infty)^N}(\lambda)
\prod_{i\lt j}|\lambda_i-\lambda_j|\,d\lambda.
```

Here $\mathrm{eig}$ uses the fixed ordering and reindexing of Hermitian eigenvalues used by the code. The assertion is:

- $\lambda^L$ is measurable on **all** complex $N\times N$ matrices.
- There is **one** finite positive number $c_N$, chosen before the target and test, such that for any measurable space $Z$ and every measurable permutation-invariant map $F:\mathbb R^N\to Z$,

```math
(F\circ\lambda^L)_{\#}(dC_{\mathrm{sym}})
=c_N F_{\#}(\rho_N).
```

Permutation invariance means $F(\lambda\circ\pi)=F(\lambda)$ for every coordinate permutation $\pi$. It is required on the whole domain of $F$. The measures in this identity may have infinite mass. In Lean, the target is any measurable type at universe level `Type 0`.

## The flat scalar integration formula

Write a regular Takagi decomposition as $C=UDU^T$ with $D=\mathrm{diag}(s_1,\ldots,s_N)$, where the $s_i$ are distinct and positive. If $X^*=-X$ is a unitary tangent and $E$ is a real diagonal variation, then

```math
dC=E+XD+DX^T=E+XD-D\overline X.
```

For $i\lt j$, the real and imaginary parts of $X_{ij}$ have factors $s_j-s_i$ and $s_j+s_i$. Diagonal imaginary directions have factor $2s_i$, and diagonal real directions are the radial coordinates. Thus, up to angular normalization,

```math
\left(\prod_i2s_i\right)
\prod_{i\lt j}|s_i^2-s_j^2|\,\prod_i ds_i
=\prod_{i\lt j}|\lambda_i-\lambda_j|\,\prod_i d\lambda_i,
\qquad \lambda_i=s_i^2.
```

This is the squared-coordinate Jacobian in FitzGerald–Warren. It has Vandermonde power one and no extra individual power of $\lambda_i$.

For the measurable integration theorem, take $G=U(N)$ acting on $X=\mathrm{Sym}_N(\mathbb C)$ by $C\mapsto UCU^T$, with $Y$ the real diagonal matrices and common stabilizer the diagonal sign group. Remove zero or repeated squared singular values from $X$, and zero coordinates or repeated squared coordinates from $Y$. The omitted sets have Lebesgue measure zero: they are zero sets of the nonzero determinant and discriminant polynomials, with the repeated-value condition empty for $N=1$. Takagi factorization gives orbit coverage. The displayed differential gives transversality on the regular set. Both stabilizers have dimension zero, and diagonal radial directions are orthogonal to orbit directions in the real Frobenius metric. Its volume differs from independent-entry volume by a positive constant only.

The orbit map on the regular sets is a local diffeomorphism because the displayed Jacobian is nonzero. It is also proper: over a compact set of regular matrices the singular values remain bounded, bounded away from zero, and separated from each other, while $G/K$ is compact. Thus the inverse image is a closed subset of a compact set in the regular domain. A proper local diffeomorphism is a covering map. Each fiber has $2^N N!$ points: the real diagonal entries can have any signs and any ordering, and the remaining ambiguity is precisely the sign stabilizer. This proves the finite-covering hypothesis, rather than inferring it from fiber counting alone.

These facts verify the hypotheses of An–Wang–Yan, Theorem 4.2. Its measurable-integrand remark therefore applies. Restricting to positive diagonal coordinates and then writing $\lambda_i=s_i^2$ gives, for every nonnegative measurable permutation-invariant scalar function $h$,

```math
\int h(\lambda^L(C))\,dC_{\mathrm{sym}}
=c_N\int h(\lambda)\,\rho_N(d\lambda).
```

Infinite integrals are allowed. The unitary angular space is compact and has positive finite volume. Ordering and sign multiplicities change only the constant. These facts give one $c_N\in(0,\infty)$ depending only on $N$, not on $h$.

## From scalar tests to arbitrary measurable targets

Let $F:\mathbb R^N\to Z$ be measurable and permutation-invariant, and let $B$ be a measurable subset of $Z$. Then

```math
h_B(\lambda)=\mathbf{1}_{F^{-1}(B)}(\lambda)
```

is a nonnegative measurable permutation-invariant scalar function. The scalar identity applied to $h_B$ says exactly that

```math
(F\circ\lambda^L)_{\#}(dC_{\mathrm{sym}})(B)
=c_N F_{\#}(\rho_N)(B).
```

Equality on every measurable $B$ proves the full pushforward identity. This step requires no standard-Borel assumption on $Z$, no injectivity of $F$, and no finite-mass assumption. In particular, the positive constant does not depend on the target or test.

## The concrete spectrum map and its full domain

For every complex square matrix $C$, the matrix $I-C^*C$ is Hermitian. The map $C\mapsto I-C^*C$ is continuous. Ordered Hermitian eigenvalues are continuous, including at repeated eigenvalues; the subsequent fixed coordinate reindexing does not affect continuity. Hence the concrete map $\lambda^L$ is continuous, and therefore measurable, on the full matrix space required by Lean.

Its entries are the eigenvalues of $C^*C$ as a multiset. On the symmetric subspace these are the squared Takagi singular values. The scalar test and $F$ are permutation-invariant, so their values agree with any ordering used by the source. No measurable choice of Takagi vectors or eigenvectors is needed. The identity does **not** claim that a fixed ordered eigenvalue vector has density $\rho_N$ on the unordered orthant.

## Normalization and the one-dimensional case

The common constant can also be fixed by the symmetric test $h(\lambda)=e^{-\sum_i\lambda_i}$. Independent-entry integration gives

```math
c_N=
\frac{\pi^{N(N+1)/2}\,2^{-N(N-1)/2}}
{\displaystyle\int_{(0,\infty)^N}
 e^{-\sum_i\lambda_i}\prod_{i\lt j}|\lambda_i-\lambda_j|\,d\lambda}.
```

The denominator is positive because its integrand is positive on an open chamber, and finite by polynomial growth and exponential decay. The numerator follows from $\mathrm{tr}(C^*C)=\sum_i|C_{ii}|^2+2\sum_{i\lt j}|C_{ij}|^2$. For $N=1$, the empty Vandermonde is one and planar polar coordinates give $c_1=\pi$. This also checks the boundary case of the contract.

## Field-by-field correspondence and formal boundary

| Mathematical statement | Lean field or definition | Justification above |
| --- | --- | --- |
| Independent complex-symmetric entry volume | `complexSymmetricMatrixVolume` | Independent-entry measure embedded in all matrices |
| Concrete squared-spectrum vector | `canonicalGapSquaredSpectrum` | Ordered eigenvalues of the Hermitian gap, then subtraction from one |
| Flat positive-orthant Vandermonde measure | `takagiFlatEigenvalueRadialMeasure` | Published squared-coordinate Jacobian |
| One finite positive constant | `orbitConstant`, `orbitConstant_pos` | Compact angular volume; normalization check |
| Global spectral measurability | `measurable_spectrum` | Continuity on the entire square-matrix domain |
| All measurable invariant pushforwards | `symmetric_flat_radial_law` | Scalar measurable formula tested on inverse-image indicators |

The relevant contract and axiom are in [H6_A2Prime_TakagiWeylSymmetricIntegration.lean](../LogdetLean/GramHafnian/UltimateHiding/DenseScore/Literature/H6_A2Prime_TakagiWeylSymmetricIntegration.lean). The concrete selector is in [H6_CanonicalGapWeylReduction.lean](../LogdetLean/GramHafnian/UltimateHiding/DenseScore/H6_CanonicalGapWeylReduction.lean), and the measure definitions are in [H6_TakagiWeylAdapters.lean](../LogdetLean/GramHafnian/UltimateHiding/DenseScore/H6_TakagiWeylAdapters.lean).

The 2026-09-07 revision changes the citation and explains its implication. It changes no Lean declaration, definition, proof term, or project axiom count. The mathematical bridge is included in the external A2 assumption; a separate Lean proof of that bridge is not claimed.
