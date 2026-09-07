# The four literature axioms used in the Lean formalization

This document explains **what Lean assumes and why the cited mathematical results justify those assumptions**. The same four-part structure appears in the revised manuscript's Appendix A (7 September 2026, pages 12–18). These results are imported rather than reproved inside Lean.

**Part 1 of each axiom is its exact mathematical translation into the paper's notation. It is neither Lean code nor a verbatim quotation from a publication.** Parts 2–4 give the source statement, the justification of differences, and the notation dictionary. Mathematical source-to-axiom arguments are distinguished from separately checked Lean deductions. There are four literature axioms; there is no A5 axiom.

All finite-dimensional spaces have their Borel structures. The notation $`f_{\#}\mu`$ means the pushforward measure. A permutation invariant test satisfies $`F(x\circ\pi)=F(x)`$ for every coordinate permutation $`\pi`$. Equation tags retain the manuscript's Appendix A numbering.

Theorem 2.1 and the assembled Route 1 conclusions use these four literature axioms together with `propext`, `Classical.choice`, and `Quot.sound`. [HidingVerification.lean](../HidingVerification.lean) checks the actual endpoint dependencies. The companion Gaussian anticoncentration endpoints use only the three foundations.

<a id="a1"></a>

## A1: COE principal block law

<a id="a1-statement"></a>

### 1. Exact mathematical translation of the Lean axiom

Let $`N,K`$ be integers with $`N\ge1`$ and $`2N\le K`$, and let $`h_K`$ be Haar probability measure on $`\mathrm U(K)`$.  Set

```math
C_{N,K}(U)=[UU^{\mathsf{T}}]_{1:N,1:N},\qquad
\mathcal S_N=\{C\in\mathbb C^{N\times N}:C^{\mathsf{T}}=C\},\qquad
\,\mathrm{d} C=\prod_{i\le j}\,\mathrm{d}\Re C_{ij}\,\,\mathrm{d}\Im C_{ij}.
```

Embed this coordinate measure in the full square-matrix space, supported on $`\mathcal S_N`$, and define

```math
w_{N,K}(C)=
\begin{cases}
\det(I_N-C^*C)^{(K-2N-1)/2},& I_N-C^*C\gt 0,\\
0,&\text{otherwise},
\end{cases}
\qquad Z_{N,K}=\int_{\mathcal S_N}w_{N,K}(C)\,\,\mathrm{d} C.
```

The imported law identity is

```math
(C_{N,K})_\#h_K
=Z_{N,K}^{-1}w_{N,K}(C)\,\,\mathrm{d} C.
\tag{A.1}
```

The right-hand side is defined by normalizing the raw measure by its own total mass.  No closed gamma or pi prefactor is part of the axiom, and no separate differentiability or moment conclusion is imported.  On the support, the determinant is positive and real, so its real power is exactly the weight used in the formalization.  The use of $`N,K`$ here is a renaming of the axiom's general block and ambient dimensions, not a restriction of its scope.

<a id="a1-source"></a>

### 2. Statement in the cited source

Friedman and Mello use $`U\in\mathrm U(n)`$ with Haar distribution and $`S=U^{\mathsf{T}}U`$ in Eq. (1.2).  For its leading $`m\times m`$ block $`s`$, their Eq. (3.7) writes the marginal, in redundant matrix coordinates, as

```math
p_0(s)\ \propto\ \delta(s-s^{\mathsf{T}})
[\det(I_m-s^\dagger s)]^{(n-2m-1)/2}.
```

The delta factor imposes complex symmetry.  The matrix-ball support comes from the corner construction and the derivation; it is not printed as a separate indicator in that display.  The stated range is $`m\le n/2`$; Appendix 1 explicitly includes $`n\ge2m`$.  Thus the endpoint $`n=2m`$, with exponent $`-1/2`$, is included [Friedman–Mello (1985), Eqs. (1.2), (3.7) and Appendix 1](https://doi.org/10.1088/0305-4470/18/3/018). The modern principal-corner density in Ref. [Shou–Miller–Galitski (2025), Theorem 2.1 and Eq. (2.1)](https://arxiv.org/abs/2508.00983) is corroboration, not an additional input in A1.

<a id="a1-justification"></a>

### 3. Difference from the source and its justification

There are two changes of representation.  First, the source has $`U^{\mathsf{T}}U`$, whereas the axiom has $`UU^{\mathsf{T}}`$.  Transposition preserves Haar probability: for fixed $`A\in\mathrm U(n)`$, $`AU^{\mathsf{T}}=(UA^{\mathsf{T}})^{\mathsf{T}}`$, so right invariance of the law of $`U`$ makes the law of $`U^{\mathsf{T}}`$ left invariant.  Haar uniqueness then gives $`U^{\mathsf{T}}\overset{\mathrm{d}}{=} U`$, and consequently $`U^{\mathsf{T}}U\overset{\mathrm{d}}{=} UU^{\mathsf{T}}`$.  Taking the same principal block preserves equality in law.  This is not a pointwise equality of the two products.

Second, the axiom uses independent symmetric coordinates and their embedding, rather than the source's redundant coordinates and symmetry delta.  Removing the redundant coordinates changes only a fixed volume factor, which disappears on normalization.  The source density therefore has exactly the support and exponent in Eq. (A.1), and its probability normalization gives $`0\lt Z_{N,K}\lt \infty`$.  These convention conversions are included in the imported law identity; no stronger regularity statement is being attributed to Friedman and Mello.

<a id="a1-notation"></a>

### 4. Notation correspondence

The dimension and matrix dictionary is

```math
n_{\mathrm{source}}=K,\qquad
m_{\mathrm{source}}=N,\qquad
s_{\mathrm{source}}\overset{\mathrm{d}}{=} C_{N,K}.
\tag{A.2}
```

The source's $`\dagger`$ is this paper's $`*`$; both mean conjugate transpose. Its $`S=U^{\mathsf{T}}U`$ corresponds in law to our $`UU^{\mathsf{T}}`$.  Its independent corner-entry volume becomes $`\,\mathrm{d} C`$, and its unspecified normalizer becomes $`Z_{N,K}^{-1}`$.  With this dictionary the imported Lean law is the density in Eq. (C.1).  Boundary regularity and score estimates are not part of A1.

<a id="a2"></a>

## A2: Flat Takagi and Weyl integration

<a id="a2-statement"></a>

### 1. Exact mathematical translation of the Lean axiom

For an integer $`N\ge1`$, use the Borel structures on Euclidean spaces and let

```math
\begin{aligned}
\mathcal M_N&=\mathbb{C}^{N\times N},\qquad
\mathcal S_N=\{C\in\mathcal M_N:C^{\mathsf{T}}=C\},\\
\,\mathrm{d} C&=\prod_{1\le i\le j\le N}
\,\mathrm{d}\Re C_{ij}\,\,\mathrm{d}\Im C_{ij}.
\end{aligned}
```

We regard $`\,\mathrm{d} C`$ as a measure on $`\mathcal M_N`$ supported on $`\mathcal S_N`$, by embedding these independent upper triangular coordinates as a symmetric matrix.  On all of $`\mathcal M_N`$ define

```math
\lambda(C)=1-\operatorname{eig}(I-C^*C),
\qquad
\Delta(\lambda)=\prod_{i\lt j}(\lambda_j-\lambda_i),
```

where $`\operatorname{eig}`$ uses a fixed ordering of the Hermitian eigenvalues, with the fixed reindexing used by the formalization. The coordinates of $`\lambda(C)`$ are the squared singular values as a multiset.  Put

```math
\rho_N(\,\mathrm{d}\lambda)=
\mathbf{1}_{(0,\infty)^N}(\lambda)\lvert \Delta(\lambda)\rvert\,\,\mathrm{d}\lambda.
```

Then $`\lambda:\mathcal M_N\to\mathbb R^N`$ is measurable, and there is *one* finite constant $`c_N\gt 0`$, depending only on $`N`$, such that for *every* measurable space $`\mathcal Y`$ and every measurable map $`F:\mathbb R^N\to\mathcal Y`$ satisfying $`F(\lambda\circ\pi)=F(\lambda)`$ for every $`\lambda\in\mathbb R^N`$ and every coordinate permutation $`\pi`$,

```math
(F\circ\lambda)_\#(\,\mathrm{d} C)=c_N F_\#\rho_N.
\tag{A.3}
```

The quantifier for $`c_N`$ precedes those for $`\mathcal Y`$ and $`F`$. No standard Borel assumption on $`\mathcal Y`$ or finite-mass assumption is needed.  These are exactly the data asserted by A2 in the formalization: a positive finite constant, measurability of the selected spectrum on all square matrices, and the displayed equality for arbitrary measurable permutation invariant tests.

<a id="a2-source"></a>

### 2. Statement in the cited source

FitzGerald and Warren display the flat Jacobian

```math
\,\mathrm{d} X\ \propto
\prod_{i\lt j}|\lambda_i-\lambda_j|\,\,\mathrm{d}\lambda\,\,\mathrm{d}\Omega
```

in Section 6, printed p. 165, immediately after Eq. (70) [FitzGerald–Warren (2020), Sec. 6, p. 165](https://doi.org/10.1007/s00440-020-00972-z). Their matrix is complex symmetric, their flat coordinates are its independent complex entries, and their $`\lambda_i`$ are the eigenvalues of $`X^*X`$. Thus the matrix space, coordinate volume, squared singular values, and Vandermonde power agree with those above.  We use this geometric Jacobian, not the subsequent density with Gaussian parameters.  The formula is unnumbered; Eq. (70) locates it but is not itself the Jacobian. For the general integration theorem and its measurable-integrand form we also use An, Wang, and Yan, Theorem 4.2 and its following remark, printed p. 13 [An–Wang–Yan (2006), Thm. 4.2 and following remark](https://doi.org/10.2140/pjm.2006.228.1). Their notation is $`G`$ for the group, $`X`$ for the integration manifold, $`Y`$ for its closed section, and $`K`$ for the section's common stabilizer. Write $`K_{\mathrm{AWY}}`$ for this subgroup to distinguish it from our ambient dimension.  Under their ensemble conditions (invariant measures, orbit coverage, transversality, isotropy dimension and orthogonality), and a finite $`d`$-sheeted covering $`G/K_{\mathrm{AWY}}\times Y'\to X'`$, their Eq. (4–4) states

```math
\int_X f(x)p(x)\,\,\mathrm{d} x
=\frac1d\int_Y
\left[\int_{G/K_{\mathrm{AWY}}}
f(\sigma_g(y))\,\,\mathrm{d}\mu([g])\right]\,\mathrm{d}\nu(y).
```

Here $`\sigma_g`$ is the action, $`p(x)\,\mathrm{d} x`$ is the invariant measure, and $`\,\mathrm{d}\nu`$ includes the section Jacobian.  The theorem states this for smooth nonnegative or integrable $`f`$; its following remark replaces smoothness by measurability, retaining nonnegativity or integrability. Neither source states the arbitrary-target pushforward identity in Eq. (A.3) verbatim.

<a id="a2-justification"></a>

### 3. Difference from the source and its justification

A2 imports three clauses beyond the geometric Jacobian's displayed form: measurability of the chosen spectrum on all square matrices, a single positive finite constant before the choice of test, and a pushforward identity into every measurable target.

The [full A2 justification](A2_SOURCE_DERIVATION.md#a2-justification) checks each clause:

- Ordered Hermitian eigenvalues are continuous. Applied to $`I-C^*C`$, with the fixed reindexing, this gives the exact selector's measurability on all matrices, including repeated eigenvalues.
- Positive ordered Takagi coordinates give a one-to-one smooth parametrization of regular symmetric matrices by $`(\mathrm U(N)/H_N)\times\lbrace 0\lt s_1\lt\cdots\lt s_N\rbrace`$, where $`H_N`$ is the diagonal sign group. The differential is invertible, so the integration map has one sheet. The excluded singular or collision set is flat null.
- The hypotheses of An–Wang–Yan's integration theorem are checked for this action. Frobenius volume is $`2^{N(N-1)/2}dC`$. The Jacobian in singular values is proportional to $`\prod_i(2s_i)\prod_{i\lt j}(s_j^2-s_i^2)`$, with a constant independent of the radial and angular points.
- Setting $`x_i=s_i^2`$ cancels the factors $`2s_i`$. Passing from the ordered chamber to the full orthant gives $`c_N=a_N/N!`$, with one positive finite constant independent of all tests. The Gaussian normalization gives $`c_1=\pi`$.
- For each measurable subset $`B`$ of the target, the scalar integration formula is applied to the indicator of $`F^{-1}(B)`$. This yields the exact arbitrary-target measure equality.

These are mathematical justifications of the assumption imported into Lean. They are not presented as a separate Lean proof of A2.

<a id="a2-notation"></a>

### 4. Notation correspondence

FitzGerald and Warren's matrix $`X`$ is our $`C\in\mathcal S_N`$, their size $`n`$ is $`N`$, and their $`\lambda_i`$ are the eigenvalues of $`C^*C`$. Our vector $`\lambda(C)=1-\operatorname{eig}(I-C^*C)`$ contains this same multiset in a fixed order.  Their angular variables $`\Omega`$ become $`[U]\in\mathrm U(N)/H_N`$ with invariant probability measure in the calculation above.  Their proportionality constant becomes the single $`c_N=a_N/N!`$ when the ordered squared chamber is replaced by the full positive orthant.  In the An–Wang–Yan specialization, $`G=\mathrm U(N)`$, their $`K`$ is our $`H_N`$, $`X=\mathcal S_N^{\mathrm{reg}}`$, and $`Y`$ is the positive ordered diagonal section.  Their action is $`\sigma_g(C)=gCg^{\mathsf{T}}`$.  Their $`K`$ is a subgroup, whereas our $`K`$ elsewhere is an ambient dimension; their $`d`$ counts covering sheets, here one.

In the formalization, A2 is applied with A1 to permutation invariant tests of the determinant weighted COE law.  Its constant $`c_N`$ cancels under probability normalization.  The odds and trace power maps are subsequent constructions, not clauses imported in A2.  Permutation invariance is essential to the axiom: an unrestricted equality between one canonically ordered eigenvalue vector and a measure on the full unordered orthant would be false.

<a id="a3"></a>

## A3: Gaussian GSVD beta Jacobi law

<a id="a3-statement"></a>

### 1. Exact mathematical translation of the Lean axiom

Let $`N\ge1`$, $`a,b\in\mathbb Z_{\ge0}`$, and $`\beta\in\lbrace 1,2\rbrace`$.  On the common sample space

```math
\Omega_{N,a,b}=\mathbb C^{(N+a)\times N}
\times\mathbb C^{(N+b)\times N},
```

let $`\mu_{N,a,b,\beta}`$ be the law of an independent pair $`(X_1,X_2)`$. For $`\beta=1`$ their entries are independent $`N(0,1)`$ variables embedded in $`\mathbb C`$; for $`\beta=2`$ they are independent $`(G_1+\mathrm iG_2)/\sqrt2`$, with $`G_1,G_2`$ independent $`N(0,1)`$. Define on every sample, including singular samples,

```math
A=X_1^*X_1,\quad B=X_2^*X_2,\quad R=(A+B)^{1/2},\quad
J=R^{-1}A(R^{-1})^*,\quad
x_i(X_1,X_2)=\bigl(\sqrt{\operatorname{eig}_i(J)}\bigr)^2.
```

Here the matrix square root is the positive semidefinite one, the inverse is the usual inverse on invertible matrices and the zero matrix on singular matrices, and the eigenvalues use the fixed ordering and reindexing of the formalization.  This inverse convention is not the Moore–Penrose inverse. The matrix $`J`$ is positive semidefinite, so $`x_i=\operatorname{eig}_i(J)`$.

Let $`\mathsf J_{N,a,b,\beta}`$ be the measure obtained by normalizing the following kernel by its own integral $`Z_{N,a,b,\beta}`$:

```math
\mathsf J_{N,a,b,\beta}(\,\mathrm{d} t)=
\frac{\mathbf{1}_{(0,1)^N}(t)}{Z_{N,a,b,\beta}}
\prod_{i=1}^N t_i^{\beta(a+1)/2-1}(1-t_i)^{\beta(b+1)/2-1}
\prod_{i\lt j}|t_i-t_j|^\beta\,\,\mathrm{d} t.
\tag{A.4}
```

The imported assertion has two conclusions: $`x:\Omega_{N,a,b}\to\mathbb R^N`$ is measurable on the whole sample space, and, for every measurable space $`\mathcal Y`$ and every measurable permutation invariant $`F:\mathbb R^N\to\mathcal Y`$,

```math
(F\circ x)_\#\mu_{N,a,b,\beta}=F_\#\mathsf J_{N,a,b,\beta}.
\tag{A.5}
```

Collision nullity, project parameter substitutions, and later trace laws are not additional conclusions of this axiom.

<a id="a3-source"></a>

### 2. Statement in the cited source

Edelman and Sutton's Definition 1.1 uses GSVD cosine coordinates $`c_i`$, the diagonal entries of a nonnegative diagonal matrix $`C_0`$ accompanied by $`S_0`$ with $`C_0^2+S_0^2=I_n`$.  The source explicitly notes that these coordinates are unique only up to reordering; its $`c_i`$ are not the ratios $`c_i/s_i`$ called generalized singular values in another convention. Proposition 1.2 states that independent Gaussian matrices $`N_1,N_2`$ of sizes $`(n+a)\times n`$ and $`(n+b)\times n`$, with the real or complex standard Gaussian conventions above, have squared GSVD coordinates $`\lbrace c_1^2,\ldots,c_n^2\rbrace`$ with the Jacobi law of parameters $`a,b`$ and $`\beta=1`$ or $`2`$, respectively [Edelman–Sutton (2008), Definition 1.1 and Proposition 1.2](https://doi.org/10.1007/s10208-006-0215-9). The source density is Eq. (A.4) with $`N=n`$. Its proof identifies the coordinates with the eigenvalues of

```math
(N_1^*N_1)(N_1^*N_1+N_2^*N_2)^{-1}.
```

The proposition does not specify our eigenvalue selector or its values and measurability on every singular sample, and it does not give an ordered vector the symmetric density on the entire cube.

<a id="a3-justification"></a>

### 3. Difference from the source and its justification

The additional interface content is the concrete coordinate map and its global measurability.  Each Gaussian matrix has full column rank almost surely: the determinant of its first $`N`$ rows is a nonzero polynomial, whose zero set has Gaussian measure zero.  On that event $`A,B\gt 0`$, and

```math
RJR^{-1}=A(A+B)^{-1},\qquad 0\lt J\lt I_N.
```

Thus the Hermitian matrix used in the axiom is similar to the source's matrix without any commutation assumption on $`A,B`$.  Its eigenvalues are the same squared GSVD coordinates.  The chosen values on the null singular set do not affect the probability law.

For measurability on all of $`\Omega_{N,a,b}`$, the Gram maps and the positive matrix square root are continuous.  Inversion extended by zero is Borel: it is the continuous rational map $`\operatorname{adj}(R)/\det R`$ on the open invertible set and is constant on its closed complement.  Hence $`J`$ is measurable.  Continuity of ordered Hermitian eigenvalues, fixed reindexing, and the real square root proves measurability of $`x`$.  Since $`J\ge0`$ on every sample, squaring its real square-root eigenvalues does not change them.

Finally, a permutation invariant $`F`$ has the same value on every ordering of the squared GSVD coordinates.  Apply the source's unordered law to the indicator of $`F^{-1}(D)`$ for each measurable $`D\subseteq\mathcal Y`$ to obtain Eq. (A.5).  This also covers arbitrary measurable targets.  These coordinate and measurability deductions explain the extension from Proposition 1.2; they are bundled into A3, not separately proved by that imported Lean declaration.  Collision nullity is then derived by the symmetric collision indicator and the null hyperplanes of the Jacobi density.

<a id="a3-notation"></a>

### 4. Notation correspondence

The source's $`n,N_1,N_2,c_i^2`$ correspond respectively to this subsection's $`N,X_1,X_2,x_i`$ up to ordering.  The Gaussian variances and the parameters $`a,b,\beta`$ are unchanged.  The formalization uses the specialization

```math
n_{\mathrm{source}}=N,\qquad a=1,\qquad
b=K-2N,\qquad\beta=1,\qquad K\ge2N.
\tag{A.6}
```

The two matrix sizes become $`(N+1)\times N`$ and $`(K-N)\times N`$; the two individual-coordinate exponents become $`0`$ and $`(K-2N-1)/2`$.  This is the radial kernel obtained from A1 and A2.  Reflection, odds transformation, and trace power maps give the beta prime trace law only after these inputs are combined.

<a id="a4"></a>

## A4: Wishart and inverse Wishart tensor moments

<a id="a4-statement"></a>

### 1. Exact mathematical translation of the Lean axiom

Let $`N,q\ge1`$, $`\beta,\gamma\in\mathbb R`$, and $`\sigma\in\operatorname{Sym}_N^+(\mathbb R)`$, with

```math
\gamma=\beta-\frac{N+1}{2},\qquad \gamma\gt q-1.
\tag{A.7}
```

Here $`q`$ is the moment order, and $`\beta`$ is the Wishart shape parameter, not the real or complex index in A3.  Let $`\mu`$ be a probability measure on $`\operatorname{Sym}_N^+(\mathbb R)`$ satisfying, for every real symmetric $`\theta`$ such that $`\sigma^{-1}-\theta\gt 0`$,

```math
\int e^{\operatorname{tr}(\theta w)}\,\mu(\,\mathrm{d} w)
=\det(I_N-\theta\sigma)^{-\beta}.
```

This supplied probability law and its transform identity are hypotheses of A4, through the definition of $`W\sim W_N(\beta,\sigma;\mathbb R)`$. The axiom does not separately assert existence of a law for arbitrary shape parameters.  Write $`\mathbb{E}_\mu`$ for integration against this law.

For arbitrary complex $`N\times N`$ matrices $`m_1,\ldots,m_q`$, a permutation $`g\in S_{2q}`$, and real symmetric $`w`$, define

```math
T_g(w;m)=\sum_{j_1,\ldots,j_{2q}=1}^N
\left(\prod_{r=1}^q(m_r)_{j_{2r-1},j_{2r}}\right)
\left(\prod_{r=1}^q w_{j_{g(2r-1)},j_{g(2r)}}\right).
\tag{A.8}
```

Let $`\mathcal M(2q)`$ be the perfect matchings of $`\lbrace 1,\ldots,2q\rbrace`$ and $`M_0=\lbrace \lbrace 1,2\rbrace ,\ldots,\lbrace 2q-1,2q\rbrace \rbrace`$.  Represent a matching $`M`$ by the permutation $`g_M`$ that lists each pair increasingly and lists the first members of pairs increasingly.  Let $`\ell(M,L)`$ count the connected components in $`M\cup L`$ and put $`\kappa(g)=\ell(M_0,gM_0)`$. The coefficient used in the axiom is defined by the finite matching matrix:

```math
G_z(M,L)=z^{\ell(M,L)},\qquad
\mathrm{Wg}^{\mathrm O}_{\mathrm L}(g;z)
=G_z^{-1}(M_0,gM_0),\qquad
\widetilde{\mathrm{Wg}}_{\mathrm L}(g;\gamma)
=(-1)^q2^q\mathrm{Wg}^{\mathrm O}_{\mathrm L}(g;-2\gamma).
```

The subscript $`\mathrm L`$ distinguishes this definition from the source's definition below.  The matrix inverse is the ordinary inverse at $`z=-2\gamma`$; its existence throughout the stated range is justified in part (3).  The imported conclusion is the conjunction

```math
\mathbb{E}_\mu T_g(W;m)
=2^{-q}\sum_{M\in\mathcal M(2q)}
(2\beta)^{\kappa(g^{-1}g_M)}T_{g_M}(\sigma;m),
\tag{A.9}
```



```math
\mathbb{E}_\mu T_g(W^{-1};m)
=\sum_{M\in\mathcal M(2q)}
\widetilde{\mathrm{Wg}}_{\mathrm L}(g^{-1}g_M;\gamma)
T_{g_M}(\sigma^{-1};m).
\tag{A.10}
```

These are equalities of complex integrals.  The declaration does not return separate integrability conclusions or any specialized trace or score bound.

<a id="a4-source"></a>

### 2. Statement in the cited source

Matsumoto's Theorem 3 takes $`W\sim W_d(\beta,\sigma;\mathbb R)`$, $`\gamma=\beta-(d+1)/2\gt n-1`$, arbitrary $`d\times d`$ matrices $`m_1,\ldots,m_n`$, and $`g\in S_{2n}`$.  It states

```math
\begin{aligned}
\mathbb{E} T_g(W;m)
&=2^{-n}\sum_{M\in\mathcal M(2n)}
(2\beta)^{\kappa(g^{-1}g_M)}T_{g_M}(\sigma;m),\\
\mathbb{E} T_g(W^{-1};m)
&=\sum_{M\in\mathcal M(2n)}
\widetilde{\mathrm{Wg}}_{\mathrm{src}}(g^{-1}g_M;\gamma)
T_{g_M}(\sigma^{-1};m).
\end{aligned}
```

These are the paired identities on printed p. 819 [Matsumoto (2012), Theorem 3](https://doi.org/10.1007/s10959-011-0340-0).  The source's Wishart convention is the Laplace-transform definition in its Section 1.1; when $`2\beta=p`$ is an integer its Gaussian realization is a sum of $`p`$ independent outer products with vector covariance $`\sigma/2`$.

The source defines its coefficient differently from part (1). Writing its moment order as $`q=n`$ for the next display, Eq. (4.10) gives

```math
\mathrm{Wg}^{\mathrm O}_{\mathrm{src}}(g;z)
=\frac{1}{(2q-1)!!}
\sum_{\nu\vdash q}
\frac{f^{2\nu}\omega^\nu(g)}{C_\nu(z)},\qquad
C_\nu(z)=\prod_{(i,j)\in\nu}(z+2j-i-1).
```

Here $`f^{2\nu}`$ is the irreducible character dimension for $`S_{2q}`$, $`H_q`$ is the stabilizer of $`M_0`$ with $`|H_q|=2^qq!`$, and $`\omega^\nu(g)=|H_q|^{-1}\sum_{h\in H_q}\chi^{2\nu}(gh)`$ is the normalized zonal spherical function.  The definition requires every $`C_\nu(z)\ne0`$.  Equation (5.2) sets $`\widetilde{\mathrm{Wg}}_{\mathrm{src}}(g;\gamma) =(-1)^q2^q\mathrm{Wg}^{\mathrm O}_{\mathrm{src}}(g;-2\gamma)`$ [Matsumoto (2012), Eqs. (4.10), (5.2)](https://doi.org/10.1007/s10959-011-0340-0).

<a id="a4-justification"></a>

### 3. Difference from the source and its justification

The tensor contractions and the two moment identities are the same after renaming $`d=N`$ and $`n=q`$.  There are two representation issues to check. First, the supplied probability measure in part (1) is identified with the source Wishart law by its Laplace transform on a neighborhood of zero in the real symmetric-matrix coordinates.  Uniqueness of such a transform therefore identifies the laws.  The gap condition implies $`\beta\gt (N+1)/2`$, so the source's singular Wishart regimes do not arise.

Second, the inverse-Gram coefficient must be identified with the zonal coefficient with its exact normalization.  For every box $`(i,j)`$ in a partition of $`q`$, $`j\le q`$ and $`i\ge1`$, so

```math
-2\gamma+2j-i-1\le-2\gamma+2q-2\lt 0.
```

Thus all the zonal denominators are nonzero at $`z=-2\gamma`$. Put $`Q_z(g)=z^{\kappa(g)}`$ and $`V_z(g)=\mathrm{Wg}^{\mathrm O}_{\mathrm{src}}(g;z)`$. Matsumoto's Lemma 5, with its normalized identity element $`|H_q|^{-1}\mathbf{1}_{H_q}`$, says for ordinary finite-group convolution that

```math
Q_z*V_z=|H_q|\mathbf{1}_{H_q}.
```

Evaluate at $`g_M^{-1}g_L`$ and sum over the cosets represented by $`g_P`$. The two functions are $`H_q`$-bi-invariant, so the group sum has a common factor $`|H_q|`$.  After dividing by that factor, the identity is exactly

```math
\sum_{P\in\mathcal M(2q)}
G_z(M,P)V_z(g_P^{-1}g_L)=\delta_{M,L}.
```

This constructs a right inverse of the finite square matrix $`G_z`$. Consequently $`G_z`$ is invertible and

```math
\mathrm{Wg}^{\mathrm O}_{\mathrm{src}}(g;z)
=G_z^{-1}(M_0,gM_0)
=\mathrm{Wg}^{\mathrm O}_{\mathrm L}(g;z).
```

The same factor $`(-1)^q2^q`$ then identifies the two modified coefficients. No additional factorial or sign is present [Matsumoto (2012), Eq. (4.10) and Lemma 5](https://doi.org/10.1007/s10959-011-0340-0).

This proves mathematical equivalence of the two definitions in the whole range used by A4.  The code defines the inverse-Gram coefficient directly and imports the moment equalities with it; it does not separately formalize the zonal expansion and this conversion.  Similarly, the source supplies finite moments in its stated range, but the imported integral equalities should not be read as separate Lean integrability assertions.

<a id="a4-notation"></a>

### 4. Notation correspondence

The source's matrix dimension $`d`$ is our $`N`$, and its moment order $`n`$ is our $`q`$.  This $`n`$ is unrelated to the half-photon count in $`N=2n`$ elsewhere in the paper.  The symbols $`\beta,\gamma,\sigma,m_r,g`$ keep their meanings; the source's $`\widetilde{\mathrm{Wg}}`$ equals $`\widetilde{\mathrm{Wg}}_{\mathrm L}`$ by part (3).  For the denominator Wishart calculation, the dictionary is

```math
d=N,\qquad n=q=4,\qquad k=K-N,\qquad
\beta=\frac{K-N}{2},\qquad\gamma=\frac{K-2N-1}{2}.
\tag{A.11}
```

The condition $`K\ge2N+8`$ gives $`\gamma\ge7/2\gt 3=q-1`$. Variance-$`1/2`$ Gaussian entries give source scale $`\sigma=I_N`$; variance-one entries give $`\sigma=2I_N`$.  The deterministic factor of two relates these Gram matrices.  Choosing the permutation and insertion matrices so that $`T_g(W^{-1};m)=\operatorname{tr}(W^{-4})`$ is a later specialization, followed by the matching sum, integrability closure, centering, and score estimates.  None of these specialized estimates is built into A4.

## Declaration locations

- **A1:** `FriedmanMelloA1.matrixLaw_external` in [H5_FriedmanMelloA1External.lean](../LogdetLean/GramHafnian/UltimateHiding/DenseScore/H5_FriedmanMelloA1External.lean#L97).
- **A2:** `A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration` and `TakagiWeylSymmetricIntegrationLaw` in [the A2 module](../LogdetLean/GramHafnian/UltimateHiding/DenseScore/Literature/H6_A2Prime_TakagiWeylSymmetricIntegration.lean#L88). The literature input is called **A2**; `A2Prime` survives only in historical code identifiers for compatibility.
- **A3:** `A3_edelmanSutton_proposition_1_2` and `EdelmanSuttonProposition12SymmetricContract` in [the A3 module](../LogdetLean/GramHafnian/UltimateHiding/DenseScore/H6_A3_EdelmanSuttonProp12Conditional.lean#L154).
- **A4:** `MatsumotoPaper.A4_matsumoto_theorem_3` in [MatsumotoTheorem3External.lean](../LogdetLean/GramHafnian/UltimateHiding/DenseScore/MatsumotoTheorem3External.lean#L254). Its supplied-law definition is in the same module.

## The additional Route 2 reference

[Shou, Gorshkov, Galitski and Miller (2026), Theorem 1.1](https://arxiv.org/html/2608.19314v1), supplies the asymptotic symmetric-Gaussian hiding rate $`O(N/\sqrt K)`$. The Route 2 interface takes a comparison estimate as a hypothesis; it does not formalize that literature theorem or fully assemble the actual symmetric-Gaussian Route 2. This additional literature result is **not a fifth Lean axiom**. A2 has two supporting references, so the number of bibliographic entries should not be confused with the number of axioms.

## Source and verification status

The 7 September 2026 documentation update aligns this file and the expanded A2 justification with the rewritten Appendix A. The declarations and all 881 Lean files are unchanged relative to commit `d3ea171e4c328989507c7188279c363944df642b`. No additional project axiom or separate formal proof of the source-to-axiom arguments is introduced. [The verification status](../verification/STATUS.md) distinguishes this documentation and source-identity check from the earlier Lean build and endpoint audit.

## Bibliographic details for A1–A4

- **A1:** W. A. Friedman and P. A. Mello, *Marginal Distribution of an Arbitrary Square Submatrix of the S Matrix for Dyson's Measure*, Journal of Physics A: Mathematical and General **18** (1985), 425–436. [DOI](https://doi.org/10.1088/0305-4470/18/3/018). Eqs. (1.2), (3.7) and Appendix 1.
- **A2, flat Jacobian:** W. FitzGerald and J. Warren, *Point-to-line last passage percolation and the invariant measure of a system of reflecting Brownian motions*, Probability Theory and Related Fields **178** (2020), 121–171. [DOI](https://doi.org/10.1007/s00440-020-00972-z). Section 6, printed p. 165, the unnumbered Jacobian immediately after Eq. (70).
- **A2, measurable integration:** J. An, Z. Wang and K. Yan, *A generalization of random matrix ensemble I. General theory*, Pacific Journal of Mathematics **228** (2006), 1–17. [DOI](https://doi.org/10.2140/pjm.2006.228.1); [publisher PDF](https://msp.org/pjm/2006/228-1/pjm-v228-n1-p01-p.pdf). Theorem 4.2, Eq. (4–4), and following remark, printed p. 13.
- **A3:** A. Edelman and B. D. Sutton, *The Beta-Jacobi Matrix Model, the CS Decomposition, and Generalized Singular Value Problems*, Foundations of Computational Mathematics **8** (2008), 259–285. [DOI](https://doi.org/10.1007/s10208-006-0215-9); [author manuscript](https://math.mit.edu/~edelman/publications/beta-jacobi.pdf). Definition 1.1 and Proposition 1.2.
- **A4:** S. Matsumoto, *General Moments of the Inverse Real Wishart Distribution and Orthogonal Weingarten Functions*, Journal of Theoretical Probability **25** (2012), 798–822. [DOI](https://doi.org/10.1007/s10959-011-0340-0); [preprint](https://arxiv.org/abs/1004.4717). Theorem 3, Eq. (4.10), Lemma 5 and Eq. (5.2).
