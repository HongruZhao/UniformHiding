# A2: mathematical justification of the imported Lean axiom

This is the expanded A2 comparison corresponding to manuscript Appendix A.2 and [the four-axiom audit](AXIOMS.md#a2). It explains why the cited results justify every clause accepted by Lean. The source-to-axiom justification is mathematical; it is not a separately formalized Lean proof.

<a id="a2-statement"></a>

## 1. Exact mathematical translation of the Lean axiom

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
\lambda(C)=1-\mathrm{eig}(I-C^*C),
\qquad
\Delta(\lambda)=\prod_{i\lt j}(\lambda_j-\lambda_i),
```

where $`\mathrm{eig}`$ uses a fixed ordering of the Hermitian eigenvalues, with the fixed reindexing used by the formalization. The coordinates of $`\lambda(C)`$ are the squared singular values as a multiset.  Put

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

## 2. Statement in the cited source

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

## 3. Difference from the source and its justification

The imported assertion includes the specific spectrum map's measurability on all square matrices, one constant before all tests, and arbitrary measurable targets.  The source supplies the geometric integration formula. The following deductions connect that formula to every imported clause. They are mathematical explanations of the bundled A2 input, not separate Lean proofs of those clauses.

*The selected spectrum is globally measurable.* For Hermitian matrices $`A,B`$, the min–max formula gives, for consistently ordered eigenvalues,

```math
\max_i|\mathrm{eig}_i(A)-\mathrm{eig}_i(B)|
\le \|A-B\|_{\mathrm{op}}.
```

The same bound holds after any fixed reindexing.  Since $`C^*C-D^*D=C^*(C-D)+(C-D)^*D`$, it follows for all $`C,D\in\mathcal M_N`$ that

```math
\max_i|\lambda_i(C)-\lambda_i(D)|
\le (\|C\|_{\mathrm{op}}+\|D\|_{\mathrm{op}})
\|C-D\|_{\mathrm{op}}.
```

Thus the exact selector used in A2 is continuous on all square matrices, including at spectral multiplicities.  Also, $`(UCU^{\mathsf{T}})^*(UCU^{\mathsf{T}})=\overline U(C^*C)U^{\mathsf{T}}`$ for unitary $`U`$, so its spectrum is unchanged by unitary congruence.  Every nonnegative Borel permutation invariant $`h`$ therefore gives a measurable invariant integrand $`C\mapsto h(\lambda(C))`$.  No choice of Takagi vectors is needed for this assertion.

*Regular coordinates and their uniqueness.* Let $`\mathcal S_N^{\mathrm{reg}}`$ consist of the symmetric matrices whose squared singular values are positive and pairwise distinct, and put

```math
\mathcal W=\{s\in\mathbb R^N:0\lt s_1\lt \cdots\lt s_N\},\qquad
H_N=\{\mathrm{diag}(\varepsilon_1,\ldots,\varepsilon_N):
\varepsilon_i\in\{-1,1\}\}.
```

The complement of $`\mathcal S_N^{\mathrm{reg}}`$ is flat null: it is the union of the zero sets of $`|\det C|^2`$ and the discriminant of the characteristic polynomial of $`C^*C`$.  Their restrictions to $`\mathcal S_N`$ are nonzero real polynomials, as a positive diagonal matrix with distinct entries shows.  For $`N=1`$ the collision condition is empty.

Takagi factorization makes the smooth map

```math
\Phi:(\mathrm U(N)/H_N)\times\mathcal W
\longrightarrow\mathcal S_N^{\mathrm{reg}},\qquad
\Phi([U],s)=U\mathrm{diag}(s)U^{\mathsf{T}},
```

surjective.  It is injective as well.  The ordered positive diagonal is fixed by the singular values.  If a unitary $`V`$ stabilizes $`D=\mathrm{diag}(s)`$, then $`VDV^{\mathsf{T}}=D`$ implies $`VD^2V^*=D^2`$.  Because $`D^2`$ has distinct diagonal entries, $`V`$ is diagonal; the first equality then gives $`V_{ii}^2=1`$.  Hence the stabilizer is exactly $`H_N`$, and the angular coordinate is unique modulo this group.

*The differential and the integration theorem.* At $`([I],s)`$, a real diagonal variation $`E`$ and a unitary tangent $`X^*=-X`$ give

```math
\,\mathrm{d} C=E+XD+DX^{\mathsf{T}}=E+XD-D\overline X.
```

For $`i\lt j`$, write $`X_{ij}=x_{ij}+\mathrm i y_{ij}`$.  The corresponding entry of the orbit tangent is $`(s_j-s_i)x_{ij}+\mathrm i(s_j+s_i)y_{ij}`$. Writing $`X_{ii}=\mathrm i t_i`$, the diagonal variation is $`E_{ii}+2\mathrm i s_i t_i`$.  These real coordinate blocks are all invertible on $`\mathcal W`$.  Thus $`\Phi`$ is a local diffeomorphism, and its bijectivity makes it a global diffeomorphism.  This proves the covering condition with one sheet; no further sign or permutation multiplicity is left in these coordinates.

Here is the precise specialization of the cited integration theorem. Take its integration manifold to be $`\mathcal S_N^{\mathrm{reg}}`$, its section to be $`\lbrace \mathrm{diag}(s):s\in\mathcal W\rbrace`$, its group to be $`\mathrm U(N)`$, and $`p=1`$.  The exceptional sets within these manifolds are empty, so $`X'=X`$ and $`Y'=Y`$ in the source's notation. The section is closed relative to $`\mathcal S_N^{\mathrm{reg}}`$: a limit there of positive ordered diagonals still has positive, distinct, ordered entries.  Its real diagonal tangent is orthogonal to the orbit tangent in the real Frobenius metric, and the displayed differential gives their direct sum.  The stabilizers equal the finite group $`H_N`$.  Thus orbit coverage, transversality, the isotropy dimension condition, orthogonality, and the covering condition all hold. The Frobenius volume is $`2^{N(N-1)/2}\,\mathrm{d} C`$, so $`\,\mathrm{d} C`$ itself is also invariant under unitary congruence.  Apply the theorem to Frobenius volume and divide both sides by this fixed factor to obtain the formula for $`\,\mathrm{d} C`$.

Give $`\mathrm U(N)/H_N`$ its invariant probability measure.  The same differential gives, with one constant $`a_N\in(0,\infty)`$ depending only on the fixed coordinate and angular normalizations, the radial Jacobian $`a_N\prod_i(2s_i)\prod_{i\lt j}(s_j^2-s_i^2)`$.  The constant is independent of $`s`$ by the displayed coordinate blocks, and independent of the angular point by unitary invariance.  The measurable form of the integration theorem therefore gives, for every nonnegative Borel permutation invariant $`h`$, including when the integrals are infinite,

```math
\int_{\mathcal S_N}h(\lambda(C))\,\,\mathrm{d} C
=a_N\int_{\mathcal W}h(s_1^2,\ldots,s_N^2)
\prod_i(2s_i)\prod_{i\lt j}(s_j^2-s_i^2)\,\,\mathrm{d} s.
```

The flat null set removed above does not affect this nonnegative integral.

*Squared coordinates and the common constant.* Set $`x_i=s_i^2`$ and $`\mathcal W_x=\lbrace x\in\mathbb R^N:0\lt x_1\lt \cdots\lt x_N\rbrace`$.  The factors $`2s_i`$ cancel exactly against the coordinate differentials:

```math
\prod_i(2s_i)\prod_{i\lt j}(s_j^2-s_i^2)\,\,\mathrm{d} s
=\Delta(x)\,\,\mathrm{d} x.
```

The positive orthant, except for its collision hyperplanes, is the disjoint union of $`N!`$ coordinate permutations of $`\mathcal W_x`$.  Permutation invariance of $`h`$, $`|\Delta|`$, and Lebesgue measure gives

```math
\int_{\mathcal S_N}h(\lambda(C))\,\,\mathrm{d} C
=a_N\int_{\mathcal W_x}h(x)\Delta(x)\,\,\mathrm{d} x
=\frac{a_N}{N!}\int_{(0,\infty)^N}h(x)|\Delta(x)|\,\,\mathrm{d} x.
```

Thus $`c_N=a_N/N!`$ is fixed before any choice of test or target. For an independent normalization check, insert $`h(x)=e^{-\sum_i x_i}`$. Since $`\mathrm{tr}(C^*C)=\sum_i|C_{ii}|^2+2\sum_{i\lt j}|C_{ij}|^2`$, this gives

```math
c_N=
\frac{2^{-N(N-1)/2}\pi^{N(N+1)/2}}
{\displaystyle\int_{(0,\infty)^N}
e^{-\sum_i x_i}|\Delta(x)|\,\,\mathrm{d} x}.
```

The denominator is positive on an open chamber and finite by polynomial growth and exponential decay.  For $`N=1`$ this reduces to $`c_1=\pi`$, as also follows directly from planar polar coordinates.

*Arbitrary measurable targets.* Finally, for any measurable $`B\subseteq\mathcal Y`$ take $`h(\lambda)=\mathbf{1}_{\lbrace F(\lambda)\in B\rbrace }`$ in the scalar integration formula. Measurability and permutation invariance of $`F`$ give the corresponding properties of $`h`$.  The resulting identity is equality of the two measures in Eq. (A.3) on every measurable $`B`$, which proves that equation for an arbitrary measurable target.  This completes the implication from the cited formula to every part of the stated A2.

<a id="a2-notation"></a>

## 4. Notation correspondence

FitzGerald and Warren's matrix $`X`$ is our $`C\in\mathcal S_N`$, their size $`n`$ is $`N`$, and their $`\lambda_i`$ are the eigenvalues of $`C^*C`$. Our vector $`\lambda(C)=1-\mathrm{eig}(I-C^*C)`$ contains this same multiset in a fixed order.  Their angular variables $`\Omega`$ become $`[U]\in\mathrm U(N)/H_N`$ with invariant probability measure in the calculation above.  Their proportionality constant becomes the single $`c_N=a_N/N!`$ when the ordered squared chamber is replaced by the full positive orthant.  In the An–Wang–Yan specialization, $`G=\mathrm U(N)`$, their $`K`$ is our $`H_N`$, $`X=\mathcal S_N^{\mathrm{reg}}`$, and $`Y`$ is the positive ordered diagonal section.  Their action is $`\sigma_g(C)=gCg^{\mathsf{T}}`$.  Their $`K`$ is a subgroup, whereas our $`K`$ elsewhere is an ambient dimension; their $`d`$ counts covering sheets, here one.

In the formalization, A2 is applied with A1 to permutation invariant tests of the determinant weighted COE law.  Its constant $`c_N`$ cancels under probability normalization.  The odds and trace power maps are subsequent constructions, not clauses imported in A2.  Permutation invariance is essential to the axiom: an unrestricted equality between one canonically ordered eigenvalue vector and a measure on the full unordered orthant would be false.

The unchanged declaration and structure are linked in [the declaration list](AXIOMS.md#declaration-locations). The remaining three literature axioms and the separate Route 2 comparison are documented in [AXIOMS.md](AXIOMS.md).
