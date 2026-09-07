# Changes in version 1.1.0

Compared with the published hiding archive version 1.0.0, which used the title *Uniform Hiding of Haar Block Transpose Gram Matrices*:

- Updates the manuscript title to *Uniform Hiding and Two Routes to Relative Accuracy in Gaussian Boson Sampling*.

- Adds a focused GitHub layout separating the main statement, public proofs, exact axiom check, and manuscript correspondence.
- Exposes Theorem 2.1 as `UniformHiding.theorem2_1`.
- Assembles the Route 1 physical-threshold bound in Theorem 3.2, its infimum, and the capped disk transfer using the companion repository's public Theorem 2.1.
- Pins an unchanged source dependency on ComplexGramHafnians commit `95ab10dc594ac92207054413220ae9fd2adab08c`.
- Documents all four literature axioms, their references and parameter translations. No new project axiom is introduced.
- Retains Route 2 as a conditional deduction, with Shou et al. (2026), Theorem 1.1 as an explicit unformalized input, not an added axiom.
- Defines the hafnian, the physical GBS probability, the two reference probabilities, and their ratio in GitHub-rendered mathematics.
- Separates historical equation coverage from the selected revised endpoints.
- Provides Lean sources and verification records without manuscript PDFs or LaTeX sources.

## A2 citation correction — 2026-09-07

- Replaces the A2 Helgason/Chen attribution with FitzGerald–Warren (2020), Section 6, p. 165, the flat Jacobian after Eq. (70), and An–Wang–Yan (2006), Theorem 4.2 and its measurable-integrand remark.
- Adds a complete source-to-contract derivation covering the independent complex-symmetric coordinates, squared singular values, one positive constant, arbitrary measurable invariant tests, and the globally measurable concrete spectrum selector.
- Aligns the manuscript and GitHub explanation of A2 with the existing Lean contract. No Lean declaration, definition, or proof term changes; no project axiom is added.

## Four-axiom documentation alignment — 2026-09-07

- Rewrites the axiom documentation to match Appendix A: exact mathematical translation from Lean, source statement, justification of differences, and notation correspondence for each of A1–A4.
- States A3's full coordinate map and global measurability, including the convention on singular samples.
- Separates A4's supplied Wishart-law hypothesis from its two moment conclusions and explains the exact inverse-Gram/zonal Weingarten conversion.
- Expands the A2 justification with a one-sheeted positive ordered Takagi parametrization, explicit volume and chamber factors, and a dictionary using the integration theorem's original notation.
- Keeps exactly four literature axioms. No Lean source file, theorem statement, or proof term changes in this documentation alignment.
- Uses the stable [version 1.1.0 archive DOI](https://doi.org/10.5281/zenodo.22558885) and removes temporary preparation-status wording.
