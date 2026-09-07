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

This version is prepared for private GitHub review and an unpublished Zenodo draft.
