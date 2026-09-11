# Hiding-paper Lean verification — version 1.3.0

This folder contains version 1.3.0, prepared locally on 10 September 2026 from the completed proofs. Start with the [completion ledger](docs/FORMALIZATION_COMPLETION.md), which describes the new results and assumptions in mathematical language. The [paper correspondence](docs/PAPER_COMPARISON.md) covers the named manuscript results.

The public build and the 47-declaration exact axiom audit passed. There are four existing literature axioms and no new project axiom. Route 2 is excluded. The photon-sector calculations use the explicitly stated squeezed-input and passive-optics model.

To reproduce the checks, install Lean through elan, open this folder in a terminal, and run:

```sh
lake exe cache get
LEAN_NUM_THREADS=4 lake build UniformHiding HidingVerification
LEAN_NUM_THREADS=4 lake env lean HidingVerification.lean
LEAN_NUM_THREADS=4 lake env lean GBSHiding/CompletionAudit.lean
python3 scripts/source_audit.py
python3 scripts/markdown_audit.py
```

The toolchain and Mathlib revision are pinned in the included configuration files. Mathlib, Lean and compiled caches are obtained during setup; they are not bundled. The source archive includes the 893 Lean modules, the included companion sources, documentation, provenance manifests and execution records. It contains no manuscript PDF or LaTeX source and no Git or build cache.

The citation file identifies software version 1.3.0. Its Zenodo identifier is [10.5281/zenodo.22670050](https://doi.org/10.5281/zenodo.22670050). The Zenodo archive adds the Appendix E and current-paper equation supplements to this shared core. The [completion receipt](verification/completion_receipt.json) records the exact Lean source bytes checked; the [release record](verification/release_1_3_0_identity.json) connects them to the local release preparation.
