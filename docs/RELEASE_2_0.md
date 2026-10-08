# Version 2.0

Version 2.0 is archived at [10.5281/zenodo.23250190](https://doi.org/10.5281/zenodo.23250190), released on 8 October 2026 in America/Chicago. This merge starts from the exact version 1.3.0 archive downloaded from [Zenodo record 22670050](https://zenodo.org/records/22670050). It integrates the full A1–A4 Lean formalizations from the author's `A1234HidingConsumer` workspace. The four scientific axiom assumptions are removed and replaced by proved theorem/data declarations preserving their original full contracts. The baseline's mathematical public statements and constants are preserved.

## Proved provider contracts

| Former input | Proof provider | Public provider declaration |
| --- | --- | --- |
| A1: principal COE corner law, including the boundary dimension | [A1/MatrixLawProof.lean](../A1/MatrixLawProof.lean) | `LogdetLean.GramHafnian.UltimateHiding.DenseScore.FriedmanMelloA1.A1_friedmanMello_matrixLaw` |
| A2: measurable Takagi–Weyl integration for arbitrary symmetric tests | [A2/WeylIntegrationProof.lean](../A2/WeylIntegrationProof.lean) | `LogdetLean.GramHafnian.UltimateHiding.DenseScore.A2_takagi_weyl_integration` |
| A3: squared GSVD beta-Jacobi law on the literal Gaussian pair carrier | [A3/Proposition12Proof.lean](../A3/Proposition12Proof.lean) | `LogdetLean.GramHafnian.UltimateHiding.DenseScore.A3_edelmanSutton_proposition_1_2` |
| A4: direct and inverse tensor moments of a supplied Wishart law | [A4/FullTheorem.lean](../A4/FullTheorem.lean) | `MatsumotoPaper.completedMatsumotoTheorem3` |

The existing consumer names are retained: `FriedmanMelloA1.matrixLaw_external`, `A2Prime_complexSymmetricTakagiWeyl_symmetricIntegration`, `A3_edelmanSutton_proposition_1_2`, and `MatsumotoPaper.A4_matsumoto_theorem_3`. The words `external`, `Conditional`, and `A2Prime` in historical names do not declare assumptions. The four interfaces now obtain their original contracts from these proof providers. A2 returns the integration-law data rather than only a proposition.

The integration changes the provider namespaces from the research workspace to the Zenodo core's `LocalAnticoncentration` namespace and connects the shared definitions through [AllFourIntegration/ProviderBase.lean](../AllFourIntegration/ProviderBase.lean) and [AllFourIntegration/TakagiDefinitions.lean](../AllFourIntegration/TakagiDefinitions.lean). The mathematical target contracts retain their full dimension ranges and original carriers.

## Uniform hiding and verification

`UniformHiding.theorem2_1` remains the all-input normalized matrix-law total-variation bound for every `1 ≤ N,K ≤ M`, with `C = 615172` and cap `min(1, C N²/M)`. Its unscaled form, quantitative Corollary 2.2, source-scale (S62) form and assembled Route 1 bounds are retained.

[HidingVerification.lean](../HidingVerification.lean) and [GBSHiding/CompletionAudit.lean](../GBSHiding/CompletionAudit.lean) require exactly `propext`, `Classical.choice`, and `Quot.sound` for every listed endpoint. [FinalHidingAudit.lean](../FinalHidingAudit.lean) checks all four provider contracts and the all-positive-input public statement. [FinalInventory.lean](../FinalInventory.lean) inventories transitive imported theorem dependencies. A source scan or an old receipt alone does not establish current kernel verification.

Run `python3 verify_final.py` from the repository root. Before invoking Lean/Lake or downloading dependencies, the verifier must confirm the actual mount of `/Volumes/Hongru‘s Second Brain` and keep all dependency caches, `.lake`, compilation outputs and temporary build directories in a project-specific directory under its `lean` folder. There is no internal-storage fallback. Lean and Mathlib pins are preserved.

The inherited [published Zenodo verification receipt](../verification/FINAL_VERIFICATION.json) records successful execution on 8 October 2026 in America/Chicago for that exact archived source tree. All three commands exited zero: the named public build and two separate Lean audits. The exact 18 provider/public endpoints passed; the inventory audited 19,639 imported local theorem declarations across 1,162 modules and 1,241 Lean source files, with zero scientific axioms and only the allowed three standard foundations. The build reused pinned dependencies and unaffected compiled-module caches; it was not wholly uncached or an independent checker run. The separate [fresh GitHub checkout recheck](../verification/GITHUB_V2_VERIFICATION.json) passed on 8 October 2026 at 23:34:55 UTC. The named public build completed 9,896 Lake jobs with exit zero; both separate Lean audits also exited zero. All 18 endpoints passed, and the inventory checked 19,639 imported local theorem declarations across 1,162 modules and 1,241 active Lean sources with zero scientific axioms and only the three standard foundations. Historical September receipts retain their original source-snapshot meaning. After the delivery manifest is frozen, fresh portable verifier runs preserve the captured delivery receipt and write new evidence under `verification/runs/<UTC run identifier>/`. A failed attempt is recorded there and exits with failure; an older delivery receipt does not certify a later failed run.

## Scientific scope

Removing A1–A4 as scientific axioms does not remove hypotheses from their theorem statements. A4 takes a supplied Wishart probability law satisfying the stated transform characterization. The hiding endpoints retain dimension and probability-family hypotheses. Route 1 retains the measurable amplitude's specified Haar marginal and the stated experiment and estimator hypotheses.

The optical squeezed-vacuum coefficients, passive tensor action and collision-free hafnian probability remain the adopted model. The source proofs do not claim to derive that full optical model from quantum dynamics.

Route 2 keeps `UniformHiding.routeTwoConditional` and its explicit symmetric-Gaussian comparison hypothesis. The Shou comparison and complete actual-law Route 2 assembly are not claimed as proved by this merge. The companion symmetric-Gaussian small-ball theorem remains available separately.

## Provenance and publication

The downloaded ZIP has MD5 `fc4cc50c6b78f8e39cacc10e0c353193` and SHA256 `cc04c945d593973eb514b7776f06fb8a42841a0d59b8fcd2dbd1aeb272c62458`, matching the official record checksum and size. It contains 1008 entries and 895 Lean sources, including the two equation supplements outside the 893-source core. A ZIP CRC check passed during acquisition; this is archive-integrity evidence.

The published Zenodo version 2.0 package preserves the original downloaded ZIP byte-for-byte. The preceding GitHub source, documentation, audit sources and verification records are preserved in [the version 1.3.0 GitHub snapshot](https://github.com/HongruZhao/UniformHiding/tree/9e44d98852a558f1495642cd841d06b5ba279a32) and Git history. The JSON files `COMPLETION_SOURCES.json`, `COROLLARY22_RELEASE.json`, `MODULE_RENAMING.json`, and `ANTICONCENTRATION_SNAPSHOT.json` document preceding snapshots and source correspondence; their fields named `current_sha256` refer to those historical stages. They are not manifests of this version 2.0 merge.

The published version 2.0 software archive is [10.5281/zenodo.23250190](https://doi.org/10.5281/zenodo.23250190). It supersedes the [version 1.3.0 baseline](https://doi.org/10.5281/zenodo.22670050). GitHub commit identity and the separate GitHub execution record distinguish the current checkout from inherited archive evidence.