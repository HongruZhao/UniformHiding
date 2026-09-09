# Verification status

## Version 1.2.0: all-input Theorem 2.1 — 9 September 2026

**Passed.** A fresh public-target build and a separate execution of `HidingVerification.lean` both returned exit code zero. The three revised public modules compiled successfully. Theorem 2.1 now assumes only positive row and input counts within the ambient matrix; Corollary 2.2 is its direct quantitative specialization.

The exact dependency check passed for **12 selected public declarations**. Nine hiding and Route 1 declarations, including two compatibility aliases, use exactly the same four literature axioms plus `propext`, `Classical.choice`, and `Quot.sound`. The two companion main theorems and the conditional Route 2 deduction use only those three foundations. The two source-scale matrix-law identity lemmas also compiled with foundations only. No project axiom was added.

- The same public targets also compiled successfully in the actual GitHub Desktop clone: [clone build log](theorem21_github_clone_build.log).
- [Current build log](theorem21_all_inputs_build.log), [separate exact axiom audit](theorem21_all_inputs_axiom_audit.log), and [source-linked build receipt](theorem21_all_inputs_receipt.json).
- [Current source audit](source_audit.json): all 881 Lean sources, exactly four project axioms, no proof escape tokens, no missing local imports or cycles, and all modules reachable from the verification target.
- [Markdown source check](markdown_source_check.json): math delimiters, TeX grouping, equation-label conventions, and local links. This check does not by itself verify browser rendering.

Theorem 2.1 is `UniformHiding.theorem2_1`, with unnormalized form `theorem2_1_unscaled`. The public `corollary2_2` has the manuscript's quantitative statement; `corollary2_2_s62` gives the source-scale form. `corollary2_2_unscaled` and `corollary2_2_s62_scaled` retain names from the earlier preparation as compatibility aliases. The audit prints both proposition specifications and their proof declarations so the new dimension range is visible.

Exactly three Lean files differ from version 1.1.0. The other 878 Lean sources, including all 225 pinned companion sources, remain unchanged. [The semantic-change manifest](../docs/COROLLARY22_RELEASE.json) records the new source hashes and the verified preceding text; the historical renaming audit does not treat new proofs as naming changes.

The build reused pinned dependencies and unaffected compiled modules. It was a fresh build invocation, not a wholly uncached build or a separate independent kernel-checker run. The GitHub clone and Zenodo package contain the same verified Lean source bytes. Earlier `corollary22_*` receipts describe the preceding preparation, before the all-input statement was promoted to Theorem 2.1; the current receipt linked above supersedes them for the public endpoint map.

Proposition 4.1 remains partly formalized: its conditional sector-reference-mass theorem assumes the photon-sector identification. The complete maximizing-squeezing and uniform Stirling conclusions are not claimed. Route 2's hiding comparison remains unformalized. See [the component ledger](../docs/PAPER_COMPARISON.md#proposition-41-partial-coverage).

## Historical verification for version 1.1.0

The dated evidence below retains its original snapshot meaning. Statements that all Lean sources were unchanged concern those earlier documentation revisions.

## Markdown equation layout — 7 September 2026

**Passed.** The seven Markdown files contain 453 math expressions, including 55 display equations. The live GitHub check found no renderer errors, unsupported numbered rows, or horizontal overflow at the current browser width. All 12 corrected numbered displays and all nine README display equations were also inspected visually. [The layout receipt](markdown_layout_check.json) records the checks and their scope.

The earlier check counted rendered math elements but missed the vertical stacking caused by embedded equation numbers. Those 12 labels now appear as ordinary Markdown outside the math blocks, retaining the manuscript numbering. The formulas are preserved, and one previously plain-text subgroup variable is now inline math. [The portable Markdown audit](../scripts/markdown_audit.py) rejects the problematic label syntax and checks delimiters, grouping, and local links. Browser layout checks remain separate.

All 881 Lean sources are unchanged by this formatting correction. Lean was not rerun; the successful build and exact axiom audit from the naming revision below remain applicable.

## Journal-independent names and fresh Lean verification — 7 September 2026

**Passed.** After the module and identifier renaming, the pinned project build and a separate execution of `HidingVerification.lean` both returned exit code zero. All seven public endpoints matched their exact expected axiom sets: four hiding/Route 1 endpoints use the four literature axioms plus three foundations; the two companion endpoints and the conditional Route 2 deduction use only the three foundations. No project axiom was added.

- The same public targets also compiled successfully in the actual GitHub Desktop clone: [clone build log](theorem21_github_clone_build.log).
- [Current build log](module_naming_build.log) and [current endpoint audit](module_naming_axiom_audit.log) record these fresh executions.
- [Current build receipt](module_naming_build_receipt.json) records the source hashes, commands, toolchain, log hashes, and endpoint counts.
- [Naming and documentation checks](module_naming_checks.json) verify all 881 Lean sources against the exact naming rules, all local documentation links, and preservation of all 452 mathematical expressions. The audit was also tested against an altered proof and an invalid reverse edit; both were rejected.
- [Current source audit](source_audit.json) verifies the import graph, four project axiom declarations, absence of proof escape tokens, and exact restoration of all 225 companion files to their original upstream hashes. [Provenance](../docs/PROVENANCE.md) explains the reversible substitutions.

This is a fresh build invocation using the pinned dependency cache and unaffected local modules. Renamed modules and their affected dependents were rebuilt. Existing linter warnings remain; the build completed without errors. It is not a completely uncached build or an independent kernel-checker run. The mathematical statements and proofs are preserved under the recorded naming substitutions. Earlier receipts below retain their original snapshot meaning.

## Earlier Lean build and endpoint audit — 6 September 2026

**Passed.** The pinned project build completed successfully with 9,585 jobs. The new `UniformHiding` proof module and `HidingVerification` module were compiled during that successful build. A separate execution of the axiom audit also returned exit code zero.

| Endpoint | Exact proof dependency set |
| --- | --- |
| `UniformHiding.theorem2_1` | Four literature axioms + three foundations |
| `UniformHiding.routeOneSmallBall` | Four literature axioms + three foundations |
| `UniformHiding.theorem3_2_route1` | Four literature axioms + three foundations |
| `UniformHiding.theorem3_2_route1_optimized` | Four literature axioms + three foundations |
| `ComplexGramHafnians.theorem2_1` | Three foundations only |
| `ComplexGramHafnians.theorem2_3` | Three foundations only |
| `UniformHiding.routeTwoConditional` | Three foundations only; comparison and small-ball estimates remain explicit hypotheses |

The foundations are `propext`, `Classical.choice`, and `Quot.sound`. The four literature declarations, full citations and parameter dictionaries are in [AXIOMS.md](../docs/AXIOMS.md). The verification code fails if an expected dependency is missing or an unexpected dependency occurs.

## Evidence and reproduction

- [Public build log](public_build.log): `LEAN_NUM_THREADS=4 lake build`, exit 0.
- [Fresh axiom audit](axiom_audit.log): `LEAN_NUM_THREADS=4 lake env lean HidingVerification.lean`, exit 0; includes the exact sets and printed public theorem types.
- [Build receipt](build_receipt.json): commands, source hashes, log hashes and endpoint results.
- [Current source audit](source_audit.json): all 881 shipped Lean modules checked; exactly four project axiom declarations, no executable `sorry`, `admit`, `unsafe`, or `native_decide`, no missing local imports or import cycles. Following the naming revision, all 225 companion files match the pinned snapshot after reversing the recorded substitutions.
- [Markdown source check](markdown_source_check.json): local links, math fence pairing and brace escaping checked. This is separate from mathematical proof checking.

The build used pinned dependency caches and reused local modules already compiled during this release's build. The initial unrestricted build was interrupted because of resource pressure; work resumed with four threads. An addition-inequality call in the new Route 1 wrapper was corrected before the successful build. These logs do not claim a completely uncached build, an independent kernel checker run, or a PrimeGaps comparator run. Existing library linter warnings remain; there were no build errors in the successful run.

## Mathematical scope

### A2 citation revision — 7 September 2026

The A2 source attribution and its mathematical derivation were revised to match the manuscript and the existing Lean contract. See [the source-to-contract derivation](../docs/A2_SOURCE_DERIVATION.md). The only edited Lean file has comment changes; its source after removing comments is identical to the previously verified version. No definition, theorem statement, proof term, import, or axiom declaration changed, and the four-literature-input boundary is unchanged.

The revised A2 module was elaborated successfully with the pinned Lean toolchain and the existing dependency cache. The portable source audit was also rerun. [The dated revision receipt](A2_revision_receipt.json) distinguishes these new checks from the full-project build and endpoint axiom audit recorded on 6 September. The latter receipts remain evidence for that earlier build; no new full-project build or Lean proof of A2's mathematical source derivation is claimed.

### Appendix A documentation alignment — 7 September 2026

The README, the four-axiom audit, the expanded A2 justification, and the correspondence documents now match the rewritten Appendix A. Each axiom is translated mathematically before presenting the source statement, source-to-axiom justification, and notation dictionary. A3's all-sample measurability and A4's supplied-law premise and coefficient conversion are explicit.

At that documentation-only stage, all 881 Lean files were byte-identical to commit `d3ea171e4c328989507c7188279c363944df642b`, and all 225 companion files matched the pinned snapshot. That update checked documentation, mathematical correspondence, source identity, and the portable source audit; it did not rerun Lean or claim a separately formalized proof of any source-to-axiom justification. [The documentation receipt](axiom_documentation_revision.json) records those earlier checks. The later naming revision is separately verified and supersedes byte-for-byte identity claims for the current source tree.

Theorem 2.1 and Route 1 of Theorem 3.2, including the infimum over nonnegative physical additive thresholds, are conditional formal proofs relative to the four cited inputs. The companion endpoints add no scientific axioms. Route 2 hiding is not proved: its conditional deduction does not establish its comparison premise. See [PAPER_COMPARISON.md](../docs/PAPER_COMPARISON.md) for the optical model convention, Haar-marginal hypothesis and remaining coverage limits. A successful build is not a claim that every sentence of the manuscript is formally verified.
