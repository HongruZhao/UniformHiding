# Verification status — 6 September 2026

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
- [Source audit](source_audit.json): all 881 shipped Lean modules checked; exactly four project axiom declarations, no executable `sorry`, `admit`, `unsafe`, or `native_decide`, no missing local imports or import cycles. All 225 vendored companion files match the pinned snapshot.
- [Markdown source check](markdown_source_check.json): local links, math fence pairing and brace escaping checked. This is separate from mathematical proof checking.

The build used pinned dependency caches and reused local modules already compiled during this release's build. The initial unrestricted build was interrupted because of resource pressure; work resumed with four threads. An addition-inequality call in the new Route 1 wrapper was corrected before the successful build. These logs do not claim a completely uncached build, an independent kernel checker run, or a PrimeGaps comparator run. Existing library linter warnings remain; there were no build errors in the successful run.

## Mathematical scope

Theorem 2.1 and Route 1 of Theorem 3.2, including the infimum over nonnegative physical additive thresholds, are conditional formal proofs relative to the four cited inputs. The companion endpoints add no scientific axioms. Route 2 hiding is not proved: its conditional deduction does not establish its comparison premise. See [PAPER_COMPARISON.md](../docs/PAPER_COMPARISON.md) for the optical model convention, Haar-marginal hypothesis and remaining coverage limits. A successful build is not a claim that every sentence of the manuscript is formally verified.
