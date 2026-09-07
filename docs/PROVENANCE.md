# Provenance and dependency

This release reorganizes the author's local `GBS_Hiding_Two_Routes_Lean` development into public manuscript endpoints. Historical namespace names such as `PRXQ` and `PRL` are retained for source compatibility; they do not describe the submission status.

The source dependency on [ComplexGramHafnians](https://github.com/HongruZhao/ComplexGramHafnians) is pinned to commit `95ab10dc594ac92207054413220ae9fd2adab08c`. All 223 `LogdetLean` files of that repository and its `Challenge.lean` and `ComplexGramHafnians.lean` are included byte-for-byte. Their hashes are recorded in [ANTICONCENTRATION_SNAPSHOT.json](ANTICONCENTRATION_SNAPSHOT.json). The shared source tree avoids compiling duplicate declarations. The companion `Challenge.lean` contains proposition specifications, not proof placeholders. Our own statement file is named `HidingStatement.lean` to avoid a module-name collision.

One shared hiding file, `CurrentPRL/CoefficientPaperEndpoints.lean`, previously appended three unused compatibility results. This release uses the exact companion version without those additions; no imported companion proof is changed. The source audit checks the pinned snapshot hashes on every run. Updates to the companion are explicit source updates, not automatic pulls.

The new Route 1 proof imports `ComplexGramHafnians` and calls its public `theorem2_1`. Source vendoring is used for reproducibility while both repositories are private. This is not a separate Lake git dependency or submodule.

The independent statement/proof/check organization is inspired by [PrimeGaps186](https://github.com/openai/PrimeGaps186). We do not claim its comparator or independent kernel-checker runs. The build log and axiom report state exactly what was executed for this release.
