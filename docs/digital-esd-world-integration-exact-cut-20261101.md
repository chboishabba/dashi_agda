# Digital-ESD world integration: exact cut (1 November 2026)

## Reconciled code owners

This branch is based on PR #1451 and incorporates the temporal owner from PR #1449. The canonical Digital-ESD umbrella imports both plus the thin `DigitalESDReviewedTemporalWorldJoinExact` interface. No new source/claim/evidence ontology is introduced.

The original `SourcePreservingRevision` from #1449 is retained for compatibility, **but its reflexive equalities do not prove a real revision**. The new `HistoricalRevisionDependency` demands an actual same-source equality and a strictly later time; the reviewed-temporal bridge requires both observations to be members of the supplied temporal world at the corresponding observer/time coordinates, and the exact source URL to match the source governed by `JointReviewHyperedge`.

`JointReviewHyperedge` in turn requires packet membership, full-text revision agreement, evidence span, same-source admitted-hyperfabric observation membership, claim-source equality and context-transfer evidence. Candidate-only records **do not** satisfy this.

## Not yet paid

| Obligation | Present evidence | Status |
|---|---|---|
| Both owners on one commit | This integration branch | Source-written |
| Cross-owner source and observation agreement | `ReviewedTemporalWorldJoin` record | Required, no canonical inhabitant |
| Nonreflexive historical source/time witness | `HistoricalRevisionDependency` | Required, no fabricated witness |
| Dependency-aware selective invalidation | Existing Alice temporal diagnosis owner | Not linked to concrete source revisions |
| Corpus census | Existing study-registry/SLR/database and audit owners | No complete joined source–claim–observation–edge census |
| Actual reviewed `JointReviewHyperedge` across EfS cases | #1451 dependent interface | Not populated |
| Same-object PG/SLR execution and human review | Independent runtime / reviewer evidence | Not demonstrated |
| Agda kernel check at exact head | No local compiler used here | Pending |

## Required next source-aware cuts

1. Derive a reproducible census from canonical source registries and SLR study ids, with study version, claims, analysis population, observations, evidence spans, world representation, review status and each join's exact proof owner.
2. Split **source-join missingness**, **intentional disagreement**, **context nontransferability**, **privacy exclusion** and **unexamined candidate** into distinguishable diagnostics. Do not force graph connectivity through seven-principle tags.
3. Connect concrete history dependencies to the already-owned selective invalidation/dynamic truth-maintenance machinery. The stronger revision witness is only source identity plus temporal advance, not full dependency closure.
4. Supply first real source-reviewed inhabitants from deeply reconstructed Alice / Digital-ESD pilot papers, then extend to new EfS sources. Do not invent full-text evidence.
5. Kernel-check the exact combined branch, run source-specific regressions and reconcile documentation-only #1452 and roadmap #1446.

**Epistemic boundary:** a reconciled branch and well-formed dependent record are not a reviewed, populated empirical world. Attribution remains attached to original authors and individual PR proof owners.


## 1 November 2026 — registry-derived K01 first cut

`DASHI/Education/DigitalESDWorldSourceCoverageCensusExact.agda` now derives one combined **25-row identity/claim-boundary census** from the exact nine-item `EducationCorpusSourceRegistry` and sixteen-item `DigitalESDEfSSourceCrossPollinationExact.canonicalSourceCases`. It proves the registry row lengths by `refl`, with no arbitrary title/URL duplicates and no claimed review promotion.

**Critical scope limit:** this 25-row ledger is only the Alice-plus-new-EfS slice; it is **not the complete Digital-ESD study-pilot universe** or the 43,996-record ERIC metadata universe. No claim/observation/span counts, graph-connected-component census, genuine reviewed `JointReviewHyperedge` inhabitant or temporal invalidation receipts are generated. The pre-existing `DigitalESDStudyProcessingCensusExact` is the separate metadata/stage ledger; it must be joined by exact identities to study/claim/world objects before calling K01 complete. The 25 rows carry `reviewNotAsserted`, not `unreviewed`: the census cannot infer absence or presence of source review from registries.

Compiler not executed; `refl` derivations are source-written, pending Agda kernel confirmation. This branch now has 25 owner-derived identity rows; the full world is still open.
