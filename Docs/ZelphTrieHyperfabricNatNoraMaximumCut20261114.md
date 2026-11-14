# Zelph ↔ trie / ultrametric ↔ indexed hyperfabric ↔ Nat/NORA — exact maximum-cut

**Date:** 2026-11-14. **Golden authority:** DASHI/Agda. **Production:** SLR Rust/PostgreSQL. **MCP / external graph routing:** ITIR-suite / Zelph. **Historical reference:** SensibLaw Python. **External NORA authorship:** Éder Porto. **No new parallel index, review store, scheduler or proof system.**

**Source state:** This is an exact-lemma/phase roadmap grounded in existing Agda declarations and a user-supplied local HF execution report. It is **not** an Agda kernel proof of new original theorems, not a re-execution of the raw HF receipt, and not SLR PostgreSQL acceptance.

## 0. Executive max-cut

**Solved/credited in previous work (as specifically qualified):**

- Golden typed theory exists for balanced-ternary prefix agreement, residual-carrying coarse trie projections, indexed relational hyperfabric, guarded gluing, query-indexed factorization, collision-driven failure of projection adequacy, typed N-dimensional Nat admissibility, separate native Wikibase vs Zelph graph planes, partial-graph no-negation, and physical-transport no-authority.
- On the ITIR PR #14 branch the user reports live HF `nodeOfName` Cap'n Proto decoding for **all five** Nat QIDs, 21 targeted tests passing, and a content-addressed filtered route receipt. Reported full graph SHA `0d4bd670959ebddae72f70d973410fdea8917ec1`; full manifest digest `cedd5cf0e4951ae1aa7c2c5968614b0eb72a4c3b5c8b2dc4ab18c40be8c83f59`. Exact mapping: `Q10403939 → 24721153, chunk 1`; `Q10416948 → 874016, chunk 1`; `Q10422059 → 63706277, chunk 1`; `Q10651551 → 2475334, chunk 4`; `Q56404383 → 741397, chunk 75`. Raw run artifacts are **not present in GitHub** and were not independently rehashed in this audit.
- The published HF layout reportedly has numeric `manifestVersion: 2`, `storageMode: split-by-direction-and-section`, and **no advertised `hfObjects.nodeRouteIndex`**. The strict sidecar-only MCP route correctly refused a fake exact route. A *separate* decoder scanned actual name shards. ITIR PR #14 added a narrowly typed manifest ABI correction; new tests are source-written, not post-patch executed.
- The ordinary Zelph graph supplies entity-to-entity relation context, **not** native quantitative/time/qualifier/reference bundles for `P14143`. Five identified QIDs are not the 57,989 historical `P5991` statements.

**True next cut:** (1) raw source identity and reproducible physical route; (2) an exact *complete-for-query* shard index under explicit scope; (3) direct adjacency and physical cost; (4) transport to native SLR evidence/review; (5) Agda kernel-checked same-object runtime witness; (6) real NORA export and Nat source support. These are separate gates and can be executed as a single coordinated tranche with one PR per repo.

## 1. Existing Agda owners — no duplicate generic structures

| Mathematical concern | Actual golden module | What it already gives | What it **does not** prove |
|---|---|---|---|
| Balanced-ternary address and finite prefix geometry | [`DASHI/Foundations/BalancedTernaryUltrametricExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Foundations/BalancedTernaryUltrametricExact.agda), [`Base369PrefixUltrametricExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Foundations/Base369PrefixUltrametricExact.agda) | `PrefixAgreement`, reflexive/symmetric/transitive/weakening, depth-limited prefix ball; no need to invent another ultrametric | An HF shard is **not** known to be a prefix ball, nor does `Q...` string order automatically share the internal node ordering |
| Information-preserving trie fallback | [`BalancedTernaryResidualTreeExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Foundations/BalancedTernaryResidualTreeExact.agda) | Coarse visible ancestor retains local components and residual; a fallback need not erase fine state | An unresolved route does not yield a valid complete negative result, nor a unique source witness |
| Indexed relational fibre and descent | [`IndexedRelationalHyperfabricSpineExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Core/IndexedRelationalHyperfabricSpineExact.agda) | `IndexedFabric`, `Address B k`, `ConsumerSufficient`, `ConsumerCollision`, `GuardedGluing` | Section overlap, exact shard-to-address mapping and a real code-level gluing witness |
| Observer and query-specific adequacy | [`QueryIndexedProjectionAdequacyExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Core/QueryIndexedProjectionAdequacyExact.agda) | `AdequateFor`, `QueryAdequacyDefect`, `queryAdequacyDefectBlocksFactorisation` | One common coarse index being adequate for **all** name, adjacency, qualifier, historical or negative-answer queries |
| Typed relational gluing with provenance | [`TypedHyperfabricCore.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Reasoning/TypedHyperfabricCore.agda) | Vertex/edge stalks, incidence, restriction, compatible `GlobalSection`, `HyperfabricObstruction` | Every local HF chunk produces one globally compatible graph view |
| Nat's nine-axis balanced admissibility | [`SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Interop/SensibLawWikidataBalancedTernaryAdmissibilityHyperfabricExact.agda) | Separates balanced truth, Wikibase `novalue/somevalue/value`, `rejected/open/admitted`; `NatNineAxisState` and `toBase369NineTrits` | A shard miss can be reinterpreted as `novalue`, or a name match can pay source or migration authority |
| Graph coverage | [`ZelphBoundedGraphCoverageExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Interop/ZelphBoundedGraphCoverageExact.agda) | Transport `complete/partial/failed` vs query coverage `complete/incomplete/uninspected/invalid`; incomplete/uninspected abstention | A fetched node/name shard establishes complete query-family coverage |
| Compiler/pruned preservation | [`ZelphPrunedArtifactQueryPreservationExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Interop/ZelphPrunedArtifactQueryPreservationExact.agda) | Monotone soundness and scope-specific preservation receipts, not blanket source/pruned equivalence | Source absence from a pruned or partially fetched artifact |
| Two independent evidence planes | [`SensibLawWikibaseZelphItemSurfaceExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Interop/SensibLawWikibaseZelphItemSurfaceExact.agda), [`SensibLawNatZelphPipelineExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Interop/SensibLawNatZelphPipelineExact.agda) | Native QID/GUID/rank/qualifier/reference vs bounded graph adjacency; no forced equivalence or migration | A routed `P31/P279` graph observation as native `P14143` statement |
| Physical scheduler | [`SLRGWBPhysicalObjectAcquisitionPolicyExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Interop/SLRGWBPhysicalObjectAcquisitionPolicyExact.agda) | Physical object resolution, coalescing before concurrency, bounded width and route→transport firewall | Current runtime source, cache and actual measured GETs complying with that contract |
| Cross-language five-choice review | [NORA review PR #1506](https://github.com/chboishabba/dashi_agda/pull/1506) | `SituatedNORAReview`, `ambiguousCannotFactorThroughSupport`, consumer-relative `valid/invalid` | A live NORA native export or SLR production review round trip |
| Shared union vs projection payments | [`SensibLawSharedAcquisitionExecutionExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Wikimedia/SensibLawSharedAcquisitionExecutionExact.agda) | Shared union-QID acquisition doesn't pay each downstream source obligation | A five-QID transport receipt being all 57 source-support or 57,989 population receipts |
| Stable typed publication and external identity | [`WikimediaWorldBucketPublicationExact.agda`](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Interop/WikimediaWorldBucketPublicationExact.agda), [xPollenation/CID existing store note](https://github.com/chboishabba/dashi_agda/blob/master/Docs/support/reference/XPollenationCIDWeld20261017.md) | Source/revision/edge/CID coordinate separation; CIDs never create authority | A downloaded chunk becoming an automatically admitted graph statement |

**Important mathematical discrimination:** `PrefixAgreement` is a *domain/carrier theorem*. For transport to use it we need a concrete encoding of a key into a prefix address **and** a verified inverse/coverage map from that address to physical shards. Sorted `nodeOfName` Cap'n Proto streams could permit interval search, but sortedness and interval coverage must be established from emitted metadata or verified decoded contents. Never call the current 204-section-shard layout a balanced-ternary trie without this bridge.

**Hyperformalism is richer than flattened triples:** A graph edge alone can lose versioned provenance, incidence, rank/qualifier, temporality and observer-relative residuals; the correct data product is a situated fibre/edge with source-hash and restricted query family. A source‑revision‑indexed hyperfabric can represent these without needing a second graph backend.

## 2. Exact new mathematical lemmas (not generic welds)

These are **proposed exact declaration names** and specifications, NOT existing proved declarations. The file owner for new proof code should be DASHI on the existing NORA/ontology Agda rollup PR #1506; reuse all modules in §1.

### A — Original nontrivial mathematics / genuinely new proof obligations

**A1 `zelphPhysicalNameShardPartitionExact`**: Under a verified sorted, nonoverlapping and covering index over **all** `nodeOfName` entries for a fixed language and graph revision, prove every existing key is routed to precisely the shard(s) containing it. Explicitly represent duplicate-name and collision policy; if key uniqueness is not guaranteed, return a finite set of witnesses rather than a fake singleton. Requires physical bridge data; no global claim without full index coverage.

**A2 `zelphBoundedShardQueryFamilyCompleteness`**: For a specified query family `F`, a decoded shard set `S`, the original graph `G` and the declared source graph revision, prove `∀ q ∈ F, answer(G,q) ≡ answer(restrict(G,S),q)` under a *certified edge-closure/partition witness*. Must produce a counterexample without the closure witness. This is the central original theorem that separates physical route completeness from just a positive hit.

**A3 `zelphHyperformalShardGluingSound`**: Given a shared-identity graph revision, pairwise compatible restriction maps and explicit overlap equality on a cover, construct a unique or suitably equivalent global section of the *situated* hyperfabric carrying `QID / edge / source / revision / qualifier / temporal / review` fibres, **only where gluing hypotheses hold**. Test with a deliberate conflicting-overlap counterexample.

**A4 `zelphPrefixQuotientQueryAdequacyIff`**: For a concrete prefix/range projection `p` and chosen query family, establish the exact criterion `AdequateFor(p,q)` (fine query answers constant on projection fibres). Produce a concrete collision witness for name-only projection queried about a native `P14143` quantity or a `P854` source. This ties physical shard refinement to existing `QueryIndexedProjectionAdequacyExact`, not a new projection logic.

**A5 `zelphRevisionRefinementTransportCoherent`**: For old/new graph revisions and changed physical shard routing, show which unchanged typed fibres and proof receipts transport and which dependencies must reopen; require an explicit revision correspondence and source/graph identity. Internal Zelph node IDs, chunks and prefix boundaries cannot silently be transported between regenerated graphs.

**A6 `zelphQueryScopedNegativeCompletenessIff`**: A negative answer may be returned only if (i) all relevant query-family input partitions/edge families were inspected for the same revision, (ii) the query evaluator is sound and complete *for those families*, and (iii) the source graph has the advertised closed-world scope. Otherwise return unresolved/incomplete. This is not closed-world truth about all Wikidata.

### B — Math-to-runtime adapters / executable exact contracts (important, but not original theorems)

**B1 `hfManifestShardIdentityPreserved`**: Numeric published `manifestVersion=2` / `storageMode=split-by-direction-and-section` normalises to `zelph-hf-layout/v2` **without changing** object paths, section-global chunk identity, source revision or digest; unsupported layouts reject. Bind the **real** emitted schema and test same-object bytes.

**B2 `hfSelectedShardDecodePreservesKeyNode`**: For the real packed `NodeNameChunk` parser, prove decoded `(lang,QID,nodeId)` corresponds to bytes from one manifest-declared selected object and that no sequential full-bin fallback is silently counted as direct fetch. Requires a trusted decoder model and runtime test receipt; do not claim Agda verifies the C++ implementation without a refinement check.

**B3 `natFiveQidsExactRouteReplays`**: Bind the five reported QIDs, numeric node IDs, chunk indices, actual byte digests and producer/version identities to a checked witness; reject altered byte, mixed dataset SHA, duplicate/missing QID, or wrong language.

**B4 `hfPhysicalRequestDedupeAndBudgetExact`**: Normalise logical QID/selector requests to selected **physical object identities**, dedupe/coalesce, enforce ≤5 simultaneous cold physical fetches, account for actual transferred bytes, forbid cache hit→network IO, and expose bounded/truncated results separately.

**B5 `zelphGraphNativeStatementJoinIsEvidenceOnly`**: Construct a source/revision-bounded join of Zelph graph observations with native Wikibase GUID/snaks/rank/qualifiers/references, preserving both evidence planes and requiring source+scope correspondence. Graph adjacency alone never instantiates a native quantitative measurement, period or P854 proposition.

**B6 `natZelphNoraReviewReplaySameSource`**: Native SLR source-unit/physical shard/statement/S29 reviewer state and ITIR MCP source/review/receipt composition share the *same* source revision, QID, GUID, subject/consumer and digest; reopening after changes is dependency-scoped and preserves rejected/held alternatives.

### C — Physical, empirical or external acceptance, not provable from mathematical carriers alone

**C1** Obtain and retain raw request, manifest, route JSON and packaged receipt bytes for exact digest replay. Verify the producer's binary source and the published HF manifest revision, not only a caller-supplied field. Distinguish `network_performed=false` in the **packager** from actual upstream network acquisition.

**C2** Read the real HF `left`, `right` and `nameOfNode` chunks for those numeric IDs, measure query-specific closure and full physical GET/byte budget. **No invented v3 performance.** v2 route-node historical estimates median 51.95 MiB, max 700.53 MiB are not physical measurements of this run.

**C3** Independently inspect source-bound native Wikidata **P14143** quantities/qualifiers/periods, P854 source documents and actual 1-to-N split receipts; migrate only through reviewed external rights. The ordinary Zelph entity-linked graph does not contain the full quantitative bundle.

**C4** Run the exact Agda import root / pinned toolchain on new proof modules and their runtime witness projection, and native ITIR/SLR tests/PostgreSQL persisted restart/replay with *the same* artifact identity; no CI-only surrogate.

**C5** Acquire an actual canonical NORA code/export fixture and do a real five-choice, multi-consumer review round trip with Éder's original semantics, no invented API.

**C6** Full Nat population inventory uses a lossless revision-aware `(QID, statement GUID)` cursor and explicit exhaustion; historical 57,989 is not the contemporary count. Five-QID exact graph name lookup is a useful calibration, not proof that the migration is complete.

## 3. Maximum-cut phases and deliverables

| Phase | Stop condition / exact deliverable | Existing PR owner | State |
|---|---|---|---|
| **P0 — Same-object source lock** | C1 raw manifest+route+receipt materialisation, SHA check and source lineage; B1 observed manifest schema regression replay | [ITIR #14](https://github.com/chboishabba/ITIR-suite/pull/14) | Reported live QID identity; independent byte replay OPEN |
| **P1 — Query-shaped index theorem** | A1 physical name partition + B2 decoder; no-coarse-fallback negative control, exact QID set; prove actual key→shard coverage on a chosen revision | [DASHI #1506](https://github.com/chboishabba/dashi_agda/pull/1506) / ITIR #14 | Mathematical hypotheses and verified index OPEN |
| **P2 — Hyperfabric adequacy** | A2/A3/A4/A6: certified query-family closure, compatibility/gluing, fine-coarse adequacy and typed negative-answer refusal | DASHI #1506 | **Genuine new mathematical cut** |
| **P3 — Physical transport and revision** | A5, B4, C2: revision transport; full direct shard decode; physical object coalescing; measured v2/v3 candidate budget | DASHI #1506 / [SLR #10](https://github.com/chboishabba/slr/pull/10) / ITIR #14 | OPEN |
| **P4 — SLR native semantics** | B5/B6, C3/C4: native quantitative statement/source evidence, S29 persisted review and sparse reopen on the original QID+GUID | SLR #10 | OPEN |
| **P5 — NORA and Nat programme** | C5/C6: actual NORA native export and governance/attribution; current full Nat population lossless inventory and external reviewed action only | [SensibLaw #514](https://github.com/chboishabba/SensibLaw/pull/514) as author-facing entry; SLR executes | OPEN |

## 4. Reuse / engineering choices

- **Trie/index:** the balanced-ternary prefix law is a suitable *formal index/refinement model*, not proof that Zelph's current chunk order is a trie. Prove the concrete key-to-prefix encoding or use a different **certified range index** when byte order is sorted but not ternary-aligned. Preserve collision buckets as fibres rather than fabricated unique answers.
- **Hyperformalism:** treat each shard as a view of a revision/scope-indexed hyperfabric with source and qualifier stalks; do not flatten to naked triples. The native Wikibase statement family is a different evidence plane, joined by explicit correspondence, not reconstructed from graph adjacency.
- **Transport:** preserve `shared-shard-artifact/v1` and current `itir.shard.*` ABI. The newly identified numeric manifest ABI is a *parser compatibility* issue, not a new manifest standard. Avoid another scheduler or database.
- **Storage identity:** xPollenation/CID and DA51 exist as typed, content-addressed indexing donors; a CID is an artifact/transport address, not a source-verification or promotion rule. Query-shaped Zelph sharding may coexist with Kant/ZOS content-addressed packaging without claiming globally optimal shards.
- **Efficiency:** don't fetch all 204 name chunks for every QID once a validated exact route/range/prefix index exists. Compare number of fetched chunks and bytes with the real five-QID scan; index size and update cost count too.
- **Golden discipline:** mark every theorem as already-existing vs proposed, and require pinned Agda kernel runs for new declarations. Never claim one modelled Boolean firewall is a runtime proof.

## 5. Exact questions the implementation must now answer

1. Are `nodeOfName` entries sorted by Wikidata QID string, internal node ID, or both? Does the order hold **globally across chunks**, or only inside chunks? Is each key allowed in multiple shards? These decide whether a sparse range index is complete.
2. Does the reported filtered receipt actually contain verified `left/right/nameOfNode` chunk memberships or merely field-presence placeholders? How much did those physical lookups cost in GETs/bytes?
3. Does the current HF manifest expose enough immutable identity to bind its indexed chunks to actual object SHA-256s? If not, which verification metadata must the ITIR producer collect?
4. Are the native P14143 statement/GUID/qualifier/reference observations independently revisioned and checked in SLR, rather than treated as latent in a Zelph entity graph?
5. Can the NORA candidate/reviewer source revision and SLR statement review be expressed as a guarded hyperfabric gluing obligation, with an explicit unresolved residual on revision mismatch?

**Do not close the programme until a same-object set of original source bytes, compiled runtime results, Agda kernel witnesses and SLR persisted state can be checked by a second operator.**

## 6. Attribution

- Original NORA project, choices and potential export/API: **Éder Porto**; original code/repository still to be pinned.
- Zelph upstream and graph binary/format: Stefan Zipproth / acrion, with provenance of contributions retained.
- Original wiki/Nat statements and sources: Wikimedia authors/contributors and each cited source.
- Agda modules and repo-local mathematical adapters: their respective repository contributors; relevant sheaf-hypergraph conceptual donor: Duta, Cassarà, Silvestri and Liò (arXiv:2309.17116). Trie/prefix and ultrametric background is not claimed as invented by this project.
- Original external compiler/Lean claims in pruned preservation: RequestProject/Aristotle donor, not newly established by a transport result.
- Numerical source identity and route receipt values above: **operator report**, not independently reverified raw bytes in this execution.
