# Zelph ↔ trie / ultrametric ↔ indexed hyperfabric ↔ Nat/NORA — exact maximum-cut

## Source acceptance update — finite-word A2 / name-fibre A1 / native original two-pass

**Still-verified base:** 7/7 Agda modules at source `4c89edb`, ITIR clean 95/95 Python plus native four schema roundtrips/five negative controls at `e64c04f`; SLR 4/4 focused Rust candidate joins and SensibLaw 17/17 reference tests at their reported older source. **New code NOT YET RUN on the new heads.**

**New formal acceptance target:** pinned `bash scripts/check_zelph_trie_hyperfabric_maxcut.sh` now checks **9** Agda modules: seven previously checked plus `ZelphFiniteQueryWordClosureExact` and `ZelphMultiNameShardFibreExact`. The finite-word theorem constructs final word equality from source-reachable one-step equality certificates (frontier-preserving); multi-shard name-fibre theorem retains every collision and proves singleton coverage embeds as a special case. Physical premises remain open.

**New ITIR runtime acceptance target:** `bash tools/check_zelph_physical_maxcut_offline.sh` adds finite-word boundary tests and strict numeric frontier route validation. Native fixture now constructs an original packed mini `.bin`, runs original two-pass QID `Q1` + unnamed numeric frontier `--node 8`, checks exact second-hop oracle and decoder without fabricating a name. Both new native producer compilation and physical source execution need local receipt.

**New SLR acceptance target:** `cargo test -p sensiblaw-source-handoff native_statement_evidence`. Read-only native GUID/mainsnak/rank/qualifier/reference/P854 comparisons are source-written, not yet compiled. The producer does not authenticate an asserted native SHA256, primary source bytes or S29 state.

**Physical P0–P5 remain as before:** original immutable HF source bytes and entire name domain, full specified query-family closure, revision transport, native P14143/P854 source payment, production S29, genuine Éder Porto NORA export and full current Nat cursor still missing. A synthetic mini `.bin` is *not* the 82 GiB Wikidata original.


## A1 collision-preserving proof-owner refinement — 15 November 2026

**New Agda source written, NOT yet Agda-checked:** `DASHI/Interop/ZelphMultiNameShardFibreExact.agda` defines `CompleteNameShardFibre` with finite `shardFibre` lists and two independent implications: `noMissingShard` (every physically containing shard appears) and `noFabricatedShard` (every listed shard actually contains the key). `zelphDuplicateNameFibreExhaustive` exposes their bidirectional exactness. `singletonNameFibre` constructs a special case from the previously checked `NameShardPartition` singleton witness, but no reverse conversion is assumed without a physical uniqueness theorem. This retains genuine name collisions rather than erasing them.

The repository's `scripts/check_zelph_trie_hyperfabric_maxcut.sh` now includes **nine** targets: the original checked seven, the new finite relation-word A2, and this new collision-preserving A1. **Only the original seven at `4c89edb` have a recorded Agda 2.9 PASS.** New declarations must be tested at their exact committed head before kernel-status promotion.

Both the new theorems are mathematical transport/representation improvements, NOT verified physical source-domain completeness. Their instantiation still requires original `nodeOfName` key-domain exhaustion, real selected packed-name bytes, decoded collision fibres and same-revision original source identity.

## New constructive A2 maximum-cut tranche — 15 November 2026

**Source committed, new head not yet kernel checked.** Existing DASHI A1–A6 conditional modules passed operator Agda 2.9 at exact earlier source `4c89edb` (7 targets). The new separate `DASHI/Interop/ZelphFiniteQueryWordClosureExact.agda` replaces the A2 circular proof premise *for finite left/right relation words* with a source-reachable local-step certificate and an induction:

`SourceReachableBoundary original selected state word` requires `original direction frontier ≡ selected direction frontier` at **each actually reached source frontier**; `zelphSelectedWordAnswerEqualsOriginal` then derives equality of the entire word's endpoint frontier; `zelphFiniteQueryFamilyBoundaryClosed` lifts it to each query in an explicitly declared family. The state is a frontier, not a fabricated single-valued node function. The accepted 7-target Agda source remains unchanged, and the exact-head checker now includes the NEW eighth module. Do not claim its Agda PASS until the operator reruns.

**ITIR P2 constructive implementation:** `tools/audit_zelph_finite_query_family.py` composes source-equal native one-hop root observations into finite `left/right` word answer traces, tracks provenance raw audit SHAs and reports exact missing `(node_id,direction)` boundaries. If the second-hop original/selected observation is missing, it **returns incomplete** rather than inventing negative answers. It explicitly refuses treating numeric `left/right` paths as property-labelled P31/P279 or P14143/SPARQL semantics. `tools/zelph_bin_filtered_route_builder.cpp` additionally accepts `--node <numeric Zelph ID>` for **unnamed physical frontier nodes**, retaining the original `--qid` seed and both source passes; raw-range, native decode and finite-family validators now carry these extra nodes. Existing QID name mapping is never replaced by made-up QIDs.

**New exact acceptance commands (NOT YET RUN at the new heads):**

```bash
# DASHI #1506 on clean new head, pinned Agda 2.9 (now 8 targets):
bash scripts/check_zelph_trie_hyperfabric_maxcut.sh
# ITIR #14 on clean new head: 11 Python suites plus native packed roundtrip:
bash tools/check_zelph_physical_maxcut_offline.sh
```

**Physical P0/P1/P2 execution after real pinned byte acquisition:** run the unchanged five-QID original-bin route; run native physical audit on actual sharded bytes; specify a finite `left/right` query family and evaluate it through `audit_zelph_finite_query_family.py`. If its output identifies missing numeric boundaries, rerun the **original** source-bin producer with the five seed QIDs and exact `--node` IDs from that report; re-fetch/re-hash and re-decode all routed selected shards, and rerun finite closure. This iterates until every declared query word has a complete physical one-hop observation on each reachable frontier, or returns incomplete. No assumption that adjacency sections are sorted by node ID, no global source-word claim, and no automatic property/qualifier semantics.

**Independent P4 advance:** SLR #10 now contains `crates/sl-source-handoff/src/native_statement_evidence.rs` (source-written, cargo not yet run). It refuses to join a claimed native statement GUID/property/revision/rank/mainsnak/qualifier/reference/P854 value that disagrees with the existing `StatementBundleReview` and graph candidate, and returns an explicit read-only candidate with `source_support_paid=false` and no edit authority. Native *raw entity byte rehash*, primary P854 document verification and persisted S29/restart still OPEN. The native GUID cannot be invented from Zelph node IDs; the statement shape follows Wikibase native statement semantics.

**Next decisive original-math cut:** instantiate A2's source-reachable equality with physically authenticated adjacency rows from a real immutable HF revision, then extend the query grammar beyond numeric left/right to a verified property-labelled, join-aware engine. A1 whole-domain original name coverage, A3–A6 real premises, original-source authentication, SLR native source payment, S29, external Éder Porto NORA and Nat full cursor remain OPEN.



## 15 November 2026: Ibrahim FLN ↔ Zelph physical-gate crosswalk

**Separate original objects, shared mathematics.** The [Ibrahim FLN exact-lemma matrix](https://github.com/chboishabba/dashi_agda/blob/feat/ibrahim-fln-ternary-revision-maxcut-20261114/Docs/IbrahimFLNMaximumCutAcceptanceAndExactLemmas20261115.md) (Agda [PR #1505](https://github.com/chboishabba/dashi_agda/pull/1505)) now distinguishes finite first-link graph mathematics, original author-parser source spans, and reviewed ITIR query objects. This Zelph [PR #1506](https://github.com/chboishabba/dashi_agda/pull/1506) continues to own the **different** original published HF `.bin`/Cap'n Proto source-evidence gate. Reuse the existing trie/hyperfabric and conditional consumer-lift owners, but **do not identify** an original Zelph QID/name edge with an original Wikipedia first-qualifying article link without an authenticated crosswalk.

| Coupled gate | Golden mathematical owner | Actual physical obligation | State |
| --- | --- | --- | --- |
| Z.P0 original byte identity | Zelph A1–A6 conditional contracts (#1506) | Published immutable `.bin` original range, offset/length/hash, selected HF chunk, content-addressed manifest and matching native packed decoder | **OPEN** |
| Z.A1 source names | QID/name trie exact route and A1 complete partition | Exhaustive original name objects, collision buckets, returned node IDs, complete declared original universe | **OPEN** |
| Z.A2 selected adjacency | A2 query-family original/selected equivalence and scoped negatives | Original source-graph/selected native first-hop equality and full required query closure | **OPEN** |
| FLN.B1 selected wiki link | Ibrahim original author-parser behavioural port; revision-bound edge Agda contract (#1505) | Actual independently retrieved `pageid`, `oldid`, wikitext bytes/SHA, first qualifying selected link and source-span receipt | **OPEN** |
| FLN.B2 original physical join | Existing ITIR Hyperfabric incidence/restriction + conditional crosswalk | Show the **same physically authenticated entity and edge** appear in both original physical and original wiki-revision packets; QID alone never pays semantic or byte equality | **OPEN** |
| FLN.B3 review + S29 | Existing consumer-bounded repair, evidence-scoped licence, selective reopening and SLR owners | Genuine reviewer-authorised query-specific after-state, qualifier/P854/GUID/P14143 retention, S29 persistence/reload | **OPEN** |

**ITIR native acceptance next:** clean checkout [ITIR #14](https://github.com/chboishabba/ITIR-suite/pull/14) at the source head represented by `e64c04f`; execute `bash tools/check_zelph_physical_maxcut_offline.sh` with the required `clang++ -fuse-ld=lld -std=c++17 -O2` path. The **reported** 90/90 Python passes comprise 58 earlier PASS plus 32 PASS **after two local corrections at `bcbf7c3`**; those fixes were committed later, not independently reverified at the current clean head. Decoder compilation is not a complete native packed writer/reader roundtrip. Then rerun `audit_zelph_native_selected_physical.py --source-bin ...` against the *actual* original original-byte object and immutable shards. Offline synthetic success is weaker than native original-object verification.

**No-promotion conditions:** no automatic QID/title/first-link identity, no absolute absence proof from a selected shard, no graph-only source-truth or Wikipedia edit authority, no unapproved NORA export, and no S29 evidence payment by a Python unit test. Keep original external attribution separate: Ibrahim–Danforth–Dodds original FLN, Duta et al. sheaf-hypergraph source inspiration, Éder Porto external NORA, and Zelph original upstream dataset/source. The new crosswalk text is DASHI programme governance, not a new original research citation.

## Authoritative current programme cut — 15 November 2026 (exact-head operator replay)

**This section supersedes the dated checkpoint summaries below; those remain for audit history, not current gate status.**

**Formal/offline CLOSED at recorded commits:** DASHI PR #1506 source commit `4c89edbe90ef0e29ea5c02b18bd5dfe090ab9e61`: seven pinned Agda 2.9 targets, clean tracked worktree, exit 0. ITIR PR #14 commit `e64c04f32f791502f6feccd3d918ece9a426c122`: ten Python suites **95/95 PASS**, native C++ Cap'n Proto writer+decoder **4 packed-message roundtrips and five fail-closed controls**, exact-head script exit 0, no tracked modifications. Both are operator-executed and were not independently replayed by this chat runtime. SLR candidate Rust **4/4** and SensibLaw reference/NORA **17/17** are separate reported focused results, not persisted/native-source acceptance.

**Status rule:** `conditional-theorem-kernel-pass` ≠ `physical-premise-constructed` ≠ `all-query-complete` ≠ `native statement evidence paid` ≠ `S29 durable review` ≠ `NORA external-author fixture verified` ≠ `operator-authorised Wikidata edit`. The first two offline source acceptance gates have been paid; the physical, semantic and production gates remain open.

### A: exact Agda mathematical declarations and the still-missing concrete theorems

| Gate | Existing kernel-checked declaration (already proved *conditional*) | Outstanding concrete proof obligation — required witness or proposed next lemma, NOT yet proved |
|---|---|---|
| **A1** | `NameShardPartition`; `zelphPhysicalNameShardPartitionExact` | Establish `indexedCoverage` **and** `indexedExclusivity` for *actual* source graph QID/name keys across the whole `nodeOfName` domain. First prove full physical manifest cover and key range/sort semantics, then a byte-checked `contains` relation; if duplicate keys can occupy multiple shards, use a **multi-shard fibre** rather than instantiate a false singleton. Proposed target `zelphPublishedNameCoverMatchesOriginalBinDomain` and `zelphDuplicateNameFibreExhaustive` (new names, not current source). Five selected QIDs do not establish A1 globally. |
| **A2** | `QueryFamilyClosure`; `zelphBoundedShardQueryFamilyCompleteness`; counterexample `nameOnlyCannotCertifyAdjacency` | Construct `edgeClosure` from actual original binary and decoded selected view **for a declared query grammar**. First close finite one-hop `left`/`right` root answers (P2); then prove the selected subgraph is closed under *every* step, join and relation word in the declared family. Proposed `zelphSelectedOneHopAnswerEqualsOriginal`, `zelphQueryFamilyBoundaryClosed` and `zelphOriginalQueryAnswerFactorsThroughSelected` (new targets, not discharged). The existing record's `edgeClosure` is the desired equality as a supplied premise; its Agda acceptance does NOT prove that real equality. |
| **A3** | `CompatibleShardSections`; `zelphHyperformalShardGluingSound`; `conflictingOverlapsCannotGlue` | Provide **real** `localVertex`, `localEdge`, and each `overlapAgreement` indexed by identical QID, source, revision, qualifier, temporal and reviewer context; reject incompatible overlaps. Current theorem **constructs** a `GlobalSection` from an already compatible family, it does **not** prove uniqueness or infer compatibility from labels. Proposed `zelphRealShardOverlapAgreement` (new). |
| **A4** | `FibreConstant`; `zelphPrefixQuotientQueryAdequacyIffForward`, `zelphPrefixQuotientQueryAdequacyIffBackward`; `nameOnlyIsNotAdequateForEdgeQuery` | Build an actual physical prefix/range projection and demonstrate a representative law for its **image**. Show selected query answers constant on physical projection fibres; supply a concrete native quantity/P854 counterexample to a name-only projection. The existing two directions make an equivalence **only under the stated representative hypothesis**, not a free-standing unconditional physical `iff`. Proposed `zelphPhysicalRangeProjectionAdequacy` (new). |
| **A5** | `RevisionFibreTransport`; `zelphRevisionRefinementTransportCoherent` | Prove `stableFibreCorrespondence` for **actual old/new graph revisions** and distinguish stable `(source,QID,GUID,scope)` fibres from regenerated internal node/chunk IDs. Produce a dependency-indexed reopen receipt; a provenance `String` alone is not a cryptographic equality. Proposed `zelphRevisionCorrespondencePreservesReviewedFibres` and `zelphChangedDependencyRequiresReopen` (new). |
| **A6** | `ScopedNegativeCertificate`; `zelphQueryScopedNegativeCompletenessIff`; `uninspectedCannotGiveNegative` | Produce **both** missing-answer preservation and reflection for a formally enumerated closed-world query family, same revision, complete decoder and full dependency closure. Missing/uninspected/ambiguous source must remain **unresolved**. The A6 bidirectional theorem is correct *given* the two certificates: it does not establish they exist for Wikidata. Proposed `zelphPhysicalScopedNegativeCertificateSound` (new). |

### B: exact runtime/refinement targets (existing roadmap names; not all Agda declarations)

| Gate / bridge target | Owner | Exact acceptance and missing evidence |
|---|---|---|
| **B1 `hfManifestShardIdentityPreserved`** | ITIR | Real published numeric-v2 raw manifest, immutable dataset SHA, schema/path/chunk range correspondence and raw SHA digest; no caller-only identity |
| **B2 `hfSelectedShardDecodePreservesKeyNode`** | ITIR → DASHI | Compiled decoder now passes native generated-schema roundtrips; missing real published packed bytes, independent original source-range equality and an explicit **decoder soundness/refinement argument** |
| **B3 `natFiveQidsExactRouteReplays`** | ITIR | Five actual QIDs, physical `nodeOfName` and reverse name rows, original `.bin` source-bin route, new route digest, request/receipt hash chain; old digest cannot be reused |
| **B4 `hfPhysicalRequestDedupeAndBudgetExact`** | ITIR / existing SLR acquisition | Actual **unique physical** GET count, cold-object coalescing, `≤5` concurrency, bytes transferred (distinct from planned bytes/cache), strict truncation policy, fail-closed retry |
| **B5 `zelphGraphNativeStatementJoinIsEvidenceOnly`** | SLR #10 | Independent same-original native `(QID, statement GUID)`/mainsnak/rank/qualifiers/time/units/references/P854 source with revision correspondence; no inference from graph edges to evidence payment |
| **B6 `natZelphNoraReviewReplaySameSource`** | SLR S29 + ITIR + SensibLaw reference | Same source/revision/QID/GUID/subject/standpoint/reviewer; restartable durable review, rejected/held options retained, sparse reopen upon dependency change |

### C: indispensable empirical/production receipts

| Gate | Exact hard artifact and stop condition |
|---|---|
| **C1** | Recomputed on-disk raw SHA256 of original request, immutable manifest, new route, packaged receipt and selected physical bytes, plus independent source URL/commit identity. No asserted hash without bytes |
| **C2** | Native decoder output on **real** selected `left`, `right`, `nodeOfName`, `nameOfNode` objects; exact original `.bin` source-range equality; measured GET/bytes/cache and no truncation. Then real finite-family closure; synthetic native fixtures are not this receipt |
| **C3** | Independently inspect actual native P14143 quantities, periods/qualifiers, GUIDs and P854 primary source records, with source-bound 1-to-N split and review disposition; do not promote graph-only candidates |
| **C4** | Preserve exact-head Agda 7/7 and ITIR 95/95 + native acceptance receipts; **remaining** same-artifact SLR PostgreSQL S29 persistence, restart/readback, sparse reopen and original-source native tests (not simply more offline fixture tests) |
| **C5** | Real Éder Porto NORA export/API artifact and documented semantics; five-choice multi-consumer replay into SLR review without flattening or inventing reviewer authority |
| **C6** | Lossless **current** Nat `(QID, statement GUID)` cursor, counted page receipts and explicit exhaustion across population. Historic P5991 statement total `57,989` and five-entity fixtures are not a current complete enumeration |

### Phase roadmap — keep one active PR per repository

| Phase | A/B/C cuts | Deliverables (independent artifacts) | Evidence-based exit | Owner |
|---|---|---|---|---|
| **P0 source lock** | B1/B3/C1 | `original-bin-source.json`, pinned full-manifest raw bytes/SHA, new five-QID route, original-source build hash, selected-object list, local-or-HTTP206 same-original range receipts | Original `.bin` identity genuinely authenticated and raw source-range equality independently checked, no synthetic records | ITIR #14 |
| **P1 name partition** | A1/B2/B3 | Real native `nodeOfName`/`nameOfNode` per-QID outputs, duplicate-name fibre results, whole-domain `nodeOfName` range/cover evidence, accepted partition witness | Finite selected QID theorem first; global A1 only after source-domain coverage and exclusivity or multi-fibre reformulation | ITIR #14 + DASHI #1506 |
| **P2 query-family completeness** | A2/A3/A4/A6/C2 | Original-vs-selected one-hop arrays/counts and source graph equality; explicit query syntax/dependencies, closed neighbourhood fixpoint and counterexamples; physical overlaps and scoped negative policy | `∀q∈F, answer(G,q)=answer(view(G),q)` with **proved premises**; no general closure or negative claim from mere one-hop equality | ITIR #14 + DASHI #1506 |
| **P3 transport/revision** | A5/B4/C2 | Cold physical GET/cache/byte budget; two actual revisions, stable key mapping, changed-dependency reopen receipts | Measured ≤5 cold physical concurrency, old/new fibre transport only on justified stable keys | ITIR #14 + SLR #10 / existing acquisition owner |
| **P4 native source/S29** | B5/B6/C3/C4 | `(QID, GUID)` native statement bundle, cited P854 verified evidence, qualified quantity/period, S29 durable initial-review/restart/reopen outputs | Production reviewed source receipt independent of graph candidate; readback matches persisted review decisions | SLR #10 + existing S29 owner |
| **P5 NORA/Nat population** | B6/C5/C6 | Attributed true NORA export + semantic crosswalk, five-choice multi-perspective replay, complete current Nat cursor/exhaustion, explicit external authorisation if any write | No source or reviewer authority from hypothetical NORA; lossless population and actual source-supported/held decisions | SensibLaw #514 (reference), SLR production |

### The immediate three highest-information cuts

1. **P0.1: real bytes**, not more synthetic tests: replay original pinned manifest + original source binary (or exact immutable original HTTP 206 ranges), download only manifest-selected physical objects, compare raw original packed ranges and produce independently recomputed SHA receipts. Real `hf` access or an already retained original `.bin` and selected chunk files is the external dependency.
2. **P1.1/P2.1: actual five-QID native replay:** compile the existing filtered original `.bin` producer; emit a **new** exact route with bounded selected-root `nodeAdjacency`, native decode 4 section types, compare five actual name routes and original vs selected left/right neighbour sets and counts; preserve ambiguity/truncation failures. This proves bounded first-hop equality only.
3. **P2.2/P4.1: extend semantics, not transport:** explicitly select a finite real query family and prove source/selected answer closure through its relation steps/joins; in parallel obtain independent native `(QID,GUID,P14143,P854)` source bundles in SLR and persist/restart the S29 review. A2 original query closure and P4 source evidence are **independent**, not substitutable.

**Hard stop:** physical or native proof cannot be inferred from a generated synthetic Cap'n Proto fixture, a request string, a manifest label, an asserted digest, or an Agda record whose fields are the desired propositions. Retain exact original authors: Zelph acrion/upstream, NORA Éder Porto, Wikimedia/primary source creators and repo-specific formal/runtime implementers.


## Latest P0/A1/A2 physical acceptance checkpoint — 15 November 2026

**Golden Agda result remains exact-head PASS:** the operator's clean Agda 2.9.0 replay at `4c89edbe90ef0e29ea5c02b18bd5dfe090ab9e61` checked seven core/interop modules (exit 0). Since then this PR has only gained documentation, so the checked mathematical source has not changed.

**ITIR operator verification at original physical-tranche head `bcbf7c3`:** four new Python suites initially **23 PASS / 9 FAIL**. The failures were exactly one wrong variable name in the native audit range proof (`manifest_sha` vs `manifest_sha256`) and one negative test that changed a name-section chunk index without updating the matching immutable physical filename. After local corrections, **32/32 new tests PASS**; combined with the earlier **58/58** Python tranche the operator reports **90/90 locally passing**. This is an **overlay-tested local receipt, not an exact-head test pass of the original `bcbf7c3` Git tree**. The two fixes have now been committed to the same existing ITIR PR #14.

**Native Cap'n Proto compilation:** operator successfully compiled `zelph_selected_packed_shard_decoder.cpp` using `clang++ -fuse-ld=lld` (default GNU linker rejected LLVM IR bitcode in local `libcapnp.a`). This verifies **compilation and CLI response**, not real packed shard decoding. Subsequent new ITIR work adds an *actual native writer/reader roundtrip*: `zelph_native_capnp_fixture.cpp` writes genuine upstream-schema packed data for the four sections, and `check_zelph_native_capnp_roundtrip.sh` decodes and checks all four, direction/index/language mismatches and forbidden trailing bytes. It remains **source-written, not yet run**.

**Physical receipt hardening:** the native audit now requires each previously recorded range receipt to match the source's exact `offset`, URI, size and SHA; pinned remote-original URL and HTTP 206 flag are enforced. It accepts `--source-bin` to independently repeat same-original packed-range comparison **in the native audit run**; without this flag it records `source_bin_range_equality_reverified_in_this_run=false` and cannot treat a raw JSON receipt alone as an independently authenticated original. Genuine HF source identity and first-hop physics are still **OPEN**.

**Exact next source acceptance:** run `bash tools/check_zelph_physical_maxcut_offline.sh` on the clean latest [ITIR #14 branch](https://github.com/chboishabba/ITIR-suite/pull/14). The script checks all ten Python suites plus both genuinely compiled upstream-schema C++ binaries. A source-level PASS does not close real HF raw-byte execution. Full physical operator commands and file/algorithm ownership: [Zelph original-bin ↔ selected HF physical P0/A1/A2 guide](https://github.com/chboishabba/ITIR-suite/blob/agent/nat-filtered-route-producer/docs/planning/zelph_original_bin_hf_ranges_maxcut_20261114.md).

**A/B/C/P exact remaining gates unchanged in mathematical strength:** A1 complete original name partition; A2 actual source/selected query-family closure beyond nominated roots/one-hop; A3 overlap gluing on real source indexed stalks; A4 real prefix quotient and factorisation; A5 graph revision/sparse reopening; A6 closed-world scoped negatives; SLR GUID/P14143/P854 + S29; real Éder Porto NORA export and contemporary Nat exhaustiveness. **No native source/payment, absolute absence or Wikidata edit authority** is created by these tests or by Agda conditional source checking.




## Verified Agda gate + concrete physical original-.bin max-cut (14 November 2026)

**A1–A6 conditional proof source: EXACT-HEAD KERNEL PASS at `4c89edbe90ef0e29ea5c02b18bd5dfe090ab9e61`**. Operator reported clean tracked worktree, no overlays, seven Agda 2.9.0 targets checked using `scripts/check_zelph_trie_hyperfabric_maxcut.sh`, exit 0. It replaces the older tentative overlay-only status. No underlying Agda proof source has been changed in the following physical ITIR tranche; a later documentation-only PR head does not retroactively change that Agda result.

**ITIR 58/58 local Python:** reported on `a119add`, before the *new* physical-replay source below. **Not** evidence that the latest remote PR head passes all new Python tests or compiles its native C++ adapter.

**Physical P0/P2 big cut source-written in the same ITIR PR #14:**
- `verify_zelph_bin_shard_exact.py`: selected packed shard bytes = exact local original `.bin` offset/length slices; independently rehash manifest + selected chunks.
- `verify_zelph_hf_remote_original_ranges.py`: optional no-local-82-GiB-blob path with immutable HF original `.bin` exact HTTP 206 range requests and byte equality. Must fail closed if range requests are unsupported.
- `plan_zelph_hf_selected_fetch.py`: manifest/route-selected-only immutable HF download plan with explicit GiB cap and opt-in existing HF client.
- `zelph_selected_packed_shard_decoder.cpp`: thin native Zelph Cap'n Proto four-section decoder for selected QIDs/nodes, preserving collisions and neighbour truncation.
- `audit_zelph_native_selected_physical.py`: requires an exact same-original byte-range equality receipt, independently rehashes selected physical objects, then compares actual `nodeOfName` + inverse `nameOfNode` and root `left/right` neighbour sets and raw counts with the original-bin producer oracle. All four corresponding new Python test files have been added but **not yet run**; native C++ has **not yet been compiled** here.

**Operator's next decisive acceptance** is to run the exact five-QID producer/fetch/range/native sequence in [ITIR's consolidated physical execution document](https://github.com/chboishabba/ITIR-suite/blob/agent/nat-filtered-route-producer/docs/planning/zelph_original_bin_hf_ranges_maxcut_20261114.md) and archive the recomputed raw SHAs, source-revision correspondence, full native JSON and fail-closed checks. The prior historical filtered-route/receipt digests are not reusable after the C++ producer's added adjacency output.

**Exact gate disposition:** A1's *formal source* CLOSED; *selected real original name bytes* OPEN; complete original name-domain partition OPEN. A2's *conditional factorisation source* CLOSED; actual selected-root one-hop equality OPEN; all specified relation words/joins OPEN. A3–A6 physical premises OPEN; real native GUID/P14143/P854 + S29 production + Éder Porto NORA export OPEN. A successful byte-range comparison alone does not fill those semantic gaps, create global absence or grant edit authority.

**Current physical blocker:** This chat's environment could not resolve `huggingface.co` via DNS or open the pinned raw manifest using web retrieval, so no physical HF bytes were fetched here. The published Zelph full network is roughly 82 GiB, but the published manifest supplies source offsets and exact packed shard paths for selective comparisons. See [Zelph Sharding](https://zelph.org/sharding/).




## Latest kernel/dependency integration checkpoint — 14 November 2026 (after local Agda 2.9 investigation)

**Current authoritative distinction:** The operator ran ITIR's six targeted suites at prior PR head `a119add`: **58/58 tests passed in 3.54 s**. SLR reported **4/4** focused Rust tests and SensibLaw/NORA **17/17** Python tests. These are native *local reported* test receipts for those recorded heads; they do **not** authenticate raw remote HF payloads, nor automatically certify later source heads.

**Agda kernel investigation:** The operator's Agda 2.9.0 worktree first exited **42** and identified three concrete source blockers. A locally corrected overlay, using the existing core sort correction [`0dc254eabe`](https://github.com/chboishabba/dashi_agda/commit/0dc254eabeb00c4fdf1dc6d6f1a0e013d05d9606), was reported to kernel-check the new A1–A6 module cleanly (zero holes, postulates or metas in that source). This is an **operator-reported local corrected-overlay kernel result**, not yet an independent type-check of the **new committed PR head**.

The exact corrections are **now committed onto this existing PR #1506**:

| Error found | Corrected ownership | Exact change |
|---|---|---|
| A1 implicit route outside scope | `DASHI/Interop/ZelphPhysicalShardQueryMaxCutExact.agda` | Bind `{route = route}` in implementation |
| Coverage parser error | `DASHI/Interop/ZelphBoundedGraphCoverageExact.agda` | Remove stray `: QueryCoverageStatus` line |
| Query-index elaboration | `DASHI/Core/QueryIndexedProjectionSpineAdapterExact.agda` | Explicit semantics/query/project (and refine for repair) in query→collision, reverse and separation witnesses |
| Existing core universe mismatches | `DASHI/Core/{TypedDependencyCore,AdmissibleReachability,FutureObservationLanguageQuotientExact,ReopenableConsumerInterventionKernelExact}.agda` | Bring in **exact previously authored code** from `0dc254eabe`, not a parallel reformulation |

A reusable **local pinned exact-head kernel acceptance root** is now committed at
`scripts/check_zelph_trie_hyperfabric_maxcut.sh`:

```bash
git switch agent/nora-perspective-consumer-maxcut-20261114
git pull --ff-only
bash scripts/check_zelph_trie_hyperfabric_maxcut.sh
```

It refuses a dirty tracked worktree, prints the exact local commit SHA and invokes the repository's pinned `scripts/run_agda29_parallel_check.sh` over the seven pertinent core, bridge, coverage and A1–A6 modules. A successful exit is a **source-level Agda kernel receipt for this head** only. It cannot certify the real physical index, Cap'n Proto bytes, query-family edge closure, native P854 statements, S29 persistence, or NORA authorship.

### A/B/C/P gate disposition after this merge

| Gate | Current paid deliverable | Highest-information next exact gate |
|---|---|---|
| **A1 (formal)** | Source-level partition theorem with route scoping repaired; local overlay reportedly checked | Exact-head Agda runner exit 0; instantiate against complete manifest-listed name objects **and prove that they exhaust original source name domain** |
| **A2 (formal)** | Conditional family factorisation and name-only collision | Same-object original `.bin` vs **real pinned** physical HF left/right/root-neighbourhood comparison; derive full declared query-family closure rather than only one hop |
| **A3** | Conditional compatible hyperfabric gluing theorem | Real overlapping source/revision/qualifier/temporal stalk equality |
| **A4** | Fibre constancy criterion and name-only information-loss witness | Verified concrete prefix/range map, representative and selected query family |
| **A5** | Conditional semantic revision transport | Actual old/new graph receipt, stable fibre and sparse S29 reopening |
| **A6 (formal)** | Corrected bidirectional scoped negative law; operator-reported local overlay kernel acceptance | Exact-head kernel receipt and real closed-world scope/decoder certificates |
| **P0/P1** | ITIR **58 reported tests passed**; manifest-name-cover and four-raw-file replay validators implemented | Replay the *actual* raw request/manifest/route/receipt and all real selected chunk bytes against pinned immutability and source provenance |
| **P2/P3** | Original-bin bounded one-hop oracle and selected-chunk comparator source/tests implemented | Compile/rerun physical C++ at pinned schema; collect GET+bytes/cache metrics; prove closure on required relation words |
| **P4/P5** | SLR candidate/native join and attributed SensibLaw NORA reference adapter; focused reported tests passed | Same-original Wikidata GUID/P14143/P854, persisted S29, actual Éder Porto NORA fixture, full Nat `(QID,GUID)` inventory |

**Important:** none of these checks authorises source-support payment or external Wikidata edits. Evidence, transport, query completeness and reviewed semantic authority remain independent coordinates. **No CI-only success substitutes for local kernel or physical same-object receipts.**


## Latest maximum-cut checkpoint — 2026-11-14, post-local 41/4/17 regression ledger

**Reported local acceptance at earlier heads (provided by operator):** ITIR #14 41/41 target tests, SLR #10 four new join tests, SensibLaw #514 17 NORA tests. These are **not tests of the subsequent commits below**. DASHI A1–A6 Agda kernel acceptance remains **OPEN**; Agda checking does not have to wait for raw HF physical premises. A6's extra antecedent was removed in DASHI commit `54f41be`; that corrected source must now be checked with the pinned Agda toolchain.

**Observed same-object bytes:** Immutable HF dataset SHA `0d4bd670959ebddae72f70d973410fdea8917ec1`, full manifest raw SHA256 `cedd5cf0e4951ae1aa7c2c5968614b0eb72a4c3b5c8b2dc4ab18c40be8c83f59`, filtered route content address `fbc43156ae80b8e32f9cbd5b32dd30dcc2085ad9ead04e73e16ff8f376425233`, packaged receipt payload digest `d3970f969c4e9b030fdb75c2914318c20d9e20eb096cb0212ed3b6b421b6dd05` remain **operator-reported**, not independently replayed by this integration. A digest's presence is not cryptographic source-origin authentication. Five-QID name→node/chunk mapping is reported, not a whole-graph closure receipt.

### Newly implemented after those local tests: concrete P0/P1/P2 cuts

| Cut | Source & precise acceptance | What remains OPEN |
|---|---|---|
| **P0a — hashed route ↔ interpreted route** | ITIR `package_zelph_filtered_route_receipt.build_receipt` now refuses any dictionary that differs from the actual file whose raw bytes are hashed. Two regression tests added. | New exact-head native test; old reported package digest does not retroactively authenticate any new receipts |
| **P0b — four-object raw replay** | ITIR `tools/verify_zelph_filtered_route_replay.py` checks raw request, v2 manifest, filtered route and receipt **independently**, recomputes manifest/route/receipt SHA256s, rejects duplicate JSON keys, requires immutable dataset SHA claim in request, checks QID/node/chunk/routing agreement and authority flags; adversarial tests added | Obtain actual four files, independent expected hashes/source URL evidence, pinned producer build and source-bin→HF graph identity |
| **P1 — full manifest name cover** | ITIR `verify_manifest_name_cover` compares the **entire manifest-listed** `nodeOfName` chunk set to raw-byte-audited objects with chunk/language/URI/length checks. Duplicate physical name chunks and missing entries rejected. | Instantiate against downloaded full numeric-v2 manifest and all name chunks; independently verify decoder; manifest listed cover ≠ original graph name-domain completeness |
| **P2a — original .bin one-hop oracle** | ITIR's *existing* `zelph_bin_filtered_route_builder.cpp` now gathers bounded selected-root `AdjChunk.getAdj()` values while scanning source `left/right` sections, checks section direction, reports truncation, preserves per-direction physical chunk route, and refuses QID duplicates across name chunks. No new graph backend. | Compile exact Cap'n Proto source, rerun against original locked `.bin`; bin SHA/source→HF revision bridge |
| **P2b — selected HF one-hop comparison** | ITIR `audit_selected_adjacency_against_bin` SHA256-checks supplied selected `left/right` chunks, verifies root+section/chunk coverage and compares decoded adjacency exactly with the non-truncated original-bin oracle; corruption, omission, mismatch and truncation tests added | Fetch real *selected* immutable HF objects, bind to manifest object paths, run trusted C++ decoder and replay; then prove wider query-family closure. One-hop equality does NOT establish all relation words |
| **A1–A6 kernel** | DASHI `ZelphPhysicalShardQueryMaxCutExact.agda` has source-written conditional A1–A6 and counterexamples, with A6 type corrected | Local pinned Agda kernel check, then actual physical propositions filling the theorem premises |
| **P4/P5** | SLR candidate join and SensibLaw NORA reference adapter retained in original PRs; reported focused tests passed before this new tranche | Native GUID+P14143+P854 source support, real S29 persisted replay, actual attributed Éder Porto NORA export, lossless contemporary Nat population |

**Status semantics:** `source-written` / `reported-local-pass` / `new-code-not-rerun` / `physical-premise-open` / `kernel-open` / `production-open` must remain separate. A dependency-set equality in `evaluate_query_closure` is NOT a demonstrated boundary-closed neighbourhood; only its labelled *dependencies* are checked, and it intentionally emits `original_graph_edge_closure_proved=false`.

### Exact replay and acceptance commands

```bash
# ITIR PR #14 exact current head; includes the new test suites:
PYTHONPATH=itir-mcp/src python -m pytest -q \
  itir-mcp/tests/test_zelph_query_closure.py \
  itir-mcp/tests/test_exact_wikidata_name_route.py \
  itir-mcp/tests/test_published_zelph_manifest_compat.py \
  tests/test_package_zelph_filtered_route_receipt.py \
  tests/test_verify_zelph_filtered_route_replay.py \
  tests/test_probe_zelph_hf_nat_routes.py

# Four independently obtained raw JSON files. Expected hashes are compared
# with actual file bytes; upstream HTTP authenticity is still a distinct gate.
python tools/verify_zelph_filtered_route_replay.py \
  --request /path/to/source-request.json \
  --manifest /path/to/wikidata-20260309-all.hf-v2.json \
  --route /path/to/zelph-filtered-route.json \
  --receipt /path/to/nat_zelph_filtered_route_receipt.json \
  --dataset-sha 0d4bd670959ebddae72f70d973410fdea8917ec1 \
  --manifest-sha256 cedd5cf0e4951ae1aa7c2c5968614b0eb72a4c3b5c8b2dc4ab18c40be8c83f59

# SLR #10:
cargo test -p sensiblaw-source-handoff

# SensibLaw #514:
python -m pytest -q tests/test_wikidata_nora_review_handoff.py

# DASHI #1506: use the repository's pinned Nix/Agda toolchain
# and type-check DASHI/Interop/ZelphPhysicalShardQueryMaxCutExact.agda
```

**P0 verifier compatibility warning:** the new replay tool insists the historical request actually included the immutable dataset SHA and the real full manifest SHA256. If those coordinates were only recorded out of band, it must **refuse**, not edit a historical receipt into a pretend prior verification. A new explicitly versioned/revision-locked source request and freshly packaged receipt may then be necessary.

**Release stop condition:** the new Python tests and C++ build pass locally, raw bytes and source provenance replay, the complete manifest cover is checked, the selected HF adjacency physically matches the source-bin oracle, A1–A6 kernel-check, and SLR's native source review is separately accepted. No single stage grants truth/source payment/migration/edit authority.



**Date:** 2026-11-14. **Golden authority:** DASHI/Agda. **Production:** SLR Rust/PostgreSQL. **MCP / external graph routing:** ITIR-suite / Zelph. **Historical reference:** SensibLaw Python. **External NORA authorship:** Éder Porto. **No new parallel index, review store, scheduler or proof system.**

**Source state:** A1–A6 conditional proof code is now committed on PR #1506, but has **not** been kernel-checked in this environment. The physical HF receipts remain operator-reported rather than independently rehashed; SLR PostgreSQL acceptance is still open. See the implementation delta at the end.

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

These were **proposed original physical-instantiation goals**. Conditional A1–A6 declaration source has now been added on PR #1506; kernel replay and concrete physical premise discharge are still OPEN. The file owner for new proof code should be DASHI on the existing NORA/ontology Agda rollup PR #1506; reuse all modules in §1. **Novelty discipline:** the abstract prefix-ultrametric law, fibrewise constancy criterion for factorisation, and conditional compatible-gluing principle are already known mathematics and in several cases already proved in the repository. The genuinely new *work here* is establishing the **concrete Zelph published-byte partition, complete-for-query physical projection, actual overlapping source/revision correspondence, and executable refinement witnesses**. A3/A4/A6 should reuse and instantiate existing theorems where the hypotheses are available, not be advertised as entirely new foundational theorems.

### A — New same-object proof obligations: distinguish true new content from existing theorem instantiation

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
| **P2 — Hyperfabric adequacy** | A2/A3/A4/A6: certified query-family closure, compatibility/gluing, fine-coarse adequacy and typed negative-answer refusal | DASHI #1506 | **Concrete new physical/query proof cut; reuse known abstract theorems** |
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


## 2026-11-14 implementation tranche — committed source, NOT runtime acceptance

This section supersedes older statements above that A1–A6 have only proposed names. On the **existing [DASHI PR #1506](https://github.com/chboishabba/dashi_agda/pull/1506)**, `DASHI/Interop/ZelphPhysicalShardQueryMaxCutExact.agda` is now source-written. It imports the existing query-factorisation, prefix-ultrametric, indexed-fabric, typed-hyperfabric and Zelph coverage owners. It does **not** reimplement a generic trie/sheaf and it makes **no claim of physical HF verification or Agda kernel acceptance**. The proof source needs exact-head pinned local Agda replay; this environment has no Agda executable.

### Exact A-gate declaration-to-deliverable ledger

| Gate | New code/theorem declaration | What is shown conditionally | Remaining physical or kernel discharge |
|---|---|---|---|
| A1 | `NameShardPartition`, `zelphPhysicalNameShardPartitionExact` | Key coverage + uniqueness from an explicitly provided partition witness | Exhaustively enumerate real `nodeOfName` manifest keys, bytes, duplicate-name fibres, and bind the verified source graph revision. Singletons cannot be fabricated for collisions. |
| A2 | `QueryFamilyClosure`, `zelphBoundedShardQueryFamilyCompleteness`, `nameOnlyCannotCertifyAdjacency` | Edge-closure premise factors the full answer through the selected view; finite name-only collision refutes unguarded adequacy | Real `left/right/nameOfNode` decode, original-graph answer evaluation and family-specific closure over selected physical objects |
| A3 | `CompatibleShardSections`, `zelphHyperformalShardGluingSound`, `conflictingOverlapsCannotGlue` | Typed global section from compatible stalk restrictions; conflicting local overlap cannot glue | Overlap/source/qualifier/revision equality on actual objects, checked extractor |
| A4 | `FibreConstant`, `zelphPrefixQuotientQueryAdequacyIffForward`, `...Backward`, `nameOnlyIsNotAdequateForEdgeQuery` | Fibre constancy is necessary; sufficient where an explicit image-representative is supplied | Physically verified prefix/range projection and representative; do not equate Cap'n Proto interval with ternary ball by fiat |
| A5 | `RevisionFibreTransport`, `zelphRevisionRefinementTransportCoherent` | Stable semantic fibres transport **given** a source/revision correspondence | Actual old/new graph identity, dependency-scoped stable-fibre map and re-open receipts; node IDs do not transport by default |
| A6 | `ScopedNegativeCertificate`, `zelphQueryScopedNegativeCompletenessIff`, `uninspectedCannotGiveNegative` | Bidirectional scoped negative equivalence when preservation + reflection certificates exist; without a certificate abstain | Declared closed-world source scope, complete decoder, exact family partition and no missing source dependencies |

**Proof labels:** `source-written` ≠ `kernel-checked` ≠ `physical premise discharged`. The A1/A2/A3/A5/A6 records deliberately demand inputs; populating them with a string receipt does not independently authenticate the underlying bytes. A4 requires a representative law, not just a proposed address mapping.

### Cross-repository implementation heads (one existing PR per repo)

| Owner | Source-added deliverable | Test entry point | What is still not claimed |
|---|---|---|---|
| [DASHI #1506](https://github.com/chboishabba/dashi_agda/pull/1506) | `DASHI/Interop/ZelphPhysicalShardQueryMaxCutExact.agda` A1–A6 conditional lemmas and counterexamples | Pinned local Agda on this import root | Kernel/byte premise acceptance |
| [ITIR #14](https://github.com/chboishabba/ITIR-suite/pull/14) | `itir-mcp/src/itir_mcp/zelph_query_closure.py`: raw object SHA-256+length checks, complete-for-declared-object enumeration, collision buckets, revision-checked dependency coverage | `PYTHONPATH=itir-mcp/src python -m pytest -q itir-mcp/tests/test_zelph_query_closure.py` | Completeness of the manifest's *source graph* universe or correctness of caller-supplied Cap'n Proto decoder |
| [SLR #10](https://github.com/chboishabba/slr/pull/10) | `crates/sl-source-handoff/src/zelph_graph_native_join.rs`: pinned graph/native candidate join, explicit correspondence, source/qualifier/ref retention, non-promotion | `cargo test -p sensiblaw-source-handoff` | Native GUID provenance inspection, S29 persisted storage or source evidence payment |
| [SensibLaw #514](https://github.com/chboishabba/SensibLaw/pull/514) | `plan_nora_zelph_scoped_review`: read-only NORA source/QID/revision/collision/closure join and digest-labelled plan | `python -m pytest -q tests/test_wikidata_nora_review_handoff.py` | True NORA export parser or external edits |

### End-to-end gate order and exact acceptance artefacts

1. **P0 / B1+B3+C1:** check in or otherwise make independently accessible the *raw* full manifest, request, scanned `nodeOfName` object bytes/digests, route JSON, matching packager receipt, producer source commit and immutable dataset SHA. Re-hash raw bytes, never source fields copied from the caller; prove no network work was confused with packager-only `network_performed=false`.
2. **P1 / A1+B2:** run `audit_declared_name_partition` with a pinned, trusted Cap'n Proto decoder and every declared name object. Verify that its *declared-object* coverage matches the actual complete manifest/graph name section before claiming A1; perform duplicate-QID, byte-tampering and missing-object negative controls.
3. **P2 / A2+A3+A4+A6:** bind the exact intended query family, collect the dependency/adjacency neighbourhood, and prove actual source→selected answer equality, overlap compatibility and scoped negatives. ITIR's `evaluate_query_closure` deliberately returns `original_graph_edge_closure_proved=false` even if a caller's listed dependencies were inspected. The stronger witness is still required.
4. **P3 / A5+B4+C2:** decode selected graph relations and record unique physical GETs, bytes, cache/coalescing, concurrency ≤5 and no fallback masquerading as direct fetch; compare same-object v2 against any v3 only with measurements; construct old/new dependency-reopening receipts.
5. **P4 / B5+B6+C3+C4:** connect to original native Wikidata QID+statement GUID+mainsnak+rank+qualifiers+P854+temporal evidence, verify source-correspondence, persist/restart/read S29 and selectively reopen, and replay pinned Agda + Rust/Python checks. A name/graph receipt is not source support.
6. **P5 / C5+C6:** consume a real **Éder Porto NORA** export with preserved review/attribution and independently authorised actions; enumerate full *current* Nat population with a lossless `(QID, GUID)` cursor and exhaustion receipt, independent of historical 57,989 and five-QID calibration.

**Release criterion:** P0–P5 are accepted only when the exact data SHA, named source file/lemma, successful local test/kernel receipt, source-provenance chain, and negative controls are committed or linked per gate. Until then the end-to-end status remains **OPEN**; this tranche advances source-level implementation, not original-graph completeness.
