# Ibrahim First Link Network × ITIR × Hyperfabric — authoritative 15 November 2026 maximum cut

**Single owner PR:** [DASHI/Agda #1505](https://github.com/chboishabba/dashi_agda/pull/1505), branch `feat/ibrahim-fln-ternary-revision-maxcut-20261114`. Companion owners: [ITIR-suite #14](https://github.com/chboishabba/ITIR-suite/pull/14), [SLR #10](https://github.com/chboishabba/slr/pull/10), [SensibLaw #514](https://github.com/chboishabba/SensibLaw/pull/514). **Do not create another rollup PR for this programme.** Separate but interacting golden Zelph [Agda #1506](https://github.com/chboishabba/dashi_agda/pull/1506) is NOT merged into #1505; it owns the different physical original-object proof problem.

**Scientific attribution:** original First Link Network methodology and historical publication: **Mark Ibrahim, Christopher M. Danforth, Peter Sheridan Dodds**, *Connecting every bit of knowledge: The structure of Wikipedia's First Link Network*, *Journal of Computational Science* 19 (2017), DOI [10.1016/j.jocs.2016.12.001](https://doi.org/10.1016/j.jocs.2016.12.001), original author source `marksibrahim/wikipedia_network`. Multilingual comparative publication: **Maxime Gabella**, DOI [10.1109/TNSE.2018.2812788](https://doi.org/10.1109/TNSE.2018.2812788). Sheaf-hypergraph modelling: **Duta et al.**, arXiv:2309.17116. **Éder Porto** owns the external NORA source. Existing DASHI/ITIR/SLR/SensibLaw modules retain their independent original project authorship. New generic mathematical proofs, checkers and adapters in #1505 are DASHI extensions, not retrospectively attributed to those external papers.

## Executive gate matrix: what is verified, what is source-written, what is still genuinely missing

| Gate | Strongest observed acceptance | Current mathematical / physical status | Next acceptance |
| --- | --- | --- | --- |
| **A0 finite graph constructive existence** | User-reported **36/36 Python, eight Agda checks, exit 0** on **exact source head `70babf96e29875e6fa945f1c1528b5a1b3af8277`**; includes all-start finite pigeonhole and generated manuscript cert | **LOCALLY KERNEL ACCEPTED at that exact head** for finite total deterministic graph; no historical Wikipedia source inference | Maintain this receipt; no re-proving prior work |
| **A1 intrinsic terminal cycles / basin classification** | `IbrahimCycleRotationRelationExact.agda` earlier had only conditional rotation witnesses; subsequently expanded in same PR | **SOURCE WRITTEN, NEW-HEAD AGDA OPEN**: arbitrary same-start cycle uniqueness, intrinsic basin equivalence, canonical-root uniqueness conditioned on minimum receipts | Full focused new-head Agda and negative-control suite |
| **A2 typed partial FLN** | Python checker distinguishes null/dead end/unresolved target | **SOURCE WRITTEN, NEW-HEAD AGDA OPEN**: new `IbrahimPartialFirstLinkSemanticsExact.agda` and total-graph embedding | Check three disjoint constructors and absorption/embedding under both pinned Agda versions |
| **A3 checked-trace ↔ graph theory** | Old generated seven-node `refl` proof accepted at `70babf96` | **SOURCE WRITTEN, NEW-HEAD AGDA OPEN**: `IbrahimFiniteTraceCheckerWeldExact.agda`, accepted edge-path → orbit equality → eventual cycle; arbitrary accepted cycle matches finite census up to rotation | Kernel acceptance; separate Python byte-format/parser semantic equivalence still **OPEN** |
| **B1 real Wikipedia source/identity** | Synthetic two-edition candidate hash/span validator and author-parser behavioural port PASS on previous head | **OPEN**: independently authenticated actual two-language wikitext, `oldid`, `pageid`, raw SHA, selected source spans and Wikidata item sitelink records | One genuine same-QID two-edition paired original-source packet |
| **B2 Hyperfabric original adjacency** | Conditional source/stalk Agda contracts and synthetic route/shard tests in owner repos | **OPEN**: same-object original `.bin` range bytes → selected immutable HF shard → native decoded matching source edge | Clean-head ITIR offline roundtrip, then real pinned physical source-range replay |
| **B3 ITIR scoped review/repair** | Synthetic non-descent and preserving-one-consumer Agda proofs, ITIR/SLR/SensibLaw handoff tests | **OPEN**: actual human-reviewed source licence, consumer-specific repair, authorised after-state reparse | Native source-backed reviewed before/after packet with original views preserved |
| **B4 revision transport / S29** | Same-node-carrier all-depth dirty-cone theorem accepted at `70babf96` | **OPEN**: deleted/added/redirected page transport, actual query dependency reopening, native S29 persistence/reload | Physically replay one real revision event and reload source-qualifier evidence |
| **C1 historical corpus reproduction** | Author source and original figure parity, paper-figure seven-node Agda + Python | **OPEN**: November 2014 original dump/decompression/112 chunks/producer revision `fln.json` same-object provenance | Original source-blob hash/source producer/split reconciliation |
| **C2 2026 multilingual census** | Attributed reporting, no downloaded source snapshots | **OPEN**: editions, revisions, cohort coverage, counts, parser/editorial confounders | Reproducible source-pinned comparative corpus and caveated statistical report |
| **Zelph P0–P5 companion** | Golden Agda conditional A1–A6 reported exact-head PASS `4c89edb`; operator **90/90 Python only in corrected local overlay**, old 58+new 32; decoder compilation with `clang++ -fuse-ld=lld` | **OPEN**: clean **ITIR #14 `e64c04f`** native C++ packed roundtrip; original byte-range rehash; A1 all-name partition/A2 query closure; native GUID/P14143/P854; S29; real NORA | `bash tools/check_zelph_physical_maxcut_offline.sh` on a clean checkout, then real `--source-bin` audit |

**Test provenance:** this assistant has independently fetched the current GitHub branch metadata and sources but has **not** executed Agda in its own environment. The successful 36/36 + 8/8 is the user's exact-head local test report. At the start of this tranche, #1505 head was `f619416c2436d927ab590fe5ee7505ccd344a860`; code additions **after** that SHA are source-written and must be checked at the newer final head. The three cross-repo PR heads reported on 15 Nov are ITIR #14 `e64c04f`, SLR #10 `0b0ea6f`, SensibLaw #514 `8187ebb`; all draft/open. No exact-head physical `.bin` acceptance was supplied.

## Batch A — finish all reusable mathematical and certificate obligations together

### A1 intrinsic terminal cycles (golden Agda `IbrahimCycleRotationRelationExact`)

| Exact lemma | New implementation / actual remaining proof |
| --- | --- |
| `mutualOrbitRotationReflexive`, `mutualOrbitRotationSym`, `mutualOrbitRotationTransitive` | **New source written**; establish mutual graph reachability as an equivalence relation |
| `periodicPointEveryOffsetIsMutualRotation` | **New source written**; any finite offset on a point with positive period has a two-way return witness via `*-suc` and `positiveCycleRepeats` |
| `earlierEntryGivesMutualRotation` | **New source written**; compare arbitrary entry times, use the earlier certified period to return from later representative |
| `terminalCycleUniqueUpToRotation` | **New source written**; takes **any** two `EventualCycle next start` objects, does not require caller-provided ordering/period split; **kernel OPEN** |
| `IntrinsicTerminalSameBasin`, `terminalBasinsPartitionByCycle` | **New source written**; basins are classes of mutually reachable terminal representatives, not equality of selected labels |
| `canonicalCycleRepresentativeUnique` | **New source written** under two `CanonicalCycleRoot` minimum receipts and antisymmetric order; does **not** construct the minimum algorithmically |
| `canonicalCycleRootExistsForFiniteDecidableOrder` | **NEW SOURCE WRITTEN** in `IbrahimFiniteCanonicalCycleRootExact.agda`: fold over the complete finite carrier, with a decidable intrinsic cycle-membership predicate and a total antisymmetric/transitive/reflexive order; prove the chosen root is below every member |
| `canonicalCycleChoiceIndependent` | **NEW SOURCE WRITTEN**: compose the finite minimum producer with `terminalCycleUniqueUpToRotation` and `canonicalCycleRepresentativeUnique` for two independent eventual-cycle certificates |

### A2 partial-link semantics (golden Agda `IbrahimPartialFirstLinkSemanticsExact`)

| Exact lemma | Status |
| --- | --- |
| `missingTargetNotDeadEnd`, `activeNotMissingTarget`, `activeNotDeadEnd` | **New source written**; constructors disjoint |
| `partialDeadEndAbsorbs`, `partialUnresolvedAbsorbs` | **New source written**; terminal observations do not become fabricated graph self-loops |
| `totalGraphEmbeddedIntoPartial`, `totalGraphCannotCreateMissingTarget`, `totalGraphCannotCreateDeadEnd` | **New source written**; exact functorial compatibility with old total `Orbit.iterate` |
| `finitePartialFLNClassifiesOrTerminates` | **OPEN**: classify arbitrary finite non-total FLNs into cycle/dead-end/outside-target while preserving optional target provenance |
| `partialSourceSelectionMatchesAuthorParser` | **OPEN**: requires independent revision/source/parser packet and an actual source-backed first-qualified-link proof |

### A3 proof-level trace ABI (golden Agda `IbrahimFiniteTraceCheckerWeldExact`)

| Exact lemma | Status |
| --- | --- |
| `CheckedEdgePath`, `pythonTraceStepMatchesAgdaIterate` | **New source written**: an accepted per-edge equality trace corresponds to the original graph `iterate`. The name does not mean the Python implementation was proved correct |
| `agdaIterateEmitsCheckedPath`, `AcceptedCycleTrace` | **New source written**: construct exact typed finite edge-chain witnesses |
| `acceptedTraceImpliesEventualCycle`, `acceptedTraceImpliesOrbitRepeat` | **New source written**: accepted graph proof → canonical owner theorems |
| `eventualCycleEmitsAcceptedTrace`, `certificateGenerationCompleteForFiniteTotalGraphs` | **New source written**: total deterministic finite graph admits an accepted proof-carrying trace |
| `terminalCensusMatchesCertificateUpToRotation` | **New source written**: any checked cycle agrees with automatic pigeonhole census intrinsically, even if the certificates choose different representatives |
| `pythonJsonCertificateDecodesToCheckedEdgePath` | **OPEN**: actual JSON shape, bytes, index ordering, destination ID and parser correspondence; no trusted import of unverified source objects |
| `pythonCertificateCheckerSoundAndComplete` | **OPEN**: formalize/check implementation semantics or a verified extraction; a generated file with `refl` checks graph algebra for that object but does not verify the Python program globally |
| `boundedGeneratedCertificateKernelReceipt` | **PARTIAL**: user earlier accepted seven-node generated figure; run the new exact-head focus suite including the two additional modules |

**Batch A release deliverable:** (a) all new source modules kernel-accepted at one exact SHA; (b) one *intrinsic* cycle/basin theorem, (c) partial-source separation, (d) proof-level trace semantics, and (e) explicit list of unproved minimum existence and Python-implementation equivalence. No source theorem should be credited on textual existence alone.

## Batch B — physical original-object witness chain, not adjacent abstract theorems

### B1 original Wikipedia revision and parser receipt (owner SensibLaw + ITIR; golden DASHI)

`wikiRevisionSourceBytesVerified` → `wikidataSitelinkIdentityVerified` → `historicalFirstQualifiedLinkSound` → `selectedEdgeHasRevisionSpanReceipt` → `actualSelectedEdgeProjectsToFirstLink` → `pageIdentityTransportPreservesConsumerQuery`.

**Acceptance:** original two-edition `oldid`, `pageid`, revision text bytes and hash, originating page URLs and independent Wikidata item/sitelinks; exact qualifying link spans and parser policy under the *original* source-linked selection algorithm. Reject synthesized titles/QIDs, generic reviewer strings, author-code port parity assumptions and unknown-as-signed-zero.

### B2 independent HF original immutable source bytes (owner ITIR #14, companion Agda #1506)

`originalBinRangeMatchesImmutableHFShard` → `nativeCapnpDecodedSectionEqualsOriginal` → `originalAdjacencyMatchesPublishedManifest` → `selectedEdgeHasPhysicalIncidenceWitness` → `queryProjectionUsesExactlySelectedAdjacency` → `incidenceAndRestrictionCompatibleForSelectedEdge` → `trajectoryTritEncodingInjectiveOrResidual` → `alignedPrefixDepthSound`.

**Source acceptance sequence:**

1. Clean **ITIR #14** `e64c04f` offline `tools/check_zelph_physical_maxcut_offline.sh` (90 Python tests, native writer/reader packed Cap’n Proto roundtrip and tampering negatives). **OPEN**.
2. Fetch (or locate) the actual immutable source `.bin`, full manifest and actual selected source ranges; independently rehash **original bytes**, exact offsets, lengths, source URLs, HTTP 206 range results, shard names and SHA—not a caller's JSON claim. **OPEN**.
3. Native decode *matching physical originals*; prove A1 complete declared name partition and A2 first-hop adjacency/query-family answer equality on the **same** pinned graph. **OPEN**.
4. Bind the resulting source-backed edge to an actual Wikipedia revision span. Zelph's general QID/graph route must not be mistaken for the article's first qualifying link. **OPEN**.

If any original immutable object is missing or the server rejects ranges, preserve a **blocked** receipt. No automatic fallback should be recorded as proof of the requested original route.

### B3 selected-consumer repair (DASHI prior art, ITIR and SensibLaw owner)

`firstLinkCollisionIsConsumerNonDescent` (synthetic prior art) → `qidAlignedTrajectoryComparisonSound` (real data) → `reviewedAlignmentPaysSelectedConsumer` (authorised human review) → `consumerObservablePreservedByEvidenceScopedLicence` (reuse existing `EvidenceScopedHeterogeneousLicence`) → `firstLinkRepairRetainsOriginalView` → `firstLinkRepairPaysSelectedConsumer` → `firstLinkRepairDoesNotPayAllConsumers` → `reviewedRepairRerunSound`.

**Acceptance:** real two-language before/repaired candidate/after query packet, honest review state, original source views preserved, typed signed/rejected/unresolved comparison evidence. No claim of translation semantic equivalence, global adequacy or edit authority from a local repair.

### B4 native revision and persistence (ITIR/SLR/SensibLaw)

`oldReverseClosureContainsAllChangedTerminals` → `queryProjectionInvariantOutsideDirtyCone` (same-carrier proved prior) → `pageIdentityTransportPreservesConsumerQuery` → `repairedTranslationReopensOnlyAffectedDependents` → `s29RevisionEvidencePersistedExact` → `reloadedRepairRerunSameObservation`.

**Acceptance:** actual before/after revision event, exact old reverse-closure impacted dependents, no spurious reopening outside closure, persisted/reloaded `(QID, GUID, rank, P14143, P854, qualifier, revision, source-span)` witness, identical selected consumer query after reload. No selected HF shard test alone pays this.

## Batch C — empirical reconstruction (distinct scientific objects)

- `originalDumpChunkLineageSameObject` — original historical Wikimedia dump exact bytes, decompress/split ancestry, 112 source producer chunks and verified release graph.
- `producerExtractionMatchesReleasedMap`, `historicalProducerPolicyParity`, `publishedFunnelCountsMatchProducerVersion`, `originalPublishedCensusReplayReceipt` — run original author code/version and compare fully published statistics, separating early pseudocode from corrected cycle-entry implementation.
- `modernLanguageCensusReproduced`, `alignedCycleBasinComparisonCoverageBound`, `parserAndRevisionSensitivityConfounderAudit`, `culturalCauseNotDeductibleFromFLNAlone` — new edition- and revision-pinned snapshots, coverage denominators, quantified sampling/editing/parser sensitivity, no cultural causal leap.

**Release gate:** historical original-object replay and contemporary datasets are distinct. A hash of data supplied by the caller is not independent acquisition/source provenance.

## Batch D — exact-head acceptance, one PR per repo

| Owner | Existing PR | Run / deliverable |
| --- | --- | --- |
| DASHI golden | [#1505](https://github.com/chboishabba/dashi_agda/pull/1505) | `git rev-parse HEAD && NO_TMUX=1 ./scripts/check_ibrahim_fln_maxcut.sh`; prior 8/8 verified checks plus new rotation, partial, trace and finite minimum mathematical sources: currently **11 source modules + one generated = 12** (exact focused script checked); compiler receipts after new mathematical edits **OPEN** |
| DASHI Zelph golden | [#1506](https://github.com/chboishabba/dashi_agda/pull/1506) | Exact previously checked conditional A1–A6 source at `4c89edb`; physical instantiation by original decoded graph remains **OPEN** |
| ITIR | [#14](https://github.com/chboishabba/ITIR-suite/pull/14) | `bash tools/check_zelph_physical_maxcut_offline.sh` **clean head** then `--source-bin` physical audit; real A1/A2 route and query closure **OPEN** |
| SLR | [#10](https://github.com/chboishabba/slr/pull/10) | `cargo test -p sensiblaw-source-handoff`, native GUID/qualifier/P854 crosswalk and S29 persist/reload **OPEN** |
| SensibLaw | [#514](https://github.com/chboishabba/SensibLaw/pull/514) | `pytest -q tests/test_wikidata_nora_review_handoff.py`, original source review/evidence/handoff **OPEN** |

**No-op/negative controls:** any source-missing, wrong-revision, absent `oldid`, nonmatching selector, QID collision, false local reviewer, capnp appended data, wrong immutable chunk index, incorrect original-byte offset, absent original `.bin`, unknown/neutral conflation or insufficient consumer licence **must fail closed** with retained evidence and typed residual. No passing synthetic test, conditional Agda theorem, human-readable name match or model inference can independently pay these original-object gates.

## Concrete finish line

**Deliverable 1:** Agda proves finite orbits, intrinsic terminal-cycle equivalence and trace semantics for total graphs, preserving partial-source distinctions. **Deliverable 2:** one genuine independently acquired wiki article pair with source-bytes/editions, parser-selected first links and query-specific consumer repair. **Deliverable 3:** original physical native HF/ITIR/SLR join, exact revision selective reopening and persisted/reloaded reviewed result. **Deliverable 4:** separate reproducible original 2014 and contemporary comparative census. Close a gate only with the exact accepted source commit, kernel/log evidence, original-byte provenance and negative controls.

This page is the **current authoritative status/lemma matrix**; earlier chronology and detailed source archaeology remain preserved in [`IbrahimFLNITIRTernaryHyperfabricMaxCut20261114.md`](IbrahimFLNITIRTernaryHyperfabricMaxCut20261114.md). Those appendices may describe older unverified heads and must not override this matrix.

## Final A2 minimum-producer extension — source implementation, pending kernel

New `DASHI/Wikimedia/IbrahimFiniteCanonicalCycleRootExact.agda` introduces `FiniteTotalOrder`, `LeastFromSeed`, `leastFromFiniteList`, `canonicalCycleRootExistsForFiniteDecidableOrder`, and `canonicalCycleChoiceIndependent`. This is a **constructive finite fold**, not a least-element axiom: the seed is the base periodic vertex, `decideCycle` determines which enumerated vertices are on its intrinsic cycle, and each comparison retains a proof that the current candidate is `≤` all accepted candidates. Coverage of `General.CompleteFiniteCarrier` lifts the minimum to every candidate in `Node`.

**Boundary:** source written; new-head Agda acceptance is pending. A decision procedure `finiteCycleMembershipDecidableFromFinEquality` remains **OPEN**; it would search bounded original-graph orbits under an explicitly decidable equality of vertices. Neither a Wikidata QID nor a title order establishes that decision or source attribution. The separate unsolved proof-relevance/semantic Python decoder contract and all physical HF, S29 and real Wiki source gates remain OPEN.

**Current exact acceptance count from focused script:** eleven explicit source modules (`IbrahimFiniteOrbitRevisionWeldExact`, `IbrahimMultilingualHyperfabricWeldExact`, `IbrahimPublishedSevenNodeFunnelExact`, `IbrahimGeneralFiniteCertificateKernelExact`, `IbrahimFinitePigeonholeProducerExact`, `IbrahimCycleRotationRelationExact`, `IbrahimPartialFirstLinkSemanticsExact`, `IbrahimFiniteTraceCheckerWeldExact`, `IbrahimFiniteCanonicalCycleRootExact`, `IbrahimFiniteFigureBasinCertificateExact`, `IbrahimITIRConsumerRepairExact`) plus one dynamically generated `GeneratedIbrahimFigureCertificateExact`. Previous `8/8` pass is deliberately not promoted to `12/12`.
