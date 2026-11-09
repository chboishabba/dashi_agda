# JMD × DASHI image-owner archaeology and formal bridge roadmap

**Date:** 2026-11-09. **Status:** planning and repository-search evidence, NOT kernel certification. **Golden formalism:** `chboishabba/dashi_agda`. **Companion:** `chboishabba/dashi_lean4`. **Source attribution:** JMD/meta-introspector/SOLFUNMEME; imported Aristotle/Harmonic, AxiomMath, Popov, TauCeti and original contributors as applicable.

## Operating rule

**P0 is discovery and reuse, not theorem creation.** Each JMD image is a hashed source/reference object. It is not a proof or permission to publish the source image. Link `image SHA-256 → depicted claim → exact existing Agda declaration → theorem prerequisites → verification receipt → source attribution`. A module filename proves only discoverability; it does not establish declaration-level parity or Agda 2.9 --safe acceptance. Never silently turn a source screenshot, historical quote, artistic visual, receipt, computational check or imported postulate into a stronger mathematical theorem.

## Phases, deliverables and exit conditions

| Phase | Deliverables | Exact exit gate |
|---|---|---|
| **P0A: image source ledger** | stable image IDs, SHA-256, filenames, motif/topic, JMD attribution, upstream licence/publication status | every byte-backed image indexed; repeated images deduplicated by exact digest; missing originals explicit |
| **P0B: find all existing Agda owners** | complete image→claim→candidate module→exact declaration crosswalk; near-duplicate searches; ownership tiers | every distinct claim classified as existing exact, partial, no owner, non-mathematical/visual, or external runtime |
| **P0C: locate Lean corpus** | JMD-supplied GitHub Lean search, separate starred-repo view, reproducible export/partitions | search source resolved; complete stable enumerated corpus is a separate open gate |
| **P1: three external library comparisons** | AxiomMath/CFSG, AxiomMath/Stacks, Fedor-Popov/Lean_VOA; selected TauCeti Hecke declarations | precise source revisions, theorem signatures, assumptions and ownership matches |
| **P2: verified bridges** | selected same-object Agda/Lean proof transports, Hecke/sorting/FRACTRAN/compiler evaluation squares | Agda kernel and Lean checks pinned to named commits, no undocumented axioms |
| **P3: runtime** | Blaze page DAG/source reconstruction, SLR/ITIR/Lean index, Rust JIT conformance observations | byte-for-byte round trip, negative controls, recorded executable versions |
| **P4: human interface** | prove-or-open theorem cards, source attribution, image/game dashboard proof links | users can distinguish exact theorem, executable test, conjecture and metaphor |

## P0B owner-discovery catalogue

**Status meaning:** `FOUND` = indexed path found; `PARTIAL` = related constructions not guaranteed equivalent; `OPEN` = specific proof/reconciliation missing. Search evidence from indexed `chboishabba/dashi_agda`, reported revision `314c7dc1741239518525891d7813aa7b0df63fea`; re-check actual branch HEAD and native Agda preflight before promotion.

| Group | JMD image IDs / concept | Existing first owners (all paths relative to dashi_agda) | Standing |
|---|---|---|---|
| G01 | 006,013–017,021,023,026: Hecke weight-12 T3/T9, tau, coefficient visual paths | `DASHI/Moonshine/ClassicalHeckeWeightKSmallWordExact.agda`; `DASHI/Moonshine/RamanujanTauHecke23Exact.agda`; `DASHI/Moonshine/AristotleHeckeRecurrenceCoreExact.agda`; `DASHI/Moonshine/AristotleHeckeWordsSourceParityExact.agda` | FOUND; visual-coordinate interpretation OPEN |
| G02 | 038,033: squarefree and repeated-prime correction | `DASHI/Moonshine/AristotleHeckeGeneralPrimePowerDecompositionExact.agda`; `DASHI/Moonshine/AristotleHeckeGeneralZeroUpdateExact.agda`; `DASHI/Moonshine/AristotleHecke23Smooth3ParityExact.agda`; `DASHI/Arithmetic/CoprimeLayer.agda`; `DASHI/Interop/AristotleMathSourceParityExact.agda` | FOUND; DO NOT reprove multiplicativity |
| G03 | 022, plus syntax/laws/handlers image missing byte-backed file: sparse tensor compiler, sorting, 0-Hecke | `DASHI/Programmes/FRACDASHCompilerCorrectionExact.agda`; `DASHI/Computation/SSSPSortingBarrierTernaryBidiExact.agda`; `DASHI/Combinatorics/FractranComputationEquivalence.agda`; `DASHI/ComputerScience/HelloWorldFibreExact.agda` | PARTIAL; precise 0-Hecke/free-monad owner not confirmed |
| G04 | 003,019: Grothendieck construction, K0 | `DASHI/Reasoning/TrialecticGrothendieckTransportCoherenceExact.agda`; `DASHI/Foundations/RelationalStageTwelveGrothendieckExtensionExact.agda`; `DASHI/Reasoning/TrialecticGrothendieckTransitionCocycleExact.agda`; `DASHI/Physics/Closure/BottIncompleteCarrierKTheoryReceipt.agda` | PARTIAL; K0 group completion is distinct from Grothendieck construction |
| G05 | 001,018: prime pantheon / ontological grounding | `Ontology/Hecke/FactorVecCorrespondence.agda`; `Ontology/Hecke/PrimeHeckeEigenMotifPipeline.agda`; `DASHI/Reasoning/SFMVerifiedClaimPresentation.agda`; `DASHI/Unified/InvariantSpine.agda` | RELATED; mythology/quotation is not proof |
| G06 | 008–012: Monster, Kiro/Y443, VOA, 196884, 13-cycle | `DASHI/Moonshine/Monster196884FibreInterferenceExact.agda`; `DASHI/Moonshine/MonsterGradedVOABridgeExact.agda`; `DASHI/Moonshine/VertexOperatorAlgebraCore.agda`; `DASHI/Moonshine/JMDMonsterRepresentationCrossPollinationMaxCutExact.agda`; `DASHI/Physics/Closure/MonsterVOAFixedPointReceipt.agda` | FOUND/PARTIAL; nonabelian kernel & original Monster action OPEN |
| G07 | 002,025: Blaze dedup, page DAG, JIT | `DASHI/Core/ContentAddressedTransitionIdentityExact.agda`; `DASHI/Reasoning/ContentAddressedVerificationBridgeExact.agda`; `Verification/SourceHash.agda`; `DASHI/Reasoning/JMDAristotleSymposiumRegression.agda` | RELATED; deployed Rust runtime not verified by Agda spec |
| G08 | 027,028: Hilbert defence, self-adjoint, spectral gap | `DASHI/Quantum/SelfAdjointGenerator.agda`; `DASHI/Quantum/SelfAdjointColimitGenerator.agda`; `DASHI/Physics/YangMills/BalabanOSMassGapClosure.agda`; `DASHI/Physics/YangMills/YangMillsClayPinnedCMP119OSSystemExact.agda` | RELATED; full physical OS gap OPEN |
| G09 | 024: prime-tower game, FRACTRAN, divisors | `DASHI/Combinatorics/FractranComputationEquivalence.agda`; `DASHI/Mathematics/NumberTheory/FiniteDivisorSumExact.agda`; `DASHI/Mathematics/NumberTheory/FiniteProductCardinalityExact.agda`; `DASHI/Programmes/FRACDASHCompilerCorrectionExact.agda` | PARTIAL; gameplay semantics not identified |
| G10 | 004,005,020,034–036: forks, Omarchy, service registry | `DASHI/Reasoning/ContentAddressedVerificationBridgeExact.agda`; `DASHI/Interop/ABIVerticalLiftBoundary.agda` | no exact OS owner asserted; cultural/ops claims |
| G11 | 007: newspace Hecke characters | `DASHI/Moonshine/ClassicalHeckeWeightKSmallWordExact.agda`; `DASHI/Moonshine/SSPRepresentationHeckeIntertwinerBoundaryExact.agda`; `DASHI/Physics/Closure/HeckeCorrOnX021Receipt.agda` | PARTIAL; original level/nebentypus hypotheses not reconciled |
| G12 | 029,037,039,040: cosmic artwork, portraits, symbolism | `DASHI/Reasoning/SFMVerifiedClaimPresentation.agda` | presentation only; no invented theorem |

**Inventory note:** physical image IDs follow the filenames in the SHA-256 manifest, **not** the ordinal order in a prior chat. IDs 030–032 lack available original image bytes. The later six repeated images 033–038 matched their earlier originals by SHA-256: no duplicate identities.

### Existing precise Hecke owners

`DASHI/Interop/AristotleMathSourceParityExact.agda` already records substantial prime-power recurrence uniqueness, coprime assembly, small 2/3 examples and an explicitly **partial** source-parity frontier. Reuse these first; the remaining tasks are full `Nat` `HeckeSystem` packaging, canonical grouping of repeated raw prime factors into prime-power blocks, and a finite separating bound. Prime-power recurrence and selected `T_9=T_3^2-3^{k-1}` are not novel work.

## Exact remaining proof/receipt cut (proposed names, not claims of existing declarations)

| Gate | Exact target | Status |
|---|---|---|
| P0A.01 | `imageDigestIdentifiesSameBytes` with source identity, custody and licence receipt | OPEN for repo integration; local hashes computed |
| P0B.01 | `eachImageClaimClassifiedAgainstExistingAgdaOwner` (ledger coverage, not a mathematical axiom) | OPEN |
| P0B.02 | `indexedCandidateOwnerHasExactDeclarationAndAssumptions` | OPEN |
| P0B.03 | `noDuplicateHeckeProofIntroduced` source regression | OPEN |
| P0C.01 | `leanCorpusPartitionCoverage` and `repositoryIdDedupCorrect` | OPEN |
| P0C.02 | `leanCorpusCommitLicenseProvenance` | OPEN |
| P1.01 | `cfsgSelectedActionOriginalKernelMatch` | OPEN |
| P1.02 | `leanVOASelectedAllModeStructureCorrespondence` | OPEN |
| P1.03 | `stacksGrothendieckIndexedFibreCorrespondence` | OPEN |
| P1.04 | `originalK0ProjectiveModuleGroupCompletion` | ownership / proof OPEN |
| P1.05 | `newspaceHeckeCharacterAssumptionParity` | OPEN |
| P2.01 | `originalHeckeNatCoprimePackaging` | source parity OPEN |
| P2.02 | `rawPrimeFactorsGroupedIntoPrimePowerBlocks` | source parity OPEN |
| P2.03 | `generalHeckeFiniteSeparatingBound` | source parity OPEN |
| P2.04 | `zeroHeckeWordInterpretationRespectsIdempotentCommutationBraid` | OPEN |
| P2.05 | `sortingWordSameValuePreservesOutputNotCost` | OPEN |
| P2.06 | `selectedFractranSourceStepExecutionCommutes` | existing related owners; exact JMD bridge OPEN |
| P3.01 | `blazePageDagReconstructsOriginalBytes` | runtime OPEN |
| P3.02 | `blazeDedupPreservesDistinctSourceIdentity` | runtime OPEN |
| P3.03 | `jitExecutionMatchesSelectedVerifiedSemantics` | runtime OPEN |
| P4.01 | `gameObservationMatchesCheckedArithmetic` | runtime OPEN |

## JMD's Lean corpus — source located; export open

- **Global search supplied by JMD:** https://github.com/search?q=lang%3Alean&type=repositories&s=updated&o=desc ; user reported approximately **17,900** results on 2026-11-09. This is a mutable GitHub-wide language filter, not a frozen curated list.
- **Separate personal stars:** https://github.com/jmikedupont2?language=lean&tab=stars ; JMD estimated 1,242 starred Lean repos on 2026-11-08.
- **Earlier conversational estimate:** ~21,000 GitHub Lean repos. Counts represent distinct scopes and times.
- **Canonical sources issue:** https://github.com/meta-introspector/solfunmeme-metameme/issues/1 (reference links, not the complete Lean repo manifest).
- For reproducibility: recursively partition GitHub searches by `created:` intervals so each partition has at most 1,000 results (GitHub Search API ceiling); paginate, retain all raw payloads, de-duplicate stable GitHub numeric IDs, record UTC retrieval, search parameters, revision/HEAD, licence, language, archived/fork state, and errors. Sorting only by updated date is not a snapshot.
- **Do not claim** the 17.9k corpus has been downloaded, indexed, or kernel checked. The stars exporter is a distinct subset tool, not a global corpus crawler.

## Attribution / governance

1. Keep original `sha256` of unmodified uploaded image bytes; reference immutable hash rather than renaming/reuploading visual files. Hash proves byte identity, **not** original authorship, licence or mathematical truth.
2. Default `origin = JMD-provided`; preserve JMD/meta-introspector/SOLFUNMEME. Cite original authors for imported declarations and downstream editors. Identify independent DASHI additions separately.
3. Preserve publication constraints on unpublished DASHI material (especially Yang–Mills). A public roadmap may name abstract gaps without leaking private or unpublished proof terms.
4. Distinguish evidence statuses `FOUND`, `KERNEL`, `REUSED`, `BRIDGED`, `OBSERVED`, `ATTRIBUTED`, `OPEN`. Do not treat a passing browser screenshot or historical quote as kernel evidence.
5. No unsolicited migration from Agda to Lean: the Agdas are the golden, Lean is a selected external source and interoperability lane.
6. Keep current ESD surfaces untouched; reuse existing imports; no CI dependence for local verification; no Docker requirement.

## 2026-11-09 correction: formal-first worlding and AO reconciliation

**Priority correction:** Agda and Lean source declarations and checked proofs are **the primary/sole mathematical substrate**. Do **not** put SLR, PNF, embeddings, Rust, dashboards, or language-as-algebra extraction in the critical path to mathematical matching. Those are optional projections and indexes. The programme is **link → cross-pollinate → deduplicate → world** all source declarations, while preserving the difference between exact equality, definitional equality, proven equivalence, implication, reuse, conjectural analogy, and source-only resemblance.

The objective is a provenance-indexed **formal declaration world**, not a flat list of repositories:

`source repo + revision + file + declaration + type + universe parameters + hypotheses + axioms + imports + proof status`
→ typed edges (`dependsOn`, `definitionallyEqual`, `provedEquivalent`, `implies`, `isTransportOf`, `sameSource`, `suggestedAnalogy`, `refutes`)
→ reusable mathematical objects / explicit residual goals.

**No semantic equivalence from hashes alone:** repository ID identifies a GitHub repository; blob SHA identifies bytes; declaration fingerprints identify normalized syntax only relative to an explicitly recorded Lean/Agda version, imports, elaboration context and normalization protocol. They cannot establish theorem equivalence without checked correspondence.

### AO owners to reuse in Agda before introducing interfaces

| Existing owner | Intended use |
|---|---|
| `DASHI/Core/ProofDebtRouterExact.agda` | classify the outstanding result: mathematics, formalization, source parity, missing data, or already-owned dependency |
| `DASHI/Interop/ProofArchaeologyCoarseFineAdapterExact.agda` | coarse candidate identification followed by exact statement and hypothesis checks |
| `DASHI/Interop/CrossLaneProofArchaeologyLedgerExact.agda` | source-specific proof-owner ledger |
| `DASHI/Core/DependencyDerivedMinimalInvalidationBidiExact.agda` | affected dependents only when new proofs or revisions arrive |
| `DASHI/Core/DependencyWeightedDiagnosisSchedulerBidiExact.agda` | prioritise shared blocker discharge |
| `DASHI/Reasoning/AristotleSelectiveImplicationReopeningExact.agda` | selective implication/certificate reopening |
| `DASHI/Interop/BroadMathProvenanceDependencyGraphExact.agda` | mathematical dependency and attribution graph |
| `DASHI/Wikimedia/JmdLeanIntegratedMachineLineageExact.agda` | JMD source and cross-prover lineage |
| `.autonomous-orchestrator/registry.json` | reuse assigned worker owners; no new orchestration substrate |

These are **located source files**, not assertions of ready-made whole-corpus support. Kernel check and inspect their precise reusable signatures before extending anything.

### Updated priorities and exact deliverables

- **P0:** finish image→Agda declaration ownership; pin and validate both Lean corpus exports; inventory existing `dashi_agda` and `dashi_lean4` declarations and corresponding provenance.
- **P1:** build declaration-level import/assumption/proof-dependency edges directly from elaborated Lean and parsed/checked Agda. Avoid treating repo names, theorem names, or README descriptions as proofs.
- **P2:** partition duplicate claims into `same bytes`, `same AST under context`, `same mathematical statement`, `one implies other`, `transport with proof`, or `unverified candidate`. Keep all source identities and licenses.
- **P3:** world the connected components: canonical mathematical referent (where justified), every original declaration, exact transport paths, unsatisfied hypotheses and affected downstream lemmas. Never quotient by an unproved equivalence.
- **P4:** AO search and reuse across components, trace shortest justified proof dependencies, select highest shared missing lemma, then kernel-check in the owner language. Agda adjudicates DASHI; Lean adjudicates source Lean. The cross-prover relation itself needs an explicit theorem/interpretation check.
- **P5:** optional SLR/PNF/Blaze interfaces for presentation/navigation and runtime observation, **not** formal-proof authority.

**Exact remaining bridge contracts (proposed signatures, not discharged lemmas):**
`leanDeclarationExtractMatchesElaboratedType`;
`agdaDeclarationExtractMatchesKernelCheckedType`;
`assumptionClosurePreservedUnderCrossLanguageBridge`;
`sameNormalizedSyntaxRequiresSameContext`;
`provedEquivalentDeclarationsCanBeSafelyWorlded`;
`unprovedAnalogyNeverPromotedToEquivalence`;
`sourceProvenanceSurvivesWorldDedup`;
`foreignProofDischargesOnlyMatchedGoal`;
`minimalDependencyReopeningAfterCorpusUpdate`;
`existingOwnerDominatesNewConstruction`.

### Live corpus correction

At this tranche, JMD's **starred repositories** export is reported committed in `dashi_lean4` PR #105 with **8,764** total and **1,996** Lean-primary-language starred repositories. The **independent GitHub-wide** Lean search displayed **20.4k** results in the user's latest observation; the separately running partitioned collector had previously reported **16,604** unique entries at 178 pages / 27 partitions. These are distinct observation instants/scopes, not a discrepancy that may be erased by changing one count into the other. GitHub search results are mutable.

### First-page GitHub-wide Lean triage (2026-11-09)

These ten repositories were located as public, non-archived GitHub repositories. This is **repository discovery only**; no theorem signatures, Lean build receipts or mathematical equivalences are asserted.

| Repository | Candidate formal-work lane | Next evidence required |
|---|---|---|
| `VladimirMarko/conaled` | unknown pending source inspection | inspect `lakefile`, declarations and domain |
| `itakura-hidetoshi/4d-mass-gap` | candidate Yang–Mills / mass-gap comparison | inspect exact 4D hypotheses and independence of source proofs; no Clay promotion |
| `TauCetiProject/TauCetiRoadmapJobs` | roadmap/worker coordination | distinguish task metadata from verified Lean declarations |
| `grwtsk/math` | mathematical discovery/provenance | pin actual theorem statements, proof status and imports |
| `emberian/minidregg` | zk/fhe/effect semantics candidate | inspect exact structures and theorems |
| `the-omega-institute/trureturing` | automated discovery and proof frontiers | inspect checked theorem objects versus discovery metadata |
| `scottnarmstrong/KAM-dev` | KAM analytic dynamics | discover exact positive-measure KAM lemma signatures |
| `TauCetiProject/TauCetiRoadmap` | human/AI Lean task routing | keep roadmap tasks distinct from proof declarations |
| `Verified-zkEVM/PolyFun` | polynomial functors, interaction trees, algebraic effects | direct high-alpha match candidate for JMD syntax/laws/handlers; theorem-by-theorem comparison required |
| `SolidiKeY/solidity-lean` | executable semantics and formal compiler contracts | identify language semantics/verified correspondence, not runtime claims |

**Highest-alpha first-page cross-pollination candidate:** `Verified-zkEVM/PolyFun` ↔ JMD's program syntax/laws/handlers ↔ existing DASHI program-semantics/effects machinery. **Highest-risk overclaim:** `itakura-hidetoshi/4d-mass-gap` is only a candidate comparison; repo name cannot discharge YM E1/D1/D2/N1/G1.

Reference: https://github.com/search?q=lang%3Alean&type=repositories&s=updated&o=desc . User-provided 20.4k display is not a stable GitHub-wide count.


## 2026-11-09 formal-world completion cut — privacy-preserving, declaration-first

**Scope:** Only formal Agda/Lean sources and mathematical dependencies belong in the critical path. The GitHub-wide search landing page (20.4k dynamic matches reported 2026-11-09) was an *illustrative sample*, **not** a task to evaluate or contact each recently updated repository. In particular, `itakura-hidetoshi/4d-mass-gap` is not an approved collaboration target or evidence of resolving a Clay gap. **Do not open external PRs, file external issues, message external maintainers, upload unpublished DASHI material, or push private work to third-party repositories.** Internal source comparisons must respect authorship and repository visibility. Public PRs may contain source pointers and generic interfaces, but not unpublished mathematical content.

### Phase gates: formal mathematical world, not metadata index

| Phase | Deliverable | Acceptance tests / exact remaining result | Status |
|---|---|---|---|
| **F0: sources** | Immutable image-to-claim pointers; Agda/Lean repo+commit inventory, independent starred/global corpus imports | F0.1 `allJmdImageClaimsHaveOwnerOrOpenClassification`; F0.2 `starsManifestRepoIdsUnique`; F0.3 `globalLeanPartitionReceiptsComplete`; F0.4 `sourceVisibilityAndAttributionPreserved` | images and starred export available, global full export and exact image declarations OPEN |
| **F1: declarations** | Versioned Lean and Agda declaration inventories with elaborated type, universe parameters, parameters/implicit instance assumptions, axioms, import closure and declaration/term identifiers | F1.1 `leanDeclarationIndexFaithfulToPinnedKernelEnvironment`; F1.2 `agdaDeclarationIndexFaithfulToPinnedKernelEnvironment`; F1.3 `declarationImportClosureSound` | OPEN |
| **F2: typed edges** | Direct formal dependencies and candidate cross-library edges; distinguish verbatim duplicate, definitional equality, mathematical equivalence, implication, interpretation, and analogy | F2.1 `edgeKindDoesNotPromoteUnprovedCandidate`; F2.2 `directImportDependencyEdgesAreSourceFaithful`; F2.3 `crossProverTranslationPreservesAssumptions` | OPEN |
| **F3: dedup/world** | Shared mathematical referents only after proof; preserve multiple proofs, licenses, and declarations as separate source identities | F3.1 `provedEquivalenceWorldingIsCongruent`; F3.2 `distinctProofAndProvenanceNotCollapsed`; F3.3 `unverifiedCandidateNeverDefinesQuotient` | OPEN |
| **F4: AO max-cut** | Existing-owner lookup followed by proof-debt classification, dependency cone computation, shared missing-lemma selection | F4.1 `ownerFirstNoUnnecessaryReproof`; F4.2 `proofDebtRoutingRespectsCertificateStatus`; F4.3 `minimalDependencyReopeningPreservesUnaffectedNodes`; F4.4 `chosenGapHasExplicitDownstreamConsumers` | partial prior AO modules, corpus instantiation OPEN |
| **F5: certified transports** | At least one end-to-end selected Hecke witness and then Monster/VOA/Karp/categorical target comparison | F5.1 `selectedHeckeCrossRepoStatementParity`; F5.2 `selectedHeckeTransportKernelChecked`; F5.3 `negativeControlDistinguishesNonEquivalentStatements`; downstream open lemmas separately tracked | OPEN |
| **F6: optional projections** | SLR/PNF/Blaze/game navigation of the *already checked* world | F6.1 `projectionDoesNotBecomeProofAuthority` | DEFERRED |

All `F*.x` names above are **proposed new integration contracts**, not existing checked declarations. Avoid writing dozens of wrappers: each should be an actual lemma or a concrete ingestion/runtime acceptance predicate, with its source evidence specified.

### Existing AO theorem owners and exact reuse points

- `DASHI/Core/ProofDebtRouterExact.agda`: `routeDebt`, `sourceEstablishedAlignedDeferredIsCertificationDebt`, `sourceEstablishedAlignedDeferredIsNotMathematicalDebt`, `SourceIdentity`, `StatementAlignmentReceipt`, `FullyAligned`, `SourceAlignedDeferredTheorem`, `CertifiedKnownTheorem`. **Do not treat a source receipt as an inhabitant of the target theorem.**
- `DASHI/Interop/ProofArchaeologyCoarseFineAdapterExact.agda`: `proofAnchorReopenExact`, `proofAnchorObserverSeparating`, `surfacePlusResidualDeterminesAnchor`. The coarse view is not enough without the fine historical/provenance residual.
- `DASHI/Interop/CrossLaneProofArchaeologyLedgerExact.agda`: `IdentityStatus` (`sameObjectProved`, `structuralAncestor`, `candidateAlias`, `notSameObject`, `unresolvedIdentity`) and `PaymentStatus` (`paid`, `conditionalPayment`, `unpaid`, `notApplicable`); canonical Ibrahim policy favours explicit owner → typed dependency → typed generalisation. **Adapt** the typed classification, do not pass unproved candidate aliases as same-object proofs.
- `DASHI/Core/DependencyDerivedMinimalInvalidationBidiExact.agda`: `AffectedSemanticAxis`, `derivedExplicitInvalidation`, `derivedInvalidationIsContainedInEveryCover`, `canonicalMinimalInvalidationReceipt`.
- `DASHI/Core/DependencyWeightedDiagnosisSchedulerBidiExact.agda`: `DependencyPriorityPolicy`, `WeightedDebugCandidate`; dependency weight is declared priority, **not** truth/confidence probability.
- `DASHI/Reasoning/AristotleSelectiveImplicationReopeningExact.agda`: `semanticChangeReopensAristotleSearchPolicy`, `semanticChangeReopensAristotleActionTransitively`, `reopenableNotRefuted`, `reopenableNotProved`.
- `DASHI/Wikimedia/JmdLeanIntegratedMachineLineageExact.agda`: `IntegratedDeclarationBinding`, `mkIntegratedDeclarationBinding` retain attribution; source presence alone is not execution or an imported Agda proof.

### First two vertical slices, exact residual dependencies

**Slice H — existing Hecke owners, cheapest proof-bearing regression.** Starting owners: `AristotleHeckeRecurrenceCoreExact`, `AristotleHeckeGeneralPrimePowerDecompositionExact`, `AristotleHeckeWordsSourceParityExact`, and `AristotleMathSourceParityExact`. Do not rebuild squarefree multiplicativity. Unpaid: extract source/target statement signatures and normalization, prove the selected same-statement receipt, record the original `Nat` Hecke packaging / raw prime-power grouping / finite separating bound as separate outstanding statements where still unpaid, and produce checked positive and negative controls. The source-side arithmetic theorem is a donor, not proof of any executable representation or whole operator algebra by itself.

**Slice W — nontrivial mathematical world.** Establish a typed world component that contains two original source declarations plus a *checked* interpretation/implication path; preserve their distinct proofs, source identifiers, assumptions and any open hypotheses. Feed a genuinely remaining target back to `ProofDebtRouterExact` and `DependencyDerivedMinimalInvalidationBidiExact`. Repeat on Monster/Y443, Popov VOA, Stacks indexed fibres and Karp/FRACTRAN only after searching their current existing owners. No source-name-based promotion.

### Definition of done for the next PR iteration

1. Extract a small real Lean/Agda declaration corpus at pinned commits **directly through each proof system**, rather than inferring theorem types from GitHub search descriptions.
2. Emit a machine-readable identity/dependency ledger with source SHA, original declaration names and types, checker version, axioms, explicit equivalence/implication receipts, and unresolved obligations.
3. Prove or kernel-check at least one nontrivial selected bridge; add one deliberately non-equivalent negative-control pair.
4. Show AO finds a previously owned theorem rather than generating a redundant proof; separately show how an unpaid target is routed without being declared solved.
5. Record the precise integration gate results and provenance in the roadmaps, without sending the work to an external repository.

**Privacy rule:** repo search and normal reading of publicly available declarations are fine. Distribution of DASHI's unpublished material to unaffiliated repositories is forbidden unless separately and explicitly authorized.


## 2026-11-09 maximum-cut reconciliation after full PR archaeology

**This section supersedes earlier speculative F0–F5 missing-capability rows.** Source archaeology identified existing implementations. Do not reimplement them. The next proof work begins at *integration of those implementations with actual source declarations*.

### Confirmed existing owners, not gaps

- `dashi_agda/tools/agda_preflight/agda_preflight/ast_index.py`: Agda AST signatures, imports, clauses and record/data structures.
- `repository_discovery.py` / `semantic_extension.py`: repository DB `normalized_signature`, `signature_sha256`, `body_sha256`, `repo_refs`, `related_symbols`, `discovery_receipt` and candidate evidence.
- `proof_router.py` / `external_proof_bridge.py`: proof debt and external source/verification receipt routing, explicitly not automatic theorem proof.
- `dashi_agda` PR **#1212**: OpenAI math corpus source atlas, symbol snowball and owner routing; `dashi_lean4` PR **#78**: source declaration index, candidate-owner matrix, reviewed same-object boundaries and statement-integrity checks.
- `dashi_agda` PR **#1437** (alongside #1415–#1417): hierarchical spectral Pareto, world-eigen stratification, sublinear conductor and max-cut ownership. Lean PR **#102** mirrors the formal contract. These are **existing mathematics**, not conjectural new machinery.
- Lean PR **#71** already has scoped verifier same-object evaluation.
- The original Hecke recurrence, prime-power assembly and related Agda owners are existing; no reproof of squarefree multiplicativity.

### New full-corpus input now committed

`dashi_lean4` PR **#105** committed two independent GitHub corpora at retrieval time 2026-11-09: **8,764 JMD public stars**, of which **1,996** are primary-language Lean, and **21,481 GitHub-wide `language:Lean` repositories** across **34 disjoint creation-date partitions**, with **231 pages** and **298 raw count/page receipts** (reported from completed collector validation). These are moving GitHub-index observations, not all formally checked Lean declarations.

New **`scripts/audit_jmd_formal_corpus.py`** joins the two sources only by numeric GitHub repository ID, validates exported counts, subset identity, checkpoint ID/name agreement, disjoint contiguous date windows and expected page counts, and writes `docs/roadmap/jmd_formal_ingress/audit.json` plus `starred_global_overlap.tsv`. `scripts/test_audit_jmd_formal_corpus.py` contains positive and fail-closed negative controls. The integration **does not classify mathematical theorems** and must never promote metadata to proof. Run locally from the Lean repo root:

```sh
python -m unittest discover -s scripts -p 'test_audit_jmd_formal_corpus.py' -v
python scripts/audit_jmd_formal_corpus.py
```

The script's synthetic fixtures were tested during development. **The full 21,481-row live ingress audit has not yet been run in the repository environment.** Its outputs should not be described as present before execution.

### Corrected exact remaining max-cut

| Gate | Decisive result (avoid duplicate tools) | Status |
|---|---|---|
| **P0.01** | Run the new full-corpus audit against both committed CSVs and actual checkpoint; inspect any coverage mismatch rather than suppressing it | OPEN for production execution |
| **P0.02** | Apply existing `dashi-repo symbol / related_symbols / discover` against **each distinct** JMD image claim and record exact declaration, full type, imports and source commit; distinguish non-mathematical images | OPEN: module candidates already indexed |
| **P1.01** | Extend **existing** OpenAI-math source candidate-router/statement-audit pattern to selected corpus **declarations**, not repository names; preserve branch/version and no-claim defaults | OPEN: generic integration, source implementations present |
| **P1.02** | Obtain authoritative selected Lean elaborated theorem types and axiom/opaque dependency closure, using pinned Lean environments, and compare with Agda original owners | OPEN for selected external formal proofs |
| **P2.01** | One *source-inspected* and *kernel-checked* same-object equality or hypothesis-preserving implication, with a deliberately non-equivalent negative control and original author credit | OPEN; source comparison precedent exists |
| **P2.02** | Join that certified relation into existing proof-debt and dependency-scheduler owners; show actual paid gap and unchanged unrelated cones | OPEN for this corpus instance |
| **P3.01** | Repeat the verified route for Hecke, selected Monster/Y443, Popov VOA, CFSG, Stacks or Karp only if a **precise** consumer and actual source declaration warrant it | OPEN by consumer |
| **P3.02** | Preserve private/unpublished DASHI material: **no external PR, issue, comment, message, or upstream source upload** unless separately authorised | Mandatory invariant |

These gate labels are **integration milestones**, not newly defined Agda/Lean theorem names. The mathematics should be placed with its existing closest owner in the Agda/Lean formal dependency graph, not in a competing world-index package. SLR/PNF is optional for human navigation and never proof authority.


### Implemented P0 image owner-search dispatch (2026-11-09)

The new `Docs/roadmap/JMDImageOwnerSymbolSnowballTerms.json` encodes **12 image-topic groups and 40 real owner-search terms** using the already existing `dashi-symbol-snowball-v1` schema from `dashi_agda` PR #1212. It is a **term pack, not a new indexer or mathematical proof**. The canonical source of searchable Agda signatures remains the `dashi-repo` preflight database. The existing runner resides in PR #1212; do not assume it is on `master` or that this branch has imported that PR.

Once the PR #1212 runner is present in a compatible checkout, run:

```sh
python scripts/run_openai_math_symbol_snowball.py \
  --terms-file Docs/roadmap/JMDImageOwnerSymbolSnowballTerms.json \
  --agda-root . --mode native --discover \
  --max-terms 100 --out /tmp/jmd-owner-search.tsv
```

This yields **candidate owner search evidence**. Next P0 payment is to source-read each matched declaration's actual type and imports and classify it as exact owner, partial owner, negative control, or no proved owner. The 37 original SHA-256 image references remain in `Docs/roadmap/JMDImageSHA256Manifest.csv`; the search pack carries stable image IDs to group search. Avoid falsely claiming these 40 queries have already been run against the current full repository database.


## 2026-11-09 implemented deterministic formal-world execution slice

This supersedes the earlier **planned-only** P0–P6 entries. Actual source is
in [dashi_agda PR #1477](https://github.com/chboishabba/dashi_agda/pull/1477)
and the pinned Lean corpus + extractor in
[dashi_lean4 PR #105](https://github.com/chboishabba/dashi_lean4/pull/105).

| Gate | Implemented owner | Precise acceptance still open |
|---|---|---|
| P0 | \`jmd_formal_world_reconcile.py\` validates manifest repository IDs/names; reads existing Agda AST/signature tables; 12 image-topic groups route to indexed symbol candidates | Full local 21,481-row ingress + 12-group execution receipts |
| P1 | Native \`repo_requirements\` and \`repo_refs\` gap discovery; direct dependency neighbourhood prioritized over lexical hits | Real full-repo gap-status comparison to AO proof-debt owners |
| P2 | \`jmd_attach_wikidata_oeis.py\` source-span QID/OEIS references, plus optional attributed external-coordinate records | Source-read same-object mathematical semantics |
| P3 | Persistent candidate-only links in **existing** \`.dashi/repository.sqlite3\`, with revision hashes and source provenance; selected pinned Lean \`#check\`/\`#print axioms\` extractor | Environment-faithful selected external theorem inventory at scale |
| P4 | Actual opt-in \`lake env lean\` exact-donor probes; reject nonzero, \`sorryAx\`, dirty revisions and injected goal text | A locally executed accepted proof and independently checked Agda transport |
| P5 | \`JMDFormalWorldReconciliationExact.agda\`: proof-term implication composition, equivalence with both sources preserved, candidate ≠ proof; world groups keep distinct accepted donor witnesses | Agda 2.9 --safe acceptance and a nontrivial source-to-target equivalence witness |
| P6 | Source signature deltas plus existing reverse \`repo_refs\` dependency closure; re-evaluate candidates on every ingestion; unaffected edges not marked refuted | Local delta replay, native reference completeness and production validation |

**Execution is not yet certified:** these modules/scripts/tests are written to
GitHub and have source-inspection and regression fixtures, but the assistant
environment has no installed Agda/Lean or the user's local full repository
checkout/index. No kernel run or complete integration replay has been claimed.
A checked Lean-local proof is not an Agda theorem until an explicit Agda
translation or consumer proof passes its own checker.

Authoritative full command guide:
[Docs/roadmap/JMDFormalWorldAutomaticExecution.md](https://github.com/chboishabba/dashi_agda/blob/chatgpt/jmd-image-owner-roadmap-20261109/Docs/roadmap/JMDFormalWorldAutomaticExecution.md).

## 2026-11-09 bidirectional translator round-trip max-cut (latest)

The **canonical** phase/deliverables/exact-lemma ledger is
[agda2lean/docs/BIDIRECTIONAL_ROUNDTRIP_MAX_CUT.md](https://github.com/chboishabba/agda2lean/blob/main/docs/BIDIRECTIONAL_ROUNDTRIP_MAX_CUT.md).
Do not create a second competing phase numbering here.

Existing source-writing:

- `dashi_lean4/Integration/JMD/RoundTripFixedPoint.lean`:
  `CertifiedRoundTrip`, `lean_agda_lean_stable`,
  `agda_lean_agda_stable`, `roundtrip_idempotent_left`,
  `roundtrip_idempotent_right`, `predicate_roundtrip`,
  `observer_roundtrip`, `trans`, `trans_source_stable`.
- `dashi_agda/DASHI/Interop/JMDRoundTripFixedPointExact.agda`:
  `CertifiedRoundTrip`, `leanAgdaLeanStable`,
  `agdaLeanAgdaStable`, `roundTripIdempotentLeft`,
  `roundTripIdempotentRight`, `observerRoundTrip`,
  `composeRoundTrip`, `composedRoundTripStable`.
  Its existing `Interop/Everything.agda` includes the module.
- `agda2lean/scripts/bidirectional_conformance.py` and
  `docs/roundtrip_feature_crosswalk.tsv`: fail-closed comparison of
  actual existing conformance corpora and reviewed candidate-only aliases.
- The separate `formalverification/lean2agda` upstream is referenced
  read-only, including its foundational profiles and original corpus
  manifest. No outbound publication, PR or user work transfer.

**Observed source counts:** agda2lean PR #7: 19 cases, 0 positive,
11 reconstruction, 8 unsupported. lean2agda upstream manifest:
12 `translated` entries (1 T0, 7 T1, 4 T2). Its corpus successes
are **not** successful translator round trips in our toolchain. The eight
reviewed taxonomy edges yield **42 candidate pairs, zero literal tag
matches**, with **10 Cubical/K-UIP conflict cases**, under the current
source manifests. Every pair remains unverified.

**Immediate exact unpaid acceptance:** M00a locally run tests and both
kernel checks; M00b source-faithful selected elaborated-normal-form
comparison; M01/M02 construct actual real translator witness maps;
M03/M04/M05/M06 prove source statement, axiom, dependency and
computation preservation; M07 instantiate fixed-point laws for a
selected original theorem; M08/M09/M10 validate negative controls and
selective reopening with the existing ITIR gap script only.

A generic conditional inverse-law theorem is NOT a proof that either
translator preserves arbitrary declarations. No such claim is made.


## 2026-11-09 correction — mathematical gap discovery is P0; translators are NOT P0

**This ordering supersedes any round-trip-centric priority that appears in
earlier sections.** The translator-specific roadmap in
`agda2lean/docs/BIDIRECTIONAL_ROUNDTRIP_MAX_CUT.md` remains useful
**inside that optional research lane**, but its R0–R6 is not the global
DASHI mathematical-discovery priority.

| Priority | Exact unpaid operational/lemma gate | Existing owner |
|---|---|---|
| **P0.1** | Run real source-index and declaration-identity reconciliations: admitted Lean repo IDs → pinned Lean declaration records, plus original Agda goal owners | `dashi_lean4` PR #105; `dashi-repo` |
| **P0.2** | Join **source-extracted Lean theorem types** against **actual unpaid Agda and Lean obligations** without promoting names/QIDs/OEIS or candidate status to proof | `ITIR-suite/scripts/formal_gap_join.py`, existing `itir.formal.inspect/route`, Lean #78, `repo_requirements` |
| **P0.3** | Output a deterministic source-pinned maximum cut: obligation, exact type, linked source candidate, dependency/axiom closure, priority/relatedness, failure/absence reason; no LLM | AO **gap-finding only**, `repo_refs`, ITIR formal tools |
| **P1.1** | For selected matched Lean declarations, establish a *kernel-checked* exact theorem reuse or source-hypothesis-preserving implication in Lean | `dashi_lean4` `Integration/JMD/CertifiedWorld.lean` and `Agda2Lean.Manifest` |
| **P1.2** | Preserve every independent proof's provenance; never merge theorem types based on source/ontology label alone | `ProofDebtRouterExact`, `CrossLaneProofArchaeologyLedgerExact`, Lean checked world |
| **P2** | On actual declaration revision delta, selectively reopen dependent goals, leave unaffected proofs untouched | `DependencyDerivedMinimalInvalidationBidiExact`, source-hash delta script |
| **P3** | Selected cross-language transfer **only when** an Agda consumer needs an already certified Lean theorem and a faithful translation is available | `agda2lean`, upstream `lean2agda` (read-only reference), original Agda owner |
| **P4** | Broader Lean→Agda→Lean fixed-point benchmark and translator capability expansion | Separate `agda2lean` round-trip roadmap |

**Immediate decisive demo:** take one original unpaid DASHI mathematical
obligation, automatically discover its strongest existing **Lean** donor,
produce a checked Lean implication/reuse, and show the proof debt reduced
or a precise fail-closed residual. The current source-written scripts have
not demonstrated this real end-to-end payment, and this document makes no
claim that a source candidate is a theorem proof. The script may be called
by an orchestrator; it neither invokes nor implements orchestration.
