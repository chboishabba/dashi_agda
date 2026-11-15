# WebKB-2 × DASHI × situated observers × PNF/world × hyperfabric
### Consolidated maximum-cut implementation and proof-obligation dossier
**Version:** 15 November 2026  
**Scope:** source-native WebKB ingestion; Agda golden contracts; intersectional/situated observers and consumer factorisation; residual-driven hyperfabric refinement; NORA author-feedback candidate; existing ITIR MCP/Zelph and SLR runtime; Lean-world and LeechTransformer consumers.  
**Evidence status:** repository source inspection on 15 November 2026, local Python reference tests, unverified WebKB-specific formal gates.

> **Contract:** Reuse the existing theorem owners. Preserve authorship and all source/observer/context/revision/authority axes. A pass on a finite reference model cannot be promoted into Agda kernel acceptance, original WebKB bytes, empirical truth, complete world coverage, or safe learner KV reuse.

## Executive disposition
The original 39 A–F names are retained below as *target contracts*. The substantive correction is that the foundational calculus is already present in DASHI: `FactorsThrough`, `ConsumerSufficient`, least sufficient consumer observers, non-descent witnesses, collision-induced residual repair, least observer joins, provenance-bearing quotient reopening and typed hyperfabric restrictions. These are **declared existing source owners**, not 39 fresh theorems.

**Maximum cut:** (i) pin a WebKB fixture and separate parsed/attributed/admitted claims; (ii) compile its typed relation inventory into the existing consumer-relative semantic kernel; (iii) verify reachability/index parity, source-context qualification, and consumer-relative residual repair on the **same original fixture**; (iv) integrate persistence and theorem/learner consumers without authority escalation.

**New local deliverable:** `webkb_situated_reference.py` and `test_webkb_situated_reference.py` run 14/14 Python `unittest` tests, including exhaustive differential index/reachability parity on the 64 directed labelled three-node graphs. This is a finite prototype without native FL parsing, Agda kernel verification, WebKB binary-code decoding, or production SLR.

## 1. Grounded WebKB source and interpretation cautions
The original WebKB-2 top ontology (`https://www.webkb.org/kb/top/theKB_categs.html`) describes its abbreviations and the native FL symbols `<` subtypeOf, `>` subtype, `^` instanceOf, `:` instance, `=` equal, `-` inverse, `!` simple exclusion, `/` closed exclusion, `&` related, and `>part` subdomain. `/` is defined as a closed exclusion, and the upper ontology distinguishes things, situations, entities and relations. Its code labels are read **right to left**, inherited or overridden; an ordinary trie-prefix interpretation is **not** established.

Do not conflate: (a) a source **asserts** a relation; (b) our parser faithfully represents it; (c) a checked derivation follows within a declared local assumption context; (d) a consumer has enough information; (e) the entire real world is covered. Each is a separate type and acceptance gate. Source qualification and creator/revision are part of identity. Explicit relation assertions must not be treated as mathematical equalities without an admitted axiom/bridge. Fuzzy `&` never becomes equivalence by name coincidence.

## 2. The shared situated-observer calculus (reuse, not reinvention)
Let `S` be the situated state carrier including source identity, observed world, time/revision, observer standpoint, access/authority, evidence route, query and modeled relation. For a coarse observation `π : S → V` and a **consumer-specific** `q : S → Q`, define

`FactorsThrough(π,q) := Σ(g : V → Q). ∀s, q(s) = g(π(s))`.

The canonical finite extensional criterion is **fibre constancy**: if `π(x)=π(y)` then `q(x)=q(y)`. Its converse to an explicit factorization requires appropriate representation/choice assumptions; the repo proves it for sectioned projections. A **non-descent witness** is `x,y` with the same coarse image and unequal consumer answers. Such a witness refutes *every* factorization and survives any recharting/postmap of `π`. An observer join `⟨π₁,π₂⟩` can refine each axis, but is sufficient for `q` only after a witness that the join actually determines `q`.

A **residual** is not a vague claim of uncertainty: it is a typed consumer-relative collision/obligation whose separation would actually improve the current query. We must route `firstResidual` to a targeted source/observer acquisition; source acquisition creates candidate evidence, not authority. A repairs-only-when-needed sparse hyperfabric stores local stalks, incidence, typed restriction, provenance and compatible sections, not the Cartesian product of all axes.

**Worked counterexample:** Let `S = {0,1} × {0,1}`, `π(a,b)=a`, and consumer `q(a,b)=b`. States `(0,0)` and `(0,1)` have equal `π` but unequal `q`, so `q` does not factor through `π`. Adding `b` as a residual coordinate makes `⟨π,b⟩` sufficient; relabeling `a` cannot. This demonstrates finite consumer sufficiency **for `q`**, not empirical knowledge completeness.

## 3. Actual existing DASHI theorem owners discovered
| Reused owner / module | Source-level contract verified by reading the file | WebKB implication |
|---|---|---|
| `DASHI/Core/IntersectionalNonFactorability.agda` | `FactorsThrough`, `NonFactorabilityWitness`, `witnessRulesOutEveryFlatFactorisation`, `postcomposeNonFactorability`, `rechartingCannotRecoverErasedPhenomenon` | An ontology label, category or coarse graph code cannot rescue omitted situated outcomes. |
| `DASHI/Core/QueryFactorisationSufficiency.agda` | `InquiryQuestionFamily`, query-indexed `FactorsThrough`, `StaticSufficient`, explicit no-world-coverage permission | Source graph can be sufficient for one query without being a world ontology. |
| `DASHI/Core/ConsumerDescentMinimalObserverExact.agda` | `FibreConstantFor`, `ConsumerSufficient`, sectioned descent equivalence, `LeastSufficientConsumerObserver`, `ConsumerNonDescentWitness` | Reuse the consumer-indexed descent theorem; no new sufficiency calculus. |
| `DASHI/Core/ConsumerFibreRepairExact.agda` | `refinementRepairSeparatesWitness`, `factorizationRepairSeparatesWitness` | Any claimed repair must separate actual colliding source states. |
| `DASHI/Core/ConsumerIndexedResidualRefinementExact.agda` | `ConsumerRelevantCollision`, `residualMustSeparateRelevantCollision`, `consumerRelevantResidualGivesStrictRefinement` | Demand-driven, query-relative ontology expansion. |
| `DASHI/Core/RequiredObserverAxisJoinAdequacyExact.agda` | `jointAxis`, `candidateRetainingBothRetainsJoint`, `retainsBothGivesJointFactorisation` | Source, world, standpoint, rights and provenance join only when the consumer requires them. |
| `DASHI/Core/ObserverRefinementCore.agda` | Pair observers and least common refinement laws | Axis order is semantic information order, not blanket addition of dimensions. |
| `DASHI/Core/MinimalSufficientResidual.agda` | Binary hidden-bit residual and concrete separation witness | Reuse finite residual/capacity counterexample as a regression. |
| `DASHI/Core/ProvenanceBearingQuotient.agda` and `CoarseFineRelativeFibreExact.agda` | Source-reopenable coarse/fine projections and fine-relative consumer obstruction | Keep original fibres after compaction or indexing. |
| `DASHI/Reasoning/TypedHyperfabricCore.agda` | Typed vertex/edge stalks, incidences, restrictions, compatible `GlobalSection`, provenance | A source mapping is a typed local relation, not automatically a globally compatible section. |
| `DASHI/Interop/GodsEyeViewProofCarryingWorldOntologyExact.agda` | Receipt-based observation, coverage and presence epistemics, attribution layer, consumer projection | `uninspected ≠ absent`; visualization ≠ world identity ≠ theorem authority. |
| `DASHI/Interop/PNFHyperfabric369.agda` | PNF and hyperfabric integration owner | Integrate worlds with qualified observer context, not a second world engine. |

**Status qualifier:** These declarations are visible in the remote repository, but this authoring environment lacks Agda/Nix; fresh kernel acceptance of any new WebKB specialization is **not claimed**. Exact current PR-head acceptance must be re-run on the intended rollup branch.

## 4. Source and formal data model
Use a *typed*, source-qualified canonical IR, not flat unscoped triples.

`SourceKey = (publisher/creator, dataset, revision, source_uri, content_digest)`  
`ConceptId = (SourceKey, local_key)`  
`Assertion = (subject, relation_kind, object, world_context, valid_time, observation_time, source_span, attribution, epistemic_mode)`  
`Admission = (consumer, query, authority_basis, required_axes, derivation_or_review_receipt)`  
`DerivedEdge = (premise_refs, inference_rule, same_world_context, proof_receipt)`  
`Residual = (consumer, query, coarse_projection, collision_pair_or_obligation, missing_axis, acquisition_route)`.

Distinguish native relation constructors `SubtypeOf`, `InstanceOf`, `EquivalenceClaim`, `SimpleExclusion`, `ClosedExclusion`, `Inverse`, `RelatedFuzzy`, `Subdomain`, `RelationSignature`, `UnknownUnsupported`. Canonicalization may deduplicate identical claim instances **but must not erase independent attributed edge receipts**. A cycle of subtype links gives a preorder; pass to an explicit equivalence/SCC quotient for poset statements. Closure and partition rules are **world/source-local**, with cross-world or cross-source transport only via an explicitly reviewed bridge.

For partition `{B,C}` under `A`, the semantics `B∪C=A` and `B∩C=∅` require an explicit closed-partition assertion with correct scoping, not a pair of isolated `!` exclusions. Incomplete import coverage forbids negative-world or negative-graph conclusions. Native WebKB binary codes are preserved as **uninterpreted source data** until differential semantics is demonstrated.

## 5. Phases, exit criteria, and named deliverables
| Phase | Concrete deliverable | Hard exit criterion |
|---|---|---|
| P0 — reuse and evidence pin | Full exact-declaration ledger; PR-head SHA; original WebKB source SHA/URI | Every contract mapped to existing owner/bridge/new proof, and exact fixture immutably pinned. |
| P1 — source native parsing | FL grammar + unsupported syntax receipts; canonical typed IR; provenance-safe parser | Round-trip and source span/identity equality on pinned original snippets. |
| P2 — semantic golden spine | Formal instance/subtype/partition/equivalence closures and conflict receipts | Kernel-checked conditional theorems, finite counterexamples and no source→truth promotion. |
| P3 — indexed hyperfabric | DAG/SCC ancestry index, query certificates, incremental invalidation | Same-object C2/C3/C7 and H4/H6 on original graph, not synthetic alone. |
| P4 — observer/consumer/world | G1–G10 bridges, contexts, residual-driven rechart/reopen | Collision witness→required axis→strict refinement→consumer answer, preserving authority. |
| P5 — persistence and orchestrator | SLR provenance-aware storage; ITIR acquisition/query API | Persist/reload exact receipt, revision, context, and strict unanswered/unsupported routing. |
| P6 — theorem/learner adapter | Lean-world retrieval certificates; PNF model; controlled LeechTransformer experiments | Kernel firewall; exact retrieval and matched training/inference ablations. |
| P7 — rollup/acceptance | One existing PR per repo; acceptance scripts; hashes and reproducible receipts | Clean exact-head Agda + Python + SLR + ITIR; real WebKB corpus + source provenance. |

**Owner selection:** The nearest active ontology/trie/hyperfabric rollup is DASHI PR #1506 (`agent/nora-perspective-consumer-maxcut-20261114`). This does **not** license modifications to unrelated Clay/Biology rollups, nor does one PR mean mixing incompatible source histories. Coordinate related ITIR/SLR owners by source-specific branches/PRs rather than creating a parallel runtime.

## 6. Formal dependency path and maximum-cut gates
`Source bytes → source-qualified FL AST → attributed claim IR → admitted context/world premises → reference inference → consumer sufficiency/refutation → hyperfabric indexed refinement → query certificate → SLR persist/reload → ITIR query/acquire/review → theorem/learner use`.

Critical formal sequence: **A1/A2/A3/A5 → B1/B2/B4/B6/B7 → G2/G3/G6/G7 → C2/C3/C7 + H4/H6**. PNF and theorem-world integrations come only after `D5/D7/E5`, and learner KV cache is an independent model-dependent correctness obligation. Exact numeric priority means very little until the actual existing generic lemmas have been reused and the WebKB-specific concrete index/consumer is instantiated.

## 7. Original 39-gate ledger (reconciled)
The following names/contracts are preserved from the supplied 15 November roadmap. **They are proposed WebKB-specialization names** unless an explicitly named existing generic declaration is shown in the owner column. `REUSE+BRIDGE` means generic mathematics visibly exists but a WebKB-specific instantiation has not been verified. `OPEN` means the named WebKB contract has no direct proof/producer receipt in this audit. No row is marked `AGDA PASS` on the strength of Python tests.

### A — Parsing, identity and canonicalization

| Gate | Target name | Contract | Audit disposition |
|---|---|---|---|
| A1 | `webKBFLParsePrintRoundTripExact` | Printing and reparsing preserves the normalized AST | OPEN |
| A2 | `webKBSourceQualifiedIdentifierInjective` | Distinct source-qualified IDs never collapse accidentally | OPEN |
| A3 | `webKBRelationSymbolInterpretationExact` | Each supported FL link maps to its declared semantic constructor | OPEN |
| A4 | `webKBPartitionSyntaxPreservesClosure` | Complete partitions retain both exclusion and coverage | OPEN |
| A5 | `webKBSourceSpanProvenancePreserved` | Every imported assertion can be traced to its original source | OPEN |
| A6 | `webKBCanonicalDAGIdempotent` | Recanonicalization does not change the canonical graph | OPEN |

**Primary owner:** DASHI/Ontology + source-native FL importer; reuse provenance/quotient core.

### B — Semantic graph and ontology reasoning

| Gate | Target name | Contract | Audit disposition |
|---|---|---|---|
| B1 | `ontologySubtypeReflexiveTransitiveClosureExact` | Finite-path reachability equals reflexive-transitive subtype closure | REUSE+BRIDGE |
| B2 | `ontologyReachabilityDecisionSoundComplete` | Executable reachability returns true exactly when a path exists | OPEN |
| B3 | `ontologyMultipleInheritancePathPreserved` | All declared inheritance routes remain available | REUSE+BRIDGE |
| B4 | `ontologyInstanceSubtypeTransport` | Instance membership propagates through valid subtype edges | REUSE+BRIDGE |
| B5 | `ontologyEquivalentClassesQuotientSound` | Explicit equivalence generates a semantics-preserving quotient | REUSE+BRIDGE |
| B6 | `ontologyDisjointSubtypeContradictionWitness` | Incompatible type memberships produce a finite conflict witness | REUSE+BRIDGE |
| B7 | `ontologyCompletePartitionCoverageExact` | The declared coverage axiom is represented and correctly applied | OPEN |
| B8 | `ontologyRelationSignatureTypingPreserved` | Relation arguments satisfy their declared signatures | OPEN |

**Primary owner:** Core.ConsumerDescentMinimalObserverExact; ObserverRefinementCore; Ontology/graph owners.

### C — Binary codes, tries and hyperfabric

| Gate | Target name | Contract | Audit disposition |
|---|---|---|---|
| C1 | `webKBBinaryCodeDecodeRoundTrip` | Valid encoded categories decode without information loss | OPEN |
| C2 | `webKBBinaryCodeSpecializationSound` | A positive code test implies graph specialization | OPEN |
| C3 | `webKBBinaryCodeSpecializationComplete` | Every graph specialization is detected, for the chosen index representation | OPEN |
| C4 | `hyperfabricMultiParentUnionExact` | Indexed descendants preserve all inheritance branches | REUSE+BRIDGE |
| C5 | `hyperfabricIncrementalEdgeInsertionExact` | An index update agrees with complete recomputation | OPEN |
| C6 | `hyperfabricCanonicalQueryInvariant` | Queries are invariant under canonical graph renaming | REUSE+BRIDGE |
| C7 | `hyperfabricIndexedReachabilityBisimulation` | Indexed reachability and reference-graph reachability are equivalent | REUSE+BRIDGE |

**Primary owner:** Reasoning.TypedHyperfabricCore; IndexedRelationalHyperfabricSpineExact; trie/ternary owners.

### D — Provenance, conflicting ontologies and world semantics

| Gate | Target name | Contract | Audit disposition |
|---|---|---|---|
| D1 | `ontologyAssertionProvenanceNonErasure` | Merging assertions preserves originating sources | REUSE+BRIDGE |
| D2 | `ontologyCrossSourceEqualityNotAutomatic` | Lexically identical names do not imply equal concepts | REUSE+BRIDGE |
| D3 | `ontologyContextualConflictWitnessExact` | Every reported conflict has supporting premises and context | REUSE+BRIDGE |
| D4 | `ontologyBeliefRevisionNonDestructive` | Corrections do not erase earlier attributed claims | REUSE+BRIDGE |
| D5 | `worldIndexedAssertionIsolation` | A claim in one world cannot silently enter another | REUSE+BRIDGE |
| D6 | `worldTransitionPreservesDeclaredInvariants` | Valid transitions preserve stipulated state constraints | REUSE+BRIDGE |
| D7 | `ontologyWorldTransportRequiresBridge` | Cross-world reasoning requires an explicit bridge rule or proof | REUSE+BRIDGE |

**Primary owner:** Core.ProvenanceBearingQuotient; GodsEyeViewProofCarryingWorldOntologyExact.

### E — Lean/Agda theorem-world integration

| Gate | Target name | Contract | Audit disposition |
|---|---|---|---|
| E1 | `theoremWorldQualifiedConstantIdentity` | Theorem identities include their defining environments | REUSE+BRIDGE |
| E2 | `theoremWorldDependencyGraphExact` | Extracted dependencies match the accepted source declaration graph | OPEN |
| E3 | `theoremWorldOntologyAlignmentWitness` | Every semantic alignment has a recorded justification and scope | REUSE+BRIDGE |
| E4 | `theoremWorldRetrievalSoundness` | A certified retrieval result satisfies its declared formal query | OPEN |
| E5 | `theoremWorldKernelAcceptanceFirewall` | Unverified ontology claims cannot become trusted kernel proofs | REUSE+BRIDGE |

**Primary owner:** Ontology.LeanWikidataWholeBridge; Lean world builder/verifier contract.

### F — PNF/world, memory and learner

| Gate | Target name | Contract | Audit disposition |
|---|---|---|---|
| F1 | `pnfOntologyStateEmbeddingExact` | Well-formed symbolic world states embed into the shared semantic representation | REUSE+BRIDGE |
| F2 | `pnfTransitionGraphSimulation` | Encoded state transitions simulate the declared reference transitions | REUSE+BRIDGE |
| F3 | `learnerMemoryProvenanceReconstruction` | Retrieved structured memory retains source and context | REUSE+BRIDGE |
| F4 | `learnerKVSemanticCacheNoFalseReuse` | Cache reuse respects exact declared key/semantic validity conditions | REUSE+BRIDGE |
| F5 | `learnerOntologyConstraintSoundMask` | Constraint masking cannot admit forbidden transitions | REUSE+BRIDGE |
| F6 | `learnerOntologyConstraintCoverage` | Constraint masking does not remove valid transitions within the modeled constraint system | REUSE+BRIDGE |

**Primary owner:** Cognition.PNF; Core.ConsumerIndexedResidualRefinementExact; LeechTransformer.

## 8. Additional observer/situated-source gates G1–G10
| Gate | New exact target | Required contract |
|---|---|---|
| G1 | `webKBSituatedObserverConsumerFibreExact` | Represent situated source, revision, world, standpoint, authority and query independently. |
| G2 | `webKBConsumerDescentFromExistingCore` | Reuse canonical ConsumerSufficient/FactorsThrough; derive WebKB-specific sufficiency only with exact consumer witnesses. |
| G3 | `webKBNonDescentWitnessFromOntologyCollision` | Same projected category but different consumer answer yields a certified non-descent obstruction. |
| G4 | `webKBRechartingCannotRestoreExcludedAxis` | No postcomposition of a collapsed coarse observer repairs an existing collision. |
| G5 | `webKBRequiredObserverJoinIsLeastRefinement` | Required source, context and situated axes combine via existing observer-join laws. |
| G6 | `webKBResidualRefinementSeparatesConsumerCollision` | Repair must separate the specified collision, preserving retained source/authority coordinates. |
| G7 | `webKBSufficientForQueryNotWorldComplete` | Consumer sufficiency never implies global ontology completeness or source coverage. |
| G8 | `webKBHyperfabricLocalToGlobalRequiresCompatibility` | Local stalk evidence glues only via explicit compatible restriction witnesses. |
| G9 | `webKBProvenanceReopeningPreservesOriginalClaim` | Coarse quotient preserves enough source data for attributable reopening. |
| G10 | `webKBContextualAuthorityNonPromotion` | Source label, inferred relation, reviewed statement and proven theorem remain distinct. |

**Already owned:** G2/G3/G4/G5/G6/G7 build upon `ConsumerDescentMinimalObserverExact`, `IntersectionalNonFactorability`, `RequiredObserverAxisJoinAdequacyExact`, and `ConsumerIndexedResidualRefinementExact`. G8 needs `TypedHyperfabricCore.GlobalSection` compatible restrictions. **New genuine cut:** independently acquired WebKB source/context/authority axes must inhabit these contracts with honest receipts. Do not relabel existing generic proofs as WebKB-specific acceptance.

## 9. Additional native-WebKB and physical-execution gates H1–H8
| Gate | New exact target | Required contract |
|---|---|---|
| H1 | `webKBFLGrammarCoverageForPinnedFixture` | Parser accepts exactly declared supported WebKB FL constructs; others carry explicit unsupported-form receipts. |
| H2 | `webKBClosedExclusionSoundAgainstPartition` | `/` is disjoint+complete only where same-parent/whole-domain side conditions actually hold. |
| H3 | `webKBCodeBitOrderValidation` | Native right-to-left encoding decoded by its own grammar; neither ordinary prefixes nor DAG closures assumed. |
| H4 | `webKBCodeCandidateFilterNoFalseNegative` | A code prefilter cannot prune any reachable specialization; otherwise mandatory exact fallback. |
| H5 | `webKBOriginalByteRevisionHashSameObject` | Pinned source bytes/URI/revision/hash bind ontology assertions to actual WebKB release. |
| H6 | `webKBHyperfabricIndexedQueryCertificate` | Indexed result includes path, source receipts, context and consumer-relative query validation. |
| H7 | `webKBIncrementalSelectiveInvalidationExact` | Insert/revise edge invalidates exactly affected result dependencies under stated version assumptions. |
| H8 | `webKBSLRRoundTripEvidenceAndRevisionExact` | Persist/reload retains all source/world/revision/consumer identity and typed authority labels. |

## 10. Finite discriminator experiments and local execution receipt
| Test | Discriminator | Status in local Python reference | Still needed |
|---|---|---|---|
| T1 | Diamond multiple inheritance | PASS | Kernel same original WebKB fixture |
| T2 | Directed cycle and preorder | PASS | Explicit quotient/SCC formal bridge |
| T3 | Closed complete partition | NOT IMPLEMENTED | Native `/` grammar, sound coverage/exclusion |
| T4 | Same-world contradiction receipt | PASS | Fully source-span-qualified provenance |
| T5 | Same local label from two ontologies | PASS | Source-creator/revision mapping index |
| T6 | New edge and index invalidation | PASS (rebuild baseline) | Selective minimal invalidation |
| T7 | Conflicting cross-world observations | PASS (isolated) | Explicit reviewed world transport |
| T8 | Same concept, different KV context | NOT IMPLEMENTED | LeechTransformer exact parameters and KV contract |
| T9 | Unverified equality mapping | PASS (fail closed) | Agda/Lean kernel firewall end-to-end |
| T10 | All 64 three-node directed graphs | PASS | Larger random/exhaustive corpus with original data |
| T11 | Coarse collision→strict consumer residual repair | PASS | Genuine source-specific axis-repair witness |
| T12 | Postcompose/rechart cannot repair information loss | PASS | Agda specialization reuse |
| T13 | Source attribution survives canonicalization | PASS (claim-level) | Multiple-claim edge-provenance joins |
| T14 | Consumer query sufficiency ≠ world completeness | PASS (finite example) | World coverage/admission receipt |

**Command:** `cd /mnt/data && python -m unittest -v test_webkb_situated_reference.py`  
**Result:** `Ran 14 tests ... OK` in the local environment (15 November 2026). No Agda binary, SLR database, real WebKB FL data corpus, external PR update acceptance, or LeechTransformer benchmark was executed by these tests.

## 11. Situated/ethical/epistemic invariants
1. **No God's-eye inference:** a map or category label cannot substitute for the source, observer position, coverage, context and admitted consumer.
2. **Intersectional non-factorability:** aggregated labels cannot be repaired by reweighting when omitted joint conditions change the decision.
3. **Question-indexed sufficiency:** `sufficientConsumer` is parameterized by the concrete decision/consumer; it does not promote into universal knowledge.
4. **Ternary/open-world discipline:** `unknown` is not false, absent, irrelevant or unsupported source; where appropriate preserve distinct unresolved, contested, uninspected and inapplicable states.
5. **Provenance-bearing quotient:** compaction and index canonicalization retain reversible attributed claim receipts.
6. **Source vs inference:** WebKB author assertions and typed DASHI deductions remain distinguishable, including disagreements between sources.
7. **Sparse consumer-directed hyperfabric:** retain only observed or requested intersections; add fibres when proven residuals show that a consumer needs them.
8. **PNF/revision discipline:** a source revision opens and invalidates only affected dependencies, while old snapshots remain attributable.
9. **Learner safety:** a semantic retrieval match does not license KV-cache reuse. Model weights, tokens, position encodings and attention context are independent constraints.
10. **Attribution:** WebKB-2 and its ontology authors own source ontology/notation; DASHI owns new formal interpretations; Duta et al. own Sheaf Hypergraph Networks inspiration; Crenshaw owns intersectional conceptual work, not our formal theorem; original Zelph/NORA/Wikimedia authors retain their independent source identities.

## 12. Remaining precise maximum cuts, by independent evidence class
**I. Original-source/physical cut (open):** pinned WebKB HTML/FL snapshot hash; source-span extraction with native identifiers and revision/creator data; supported grammar test fixture; native right-to-left binary-code decoding; real source-context qualified graph agreement; source ownership/terms.

**II. Proof cut (open):** real WebKB IR type preservation, closed-partition semantics, equivalence claim/admission distinction, same-context reachability proof, exact index bisimulation, consumer-specific non-descent and repair, typed compatible hyperfabric sections, world transport firewall.

**III. Runtime cut (open):** SLR persisted/reloaded source and graph IDs, ITIR proof-query and residual-acquisition endpoints, source revision invalidation, receipts with original bytes and same-object join.

**IV. Theorem-world/learner cut (open):** Lean-world identity + kernel checks; grounded ontology alignment receipts; PNF candidate-only world transport; matched TinyStories/learner retrieval and KV variants with CE, latency, memory and false-reuse discriminators. No claim that ontological constraint training improves generalization without controlled results.

**V. Reuse audit (partially paid):** twelve actual module paths and key declarations verified from remote default-branch file contents; this is neither an exact rollup-head dependency closure nor an Agda kernel run. Exact cross-branch head reconciliation is required before commit/review.

## 13. Suggested one-PR-per-repository integration
| System | Golden home and planned changes | Exit evidence |
|---|---|---|
| DASHI Agda | Existing ontology/hyperfabric rollup PR #1506; reuse Core owners, add only bridges, evidence ledger | Pinned SHA, `agda --safe` target commands/logs, zero new postulates/holes |
| SLR | Existing S29 graph/claim persistence | Database migrations, rust tests and persisted/reloaded original source receipts |
| ITIR-suite | Existing original-data/query routing | Native source importer, exact source-span and native binary-code fixture, fail-closed CLI tests |
| dashi_lean4 | Existing theorem-world ingestion | Checkable theorem environment and declaration identity; source alignment proof |
| LeechTransformer | Existing C2/C3 work | Matched constrained/unconstrained runs with fixed seeds, equal budget and KV parity controls |
| SensibLaw/Zelph | Existing provenance/graph routes, not a new indexing stack | Source/claim/revision identity join without Wikidata/API authority escalation |

No new PR should be created solely to duplicate existing generic mathematics. If the chosen active ontology PR cannot accept a coherent change safely, prepare a grounded patch artifact and reconcile its base first rather than mutating a random branch.

## 14. Next exact commands / acceptance ledger template
1. `git fetch --all --prune`; checkout clean PR #1506 current head; record `git rev-parse HEAD`, `git status --porcelain=v1`.
2. `rg -n 'FactorsThrough|ConsumerSufficient|NonDescentWitness|ResidualRepair|TypedHyperfabric|SourceAttribution|WorldCoverage' DASHI Docs scripts` and map each proposed gate to exact owner imports.
3. Pin original WebKB top ontology HTML as a source immutable fixture and record `sha256sum`, URL, fetched timestamp and licence/terms; do **not** manually rewrite it into authoritative source bytes.
4. Run Python finite harness under a pinned interpreter: `python -m unittest -v test_webkb_situated_reference.py`; extend with native FL parser/partition controls only after source fixture acquisition.
5. Add minimal safe Agda module(s) importing the named owners; instantiate source-qualified concepts, contextual consumer and residuals. Run `agda --safe -i . -l standard-library <module>` at exact commit. No generated proof `refl` stands in for source identity.
6. Make SLR/ITIR query pathways produce signed/digested receipts; compare indexed answers to source graph and fail closed on missing coverage or unsupported native symbol.
7. Add PNF/learner matched experiments; disable semantic KV-cache reuse unless exact equality/dynamic dependency conditions pay.
8. Record commit SHA and independent exit code for each repository, preserving last accepted heads even if later heads advance.

## 15. Sources and direct repository verification
- WebKB-2 top-level ontology: https://www.webkb.org/kb/top/theKB_categs.html (accessed 2026-11-15).
- DASHI master theorem files: https://github.com/chboishabba/dashi_agda/tree/master/DASHI/Core/ and https://github.com/chboishabba/dashi_agda/tree/master/DASHI/Reasoning/.
- [Specific factorisation owner] https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Core/ConsumerDescentMinimalObserverExact.agda
- [Intersectional witness owner] https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Core/IntersectionalNonFactorability.agda
- [Consumer residual owner] https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Core/ConsumerIndexedResidualRefinementExact.agda
- [Typed hyperfabric] https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Reasoning/TypedHyperfabricCore.agda
- [World ontology/observation epistemics] https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Interop/GodsEyeViewProofCarryingWorldOntologyExact.agda
- [Ontology rollup] https://github.com/chboishabba/dashi_agda/pull/1506
- Source inputs supplied by user: `Pasted text.txt`, WebKB-2 × DASHI original 39-contract roadmap (15 November 2026).

**Literature attribution:** Kimberlé Crenshaw, *Mapping the Margins* (1991) grounds the intersectionality framing, not the DASHI formal theorem. Blackwell (1953), Cousot & Cousot (1977) motivate comparison/refinement interpretations; they do not independently prove the WebKB-specific bridges. Duta et al., *Sheaf Hypergraph Networks*, arXiv:2309.17116, motivates typed sheaf-like hyperfabric structures without importing its empirical results.
## 16. NORA alpha: author-supplied announcement, integration scope and attribution

**Primary communications supplied in the request:** On 12 November 2026 at 04:04, **Éder Porto** announced the independently authored **NORA** ontology-mapping alpha/prototype, asked for feedback, and noted that documentation was not yet available. The links supplied were [NORA on Toolforge](https://nora-wmb.toolforge.org) and [Wikimedia Portugal feedback survey](https://lime.wikimedia.pt/wmbr/index.php/834521). On 14 November 2026 at 20:25–20:26, chb replied with [DASHI PR #1506](https://github.com/chboishabba/dashi_agda/pull/1506) and [SensibLaw PR #514](https://github.com/chboishabba/SensibLaw/pull/514). **Neither the author announcement nor the two PR links establish that Éder has reviewed, endorsed, merged, accepted or implemented the proposal.** The live NORA UI was not independently inspectable in this audit.

The existing [DASHI situated NORA projection](https://github.com/chboishabba/dashi_agda/blob/agent/nora-perspective-consumer-maxcut-20261114/DASHI/Ontology/NORAReviewPerspectiveProjectionExact.agda) defines **proposed local interoperability choices** as follows, without equating them to ontology truth values:

| Locally modeled choice | Type of action or judgment | Explicit non-promotion |
| --- | --- | --- |
| **valid** | consumer/context-specific reviewer judgment | neither universal truth nor a formal theorem |
| **invalid** | consumer/context-specific rejection | not global rejection under every observer |
| **ambiguous** | unresolved judgment | does not distinguish contradictory support from absent support |
| **manualSearch** | source acquisition request | not evidence that the search was performed |
| **modelingGap** | missing model construct / residual | not approval to create or edit Wikidata objects |

**Already implemented finite generic owner:** The declaration **ambiguousHidesDistinctSupport** is a consumer non-descent witness: a single ambiguous projection hides two distinct support positions, **both** versus **neither**. The module also has **ambiguousIsNotSufficientForSupport** and **ambiguousCannotFactorThroughSupport**, explicitly reusing **ConsumerDescentMinimalObserverExact**. No new sixfold, tetralemma, intersectional or factorisation calculus is needed. Fresh latest-head Agda acceptance of the WebKB/NORA junction remains a separate gate.

**Source and governance separation:** NORA authorship and user interface belong to Éder Porto. WebKB owns the original source FL ontology assertions. Stefan Zipproth/acrion is the upstream Zelph author/source owner. Crenshaw's intersectionality and the cited sheaf-hypergraph literature are correctly attributed as influences, not as authors of the DASHI lemmas. DASHI/SLR/ITIR proposals are **independent interoperability work**, not already-shipped NORA features.

The existing [author-facing NORA handoff in SensibLaw #514](https://github.com/chboishabba/SensibLaw/blob/agent/nora-review-source-preserving-maxcut-20261114/docs/handoffs/NORA_Developer_Handoff_ASD_STE100_20261114.md) requests a candidate exchange with source dataset/field/revision, candidate Wikidata Q/P identity, method, relation kind, reviewer/context, review choice/reason, evidence references and provenance. It is a **candidate read-only contract**. It neither authorizes Wikidata editing nor certifies author approval.

### NORA-specific remaining maximum-cut gates

| Gate | Proposed bridge / witness | Exact closure condition |
| --- | --- | --- |
| N1 | **webKBToNORAAttributedCandidateExact** | WebKB source/creator/revision and relation semantics survive candidate conversion |
| N2 | **noraReviewChoiceNotTruthPromotion** | reviewer choice cannot manufacture source truth or Agda proof |
| N3 | **noraAmbiguousConsumerNonDescentReuse** | existing ambiguity witness imported at the WebKB-specific consumer |
| N4 | **noraManualSearchToITIRBoundedPlan** | action yields a bounded, pending source-acquisition plan, not a completed fetch |
| N5 | **noraModelingGapPreservesResidual** | missing modelling axis survives coarse-graining and review |
| N6 | **noraReviewSourceRevisionReplayExact** | identical source/revision/reviewer/candidate after SLR persist/reload |
| N7 | **webKBWikidataNoraSameObjectBridgeRequiresReceipt** | lexical identity alone cannot conflate ontology classes, QIDs and review items |
| N8 | **noraAuthorFeedbackExportContract** | author-consented external feedback/export can be round-tripped; not yet received |

**All N1–N8 are proposed integration targets, not newly kernel-checked declarations.** N3's generic underlying lemma already exists. One decisive experiment holds the coarse UI label “ambiguous” constant while varying support between both and neither; a sufficient observer must retain the discriminating residual.

## 17. ITIR MCP: reuse the tools already registered

Existing [ITIR MCP governance tools](https://github.com/chboishabba/ITIR-suite/blob/main/itir-mcp/src/itir_mcp/governance_tools.py) and [registry](https://github.com/chboishabba/ITIR-suite/blob/main/itir-mcp/src/itir_mcp/registry.py) already expose the following tool names, including the disjointness tool registered by its separate module:

| Tool | Existing scope | New WebKB/NORA seam |
| --- | --- | --- |
| **itir.wikidata.review_packet** | read-only statement/evidence review | retain original source and proposed reviewer role |
| **itir.wikidata.object_review_bundle** | normalized review bundles | do not conflate object, source and candidate |
| **itir.wikidata.migration_candidate** | migration candidate proposal | no editing authority from the packet |
| **itir.wikidata.disjointness_report** | ontology disjointness report | conflict evidence must be scoped to source/world |
| **itir.wikidata.tooling_profile** | governed capability summary | report planning/transport limitations |
| **itir.zelph.hf_manifest_contract** | normalize HF shard manifest contract | pin immutable original revision and digest |
| **itir.shard.route_selector** | route logical selectors to source chunks | original QID/name/section identity required |
| **itir.shard.bounded_graph_slice_plan** | estimate and constrain bounded shard reads | make residual acquisitions explicit and bounded |
| **itir.shard.payload_probe** | prepare bounded physical data probes | a probe plan is not a successful fetch |
| **itir.zelph.partial_closure** | conditional evidence from partial graphs | absence cannot be concluded without coverage |

See the [existing ITIR HF/Wikidata MCP locator on PR #14](https://github.com/chboishabba/ITIR-suite/blob/agent/nat-filtered-route-producer/docs/planning/zelph_hf_wikidata_mcp_locator_20261114.md) for exact implementation paths and physical runbook. The tool registrations were verified from repository source; **this round did not execute their remote handlers or a full shard decode**.

**Architecture:** NORA manualSearch or the selected consumer's firstResidual → existing ITIR bounded plan + route selector → physical evidence receipt → read-only review packet → production SLR original-evidence persist/reload → consumer-specific Agda admission. Do not fork a parallel MCP interface, graph engine, review store, or collector.

## 18. Zelph Hugging Face publication, physical route and original-source boundary

[Zelph upstream sharding documentation](https://zelph.org/sharding/) and the [acrion/zelph HF dataset](https://huggingface.co/datasets/acrion/zelph) now publish/document the dataset layout. An older July 2026 audit's missing-metadata observation is historical, **not** a current assertion of unpublished shards.

| Graph | Published manifest path | Limit |
| --- | --- | --- |
| Full 2026-03-09 Wikidata | **wikidata-20260309-all/wikidata-20260309-all.hf-v2.json** | graph between entities, not the full original Wikidata statement/qualifier/evidence model |
| Pruned-small 2026-03-09 | **wikidata-20260309-all-pruned-small/wikidata-20260309-all-pruned-small.hf-v2.json** | reduced coverage; does not justify whole-Wikidata negatives |

The HF locator uses the source prefix **hf://datasets/acrion/zelph/**, with the full example **.load-partial hf://datasets/acrion/zelph/wikidata-20260309-all/wikidata-20260309-all.hf-v2.json left=0**. Native layout includes each artifact's **.hf-v2.json** manifest, **artifact.index.json**, and **shards/left**, **shards/right**, **shards/nameOfNode**, **shards/nodeOfName**.

**A manifest location is not a paid physical shard.** In particular, the example **left=0** does not resolve the selected Nat QID. An exact source-name→node mapping and section-global chunk range must be read from the pinned original index/sidecar. Regenerated graph IDs and guessed shard numbers are forbidden.

### The one original-physical maximum cut still to run

1. Pin the **immutable HF revision**, manifest and route-sidecar byte hashes, source version and full chunk geometry.
2. Resolve the **five Nat QIDs from the existing Nat tranche** without inventing numeric node IDs or language/direction routes.
3. Fetch/authenticate bounded original shard objects or HTTP206 ranges, verifying Cap'n Proto packing, offsets and digests against the same original source.
4. Establish selected adjacency/query-family soundness and completeness **relative to the actually fetched, covered source domain**, preserving unknown results for missing shards.
5. Feed source-qualified receipts into the **existing** ITIR review packet and SLR persisted/reloaded review contract, not directly into author-approved NORA or Wikidata edits.
6. Record source SHA, commands, environment, test logs, full exact-head exit receipts in existing ITIR #14, SLR #10, SensibLaw #514 and DASHI #1506.

**Source/code status:** HF manifest locations and ITIR tool names located; prior PR-local synthetic/finite tests may be cited at their *previous accepted heads only*. An immutable current dataset SHA, authentic five-QID physical routes, exact bytes/decoder, real SLR production replay and Éder-approved NORA export are **OPEN**.

**Proposed remaining physical bridge targets:** **zelphHfOriginalManifestPinnedDigest**, **zelphNatFiveQIDOriginalNamePartition**, **zelphNatOriginalShardDecodeSameObject**, **webKBNoraZelphClaimSourceQualifierTransport**, **noraPartialGraphNoClosedWorldAbsence**, **slrNoraWebKBOriginalEvidenceRoundTrip**.

## 19. Consolidated acceptance boundary

**Present:** original A–H WebKB/observer maximum-cut ledger; existing Agda theorem owners for intersectional non-factorability, consumer sufficiency, minimal residual, coarse/fine reopening and typed hyperfabric; NORA finite local proposed five-choice model and author-facing handoff; ITIR registered tool interfaces; current published Zelph manifest locations. The 14/14 standalone finite Python tests were rerun locally on 15 November 2026 and are **not** a source-native FL or Agda/SLR validation receipt.

**Still open:** original WebKB FL/native code and pinned HTML fixture; WebKB-specific Agda kernel refinement; original actual Zelph five-QID shard receipt; SLR production persist/reload; NORA live export and developer review; theorem-world certificate and learner KV tensor-context parity.

**Non-promotion rules:** source assertion ≠ accepted proof; same label ≠ same concept; review choice ≠ ontology truth; incomplete graph ≠ absence; coarse query sufficiency ≠ world completeness; typed local hyperedge ≠ compatible global section; matching semantic label ≠ matching KV tensors; acquiring a residual ≠ authority to edit.

The **single existing PR per repository** remains the rule. No DOCX is part of the required deliverable.


## 20. User-story correction: NORA as situated semantic crosswalk and residual producer

**Verified source audit: 15 November 2026.** This corrects the too-linear diagram previously used in discussion. **NORA is not a mandatory step between Zelph and SLR, nor a new canonical truth or state owner.** NORA (Éder Porto's independent alpha) is a *possible opt-in consumer-specific ontology review adapter* and producer of reviewer-attributed mapping decisions, conflicts, unanswered questions and acquisition requests. The true live NORA export/API remains an external open gate.

### 20.1 Actual user-story ownership and required separation

| Existing user-story owner | Exact story/contract | NORA integration consequence |
| --- | --- | --- |
| [TiRCorder capture](https://github.com/chboishabba/tircorder-JOBBIE/blob/master/README.md), [connector contract](https://github.com/chboishabba/tircorder-JOBBIE/blob/master/docs/tircorder_connector(1).md) | Capture audio, diarisation, transcript, utterances, timestamps and source receipts; explicit ban on semantic/ontology fields in capture packets | Review later through immutable original utterance/span reference; **do not** write concepts or legal claims into the capture artifact |
| [StatiBaker README](https://github.com/chboishabba/StatiBaker/blob/main/README.md), [ingest contract](https://github.com/chboishabba/StatiBaker/blob/main/ITIR_INGEST_CONTRACT.md), [loss profile](https://github.com/chboishabba/StatiBaker/blob/main/LOSS_PROFILES.md) | Append-only deterministic temporal state compilation; read-only ID/reference overlays; explicit loss; no meaning rewrite | NORA decision can be an externally referenced *event about review*, not a rewrite of SB canonical events or a diagnosis |
| [ITIR suite stories](https://github.com/chboishabba/ITIR-suite/blob/main/docs/user_stories.md) | US-01–03 context, knowable-then vs known-later, drift; US-11–16 personal memory, review, trauma-safe reconstruction, private/professional handoff and anti-false-coherence; US-17 wiki revision follow | Scoped optional consumer views; preserve authored source, time, uncertainty, standpoint and abstentions, even when ontology labels match |
| [SensibLaw Wikidata editor/persona/partial-stack stories](https://github.com/chboishabba/SensibLaw/blob/main/docs/user_stories.md) | Work/home legal/psychologist scopes; ontology workers review identity/role/time/sourcing pressure, not unreviewed authority; source-sensitive user stories across legal, audit and private users | A mapping may be adequate for one professional's exact question and inadequate for another; no cross-scope forced consensus |
| [SLR production roadmap](https://github.com/chboishabba/slr/blob/main/docs/ROADMAP.md) / [sprint board](https://github.com/chboishabba/slr/blob/main/docs/SPRINTS.md) | source/revision/span/observation → consumer residual → producer plan → bounded acquisition → candidate → explicit review/payment → W(n+1) → rediagnosis; Sprint 2 active shared evidence convergence | SLR, not NORA, owns durable production evidence, admission, source acquisition and selective dependency reopening |
| [ITIR WIKI-US-01–04](https://github.com/chboishabba/ITIR-suite/blob/main/docs/user_stories.md#wiki-and-public-knowledge-operator-integration-stories) | Registered read-only review/object/migration packets; governance; P2738 disjointness; cross-corpus provenance | Reuse existing ITIR MCP, never a separate edit service |
| [ITIR WIKI-US-05 / US-26 (PR #14)](https://github.com/chboishabba/ITIR-suite/blob/agent/nat-filtered-route-producer/docs/user_stories.md) | exact immutable QID→HF physical name shard, no false negative completeness, (QID, native GUID) population accounting | Physical graph evidence is not a native Wikibase qualified statement, P854 source support or edit permission |
| [SLR WIKI-US-01–03 (PR #10 branch)](https://github.com/chboishabba/slr/blob/agent/source-unit-wikimedia-handoff/docs/user_stories_wikidata_zelph_mcp_20261114.md) | Native source and statement review, existing MCP source execution, bounded physical slices, full Nat review | Use existing SLR producer/S29 paths; authentic NORA export and persisted reviewed native/graph join still open |

The suite's own words: **ITIR preserves what happened, SensibLaw constrains what can be claimed, and StatiBaker refuses to tell you what it means.** Context is mandatory, interpretation optional, expanding context cheaper than compressing it, and context removal logged. The [SensibLaw extractor→ontology contract](https://github.com/chboishabba/SensibLaw/blob/main/docs/extractor_ontology_mapping_contract_20260213.md) separately requires deterministic pinned lexical/synset resolution and abstention on ambiguous mappings, not LLM inference promoted to canonical ontology identity.

### 20.2 Corrected architecture (multiple entry/exit points)

~~~text
   TiRCorder + primary sources                 StatiBaker time/state observer
             |                                           |
             +------------> ITIR source/context ----------+
                                  |
                       SLR canonical evidence state
                                  |
             consumer-specific residual / unresolved question
                     /                         \
                    v                           v
       SLR existing bounded producer     NORA optional ontology review
       local → Zelph HF → governed      source/standpoint/consumer/candidate
       revision-pinned live                         |
                    \                           /
                     +---- candidate evidence -+
                                  |
                   independent review / payment
                                  |
                  persisted W(n+1) + sparse reopen
                                  |
          scoped professional/personal/ontology consumers
                                  |
              DASHI Agda conditional proof authority
~~~

Do not make NORA a compulsory gateway for source capture, state compilation, legal review, formal theorem checking, or user knowledge. An ontology reviewer may use it; another consumer may never call it. Nor may NORA's reviewer status itself authorize a Wikidata write, legal finding, user diagnosis, or a global ontology merge.

### 20.3 Exact situated sufficiency and residual connection

Fix a source situation, world/temporal context, observer and consumer question. A coarse projection pi is sufficient for question q only if an answer on pi exists with q = answer ∘ pi (existing **FactorsThrough**, **ConsumerSufficient**). A pair of situations with equal pi but different q is a **ConsumerNonDescentWitness**; post-composing/recharting pi cannot repair it (existing **IntersectionalNonFactorability**). Acquire a query-relevant residual r and test the refined observer (pi,r), using **ConsumerIndexedResidualRefinementExact**, **RequiredObserverAxisJoinAdequacyExact**, **CoarseFineRelativeFibreExact** and the existing typed hyperfabric.

NORA's internal five-choice review projection is deliberately an **INTERNAL DASHI design**, not a confirmed native Éder Porto NORA export. In that model valid/invalid are scoped judgements, ambiguous is unresolved, manual_search is an acquisition request, and modeling_gap is a modelling residual. Even the same word or Wikidata QID cannot force one consumer's choice onto another's context. A true contradiction requires same-source/same-claim/time/observer scope; disagreement may be legitimate without such identity.

### 20.4 Proposed exchange, not yet native NORA API

~~~text
ReviewRequest:
  source_manifestation_id, source_revision_id, raw_span_or_native_GUID,
  source_hash, capture_context_and_time, observer_scope, access_scope,
  consumer_question, candidate_ids_and_relation_kinds, evidence_refs,
  coverage_status, required_discriminator

ReviewReturn:
  request_digest, reviewer, standpoint, review_time, candidate_id,
  review_disposition, rationale, inspected_evidence_refs, uncertainty,
  residual_kind, next_evidence_request, no_semantic_payment, no_edit_right
~~~

Must not identify an article oldid with a Wikibase entity revision, original HF graph revision or P854 primary-document revision. Native NORA export, review terminology and consent/scopes require original author/source validation. A proposed relation ('equivalent', subtype, part-of, related) is typed; lexical identity is never enough.

### 20.5 Three story-complete high-alpha acceptance pilots

| Pilot | Exact original stories | Exit/decisive witness |
| --- | --- | --- |
| **U1. Nat wiki mapping review** | ITIR WIKI-US-01/03/04/05; SensibLaw Wiki editor; SLR WIKI-US-01–03 | Pin original source and selected HF physical route, independent native (QID, GUID, qualifiers, references, P854) evidence, real Éder Porto NORA review fixture, SLR persisted S29 decision, restart, scoped reopen; negative coverage and held alternatives survive |
| **U2. One utterance, two consumers** | ITIR-US-11/13/15/16; SensibLaw lawyer/psychologist and private→professional; TiRCorder capture | Same immutable capture serves two scoped queries, coarse mapping collision is shown, one consumer receives sufficient residual while the other may abstain; no SB source/state mutation or cross-scope interpretation |
| **U3. Temporal/role/source drift** | ITIR-US-01/02/03; SB state and explicit loss; SLR recurrent acquisition/replay | Change source revision; preserve what was knowable then, former decisions, and old source; only dependent consumer reviews reopen; unrelated consumers/state replay unchanged |

**Remaining exact story gates US-N1–US-N8 (not additional generic Agda theorems):** US-N1 original NORA export, US-N2 two-consumer scoped review, US-N3 real collision→residual→fresh factorisation, US-N4 immutable TiRCorder/SB source, US-N5 SLR native candidate→review/payment→restart and sparse reopen, US-N6 temporal/role/consent isolation, US-N7 original WebKB FL code/DAG soundness, US-N8 theorem/learner no-promotion. Generic Agda owners are present; real source/physical/current-head specializations remain open.

**Rollup rule:** use existing Agda #1506, ITIR #14, SensibLaw reference #514 and existing SLR #10/#76; no parallel SLR review store, TiRCorder ontology parser, SB semantic reducer or global NORA truth layer. The SLR roadmap reports Sprint 1 certified at its pinned head; that does *not* certify an original NORA integration or Sprint 2.

## 21. CORRECTED: law-as-algebra is institutional schema crosswalking; NORA's value is not a distinct problem category (15 November 2026)

**This section supersedes the earlier Section 21 comparison.** The prior claim that NORA uniquely targets "institutional metadata-schema crosswalk authoring" whereas we mainly do evidence, constraints and governance is **incorrect**. We failed to account for SensibLaw's actual user stories, L0–L6 institutional ontology, legal-system/value-frame onboarding, cross-jurisdiction projections, and DASHI's law-as-algebra proof structure. These are already **institutional schema authoring, alignment, transformation and review problems**. Merely changing the institution from a museum to a court, regulator, local government, legal service, company or community normative system does not create a new mathematical problem class.

The valid remaining distinction is **scope/UX/current implementation maturity**, not product essence. Éder Porto owns independent NORA; no original NORA alpha code/export has been inspected or verified end-to-end here. The [author's Ontology Mapper technical plan](https://commons.wikimedia.org/wiki/File:Ontology_Mapper_-_Technical_Development_Plan_-_pt.pdf) documents institutional field-to-Wikidata mapping proposals, ranked candidates, five choices (*válida*, *inválida*, *ambígua*, *busca manual*, *lacuna de modelagem*), authoring/proposed properties, reused decisions, preview, exports and direct/federated Wikibase targets. These are intended capabilities, not proof of deployed alpha coverage. Our internal five-choice Agda model is **aligned with the documented author choices**, not a verified native NORA API schema.

### 21.1 What our own user stories actually require

| In-repository evidence | Real institutional authoring / mapping problem | Maturity claim we can support |
| --- | --- | --- |
| [SensibLaw ontology architecture](https://github.com/chboishabba/SensibLaw/blob/main/docs/ontology.md) | L0 source/utterance → L1 actors/events → L2 cases/claims → L3 legal systems/authority/provisions → L4 wrong types/elements/duties → L5 protected interests/harms → L6 value frames/perspectives/remedies; explicit **Programmatized Liability Stack (Crosswalk)** | Defined layered institutional ontology and crosswalk **contract**; not proof of complete authoring UI |
| [Ontology onboarding playbooks](https://github.com/chboishabba/SensibLaw/blob/main/docs/onboarding_playbooks.md) | Author a jurisdiction/authority hierarchy; seed legal sources, provisions, citations, wrong-type links, value-frame/cultural semantics; migrate and validate | Documented onboarding and checks; individual workflows must be tested separately |
| [SensibLaw user stories](https://github.com/chboishabba/SensibLaw/blob/main/docs/user_stories.md) | Regulatory applicability mapper; compliance/regtech analyst; institutional buyer/integrator; customer onboarding schema mapping; external counsel; regulator; Wikidata editor/ontology reviewer; personal-to-professional source handoff | **User stories** do not imply all product UI capabilities are deployed |
| [SensibLaw implementation coverage](https://github.com/chboishabba/SensibLaw/blob/main/docs/planning/user_story_implementation_coverage_20260326.md) | AU/Wikidata/GWB review geometry, central promotion gate, candidate/source bundles, split verification, source-follow and bounded personal handoffs | Explicitly distinguishes tested reference/CLI slices from wider unbuilt UX |
| [ITIR wiki stories](https://github.com/chboishabba/ITIR-suite/blob/main/docs/user_stories.md) | WIKI-US-01–04: revision-pinned qualified statement review, QuickStatements/OpenRefine tooling profiles, disjointness/migration candidates, cross-corpus reconstruction | Registered existing read-only MCP handlers; not arbitrary end-to-end schema wizard |
| [SLR production roadmap](https://github.com/chboishabba/slr/blob/main/docs/ROADMAP.md) | Source/revision/span→consumer residual→bounded acquisition→candidate→review/payment→world; **Sprint 4 M4.7 cross-jurisdiction projection**; M4.1–M4.6 workspaces, research UX, drilldown and exports | Sprint 1 reported certified at pinned head; Sprint 2 active; **Sprint 4 product is a roadmap, not a completed UI** |
| [DASHI statutory-rule algebra](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Cognition/PNF/SensibLawStatutoryRuleStructureAlgebraExact.agda), [legal world/revision](https://github.com/chboishabba/dashi_agda/blob/master/DASHI/Law/LegalWorldRevisionReconstructionExact.agda) | Typed provisions, jurisdiction-scoped definitions, authority roles, amendments/repeal, compilation into rules, temporally contextual world and dependence-aware reopen | Formal source declarations present; this audit did **not** re-run an exact-head Agda kernel acceptance |
| [ITIR architecture guide](https://github.com/chboishabba/ITIR-suite/blob/main/SL-arch-guide.md), [SLR roadmap](https://github.com/chboishabba/slr/blob/main/docs/ROADMAP.md) | One generic reconciliation algebra over typed semantic deltas/residuals; source identities are not DB surrogates; publication only at explicit authority boundary | Existing target execution architecture, not a basis for another NORA production store |

**A legal statute is institutional data with additional normative constraints**: institutionally scoped terms, roles and capacities, effective dates, hierarchies of binding authority, conditions, exceptions, defeaters, burdens, rights, duties and remedies. An ontology mapping from that source into the legal algebra is not an inferior form of GLAM catalogue field mapping; it is at least as demanding on semantics. Formal equivalence or label matching alone cannot grant legal applicability or truth.

### 21.2 Shared abstraction, not "our back end" versus "their authoring"

For a source schema S, target schema T, standpoint/observer o, legal or institutional world w, and consumer query q, a candidate schema morphism m is useful only if it preserves the query-relevant predicates and evidence identities. Use the *existing* DAG/typed hyperfabric and consumer sufficiency:

- **Draft**: a proposed source-field → target-property/class/relation mapping is an attributed candidate, not accepted truth.
- **Check**: test datatype, unit, cardinality/1-to-N, source anchors, hierarchy, authority, scope and time, and application-specific obligations.
- **Counterexample**: a collision with equal coarse projection but differing consumer answer is a concrete `ConsumerNonDescentWitness`. Recharting labels does not pay it.
- **Refine**: recover the first source-backed consumer-relevant residual, join sufficient observer axes, and recheck `FactorsThrough`; do not assume that every independently sufficient axis yields an adequate intersection.
- **Review**: different situated reviewers may legitimately produce nonidentical decisions; source, observer, consumer, validity window, access scope and actual evidence remain separate.
- **Admit**: the SLR review/payment gate, not either UI or external ontology, decides which bounded evidence can alter an admitted world. Export/public write requires an independent authority gate.

The same apparatus supports archive-to-Wikidata mapping, law-to-normative-algebra authoring, cross-jurisdiction legal applicability, GLAM institutional imports, and personal-to-professional record reinterpretation. **NORA is an optional external *peer front-end / source of mapping proposals*, not the human interpretation layer missing from our stack.** ITIR/SensibLaw already specify multiple human review and consumer workbenches.

### 21.3 Capability parity: distinguish problem solved from UX shipped

| Function | Ours | Native NORA | Differential evidence required |
| --- | --- | --- | --- |
| Institution-specific ontology/source schemas | Legal L0–L6, jurisdiction/source onboarding, external ontology refs and tests | Museum/archive/library source fields in author plan | Actual independent source examples on both sides |
| Candidate relation/mapping authoring | Ontology/split/constraint/reference routes plus planned richer workbench | Author plan has property ranking, five human choices, field authoring | Working UI/API traces, preserved exact source IDs |
| Modelling gaps & proposed terms | Diagnostic, abstention, native/migration candidates; typed residuals | Intended property-proposal drafting and manual search | Real missing-model case; draft expressivity and review cost |
| Collaborative decision reuse | Durable review/provenance and context-scoped reopening; no verified community-wide reuse wizard | Intended shared mapping memory | Real revision/observer-scoped reuse, negative-transfer controls |
| Preview/validated import export | ITIR batch tooling governance, source receipts; broader user-facing authoring/export not proven deployed | Intended example item and QuickStatements/OpenRefine exports | Exact item examples, datatype validity and no-write preflight |
| Formal semantic preservation | DASHI `FactorsThrough`, `ConsumerSufficient`, non-descent, legal-world semantics, hyperfabric | No native formal proof demonstrated | Source-specific invariant/counterexample and a kernel receipt |
| Durable production admission/replay | SLR owns; no new store | Native NORA data model unknown | If needed, one candidate-only adapter into existing SLR |

**Neither project gets credit merely for a roadmap.** Do not infer that ours has a polished universal crosswalk editor; do not infer NORA has deployed federation, batch export or superior accuracy from a design document. Also do not erase our institutional authoring use cases simply because the currently accepted product slice has more CLI/contract implementations than end-user UI.

### 21.4 Replace false "NORA vs our backend" experiment with shared-institution benchmark

Use **two complementary cohorts**:
1. **GLAM field crosswalk**: genuine immutable museum/archive/library metadata fields → appropriate Wikidata/Wikibase mapping with false-cognate, datatype, cardinality, 1-to-N, invalid and missing-property controls.
2. **Legal institutional crosswalk**: a revision-pinned statute/provision/definition, jurisdictional authority hierarchy and case/role relationship → existing SensibLaw legal ontology and qualified legal-rule structure; time-sensitive applicability, obligation/exception, cultural/standpoint and consumer non-descent controls.

The legal cohort tests *our* existing machine's representation and source-bound review and what an optional NORA generic mapping interface can express; **it is not fair to score NORA as failing its declared GLAM-focused product just because it does not implement full legal reasoning**. GLAM cohort tests both projects only for overlapping supported crosswalk operations. Report coverage and abstention instead of forcing unsupported tasks to produce scores.

Three *capability-scoped* arms: **Ours-as-built** (current CLI/MCP/reference/UI), **NORA-as-built** (real deployed author-exportable alpha), and **composition** (only if consented original NORA input/output supports a read-only bridge). Blind gold must be independent and preserve semantics, original field identity, source revision and context. Metrics: valid mappings per reviewer-hour, false equivalences, structural violations, recoverable provenance, modelling-gap accuracy, exact 1-to-N preservation, time and maintenance complexity, reviewer transfer between institutions, and subject-specific contextual sufficiency.

A GO threshold is a **proposal** (e.g., 20% operator-time benefit at noninferior correctness) rather than a finding. **NO-GO for integration** if overlap plus bridge cost gives no advantage; **LIMITED ADOPT** for an excellent specific UX/editor affordance. **NO EVIDENCE** if no original native author fixture or matched run; never manufacture performance figures. NORA does not need to "earn its keep" by solving legal ontology semantics; it must offer some empirically useful affordance in its actual product scope, and our collaboration must improve our own goals.

### 21.5 Corrected ownership and maximum-cut next deliverables

- Keep source authority and semantics at current owners: DASHI Agda #1506, ITIR #14, SensibLaw reference #514, SLR current source/evidence/S29 owners. No new ontology DB, solver, user-story suite, or separate NORA review-admission machine.
- Establish **law-as-algebra ↔ generic institution schema** mapping type with existing source-qualified object IDs, structured relation kind, typed constraints, time, legal source validity and consumer scope; reuse existing Agda law + observer theorem owners and SLR candidate/review state. This is a *new domain-specific bridge/fixture*, not a new core calculus.
- Produce a two-cohort reference suite and retain failed mappings as typed residuals. Distinguish **source-backed mathematical equivalence** from partial mappings, candidate similarities, and unknowns.
- Verify real original NORA alpha input/output schema, attributable author choice and export before proposing any native adapter; use the five choices from the original plan as **design context**, not guaranteed deployed data structures.
- Prioritize legal/GLAM crosswalk parity and source-preserving ergonomic comparison **after** existing SLR physical-source / same-source / persisted-replay gates; those independent production gates remain open whether NORA participates or not.

**Corrected conclusion:** The overlap is *larger* than our prior write-up admitted. Both projects address situated institutional schema mappings and review. Our law-as-algebra work is a substantial example of this. Possible NORA value is a particular authoring UI/community workflow or reuse mechanism, which must be demonstrated, not a supposedly unique capability class.
