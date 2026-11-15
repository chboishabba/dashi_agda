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
