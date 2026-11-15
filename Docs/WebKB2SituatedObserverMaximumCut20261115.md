# WebKB-2 × DASHI situated ontology / PNF-world / hyperfabric — maximum-cut integration

**Date:** 2026-11-15  
**Owner:** Existing DASHI ontology/trie/hyperfabric rollup PR #1506 (do not create another PR).  
**State:** SOURCE AND REUSE AUDIT; NEW WEBKB-SPECIFIC AGDA/PHYSICAL/PRODUCTION GATES OPEN.  
**Primary source:** https://www.webkb.org/kb/top/theKB_categs.html

## Objective and discipline

Integrate WebKB-2 source-qualified FL concepts and relations into the **existing** DASHI consumer-indexed observer and source-provenance calculus, with Agda as the golden semantic interface, sparse typed hyperfabric as the local/gluing carrier, and SLR/ITIR as persistence and source-acquisition layers. Do not construct a new parallel ontology, trie, PNF or world runtime.

Five independently paid gates: (1) original source bytes and syntax; (2) faithful parsed/attributed claim representation; (3) derivation conditional on declared context and admission; (4) consumer-specific sufficiency and indexed parity; (5) production persist/reload. None entails world completeness, observer authority, theorem truth, or learner KV equivalence.

## Critical WebKB source distinctions

Native FL uses `<` subtypeOf, `>` subtype, `^` instanceOf, `:` instance, `=` equality, `-` inverse, `!` simple exclusion, `/` closed exclusion (exclusive/complete partition under the source's side conditions), `&` related (fuzzy), and `>part` subdomain. Native binary category specialization codes are read **right to left**, and may be inherited or overridden. They are **not** proven to be ordinary trie-prefix encodings. Preserve original code and source span; verify any compiled index by independent reachability parity.

## Actual existing Agda owners (do not copy/rename)

- `DASHI.Core.IntersectionalNonFactorability`: `FactorsThrough`, `NonFactorabilityWitness`, `witnessRulesOutEveryFlatFactorisation`, `postcomposeNonFactorability`, `rechartingCannotRecoverErasedPhenomenon`.
- `DASHI.Core.QueryFactorisationSufficiency`: `InquiryQuestionFamily`, query-indexed `FactorsThrough`, `StaticSufficient`, explicit no-world-completeness boundary.
- `DASHI.Core.ConsumerDescentMinimalObserverExact`: `FibreConstantFor`, `ConsumerSufficient`, sectioned-projection descent, `LeastSufficientConsumerObserver`, `ConsumerNonDescentWitness`.
- `DASHI.Core.ConsumerFibreRepairExact`: `refinementRepairSeparatesWitness`, `factorizationRepairSeparatesWitness`.
- `DASHI.Core.ConsumerIndexedResidualRefinementExact`: `ConsumerRelevantCollision`, `residualMustSeparateRelevantCollision`, `consumerRelevantResidualGivesStrictRefinement`.
- `DASHI.Core.RequiredObserverAxisJoinAdequacyExact`: `jointAxis`, `retainsBothGivesJointFactorisation`.
- `DASHI.Core.MinimalSufficientResidual`, `DASHI.Core.ProvenanceBearingQuotient`, `DASHI.Core.CoarseFineRelativeFibreExact`, `DASHI.Core.ObserverRefinementCore`.
- `DASHI.Reasoning.TypedHyperfabricCore`: typed stalks, incidence/restrict, compatible `GlobalSection`, provenance and obstruction.
- `DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact`: coverage/epistemic state, source attribution, source/renderer/world non-promotion.
- `DASHI.Interop.PNFHyperfabric369`, `DASHI.Ontology.WikidataEpistemicBridge`, existing Zelph/ITIR/SLR physical source-route owners.

Remote default-branch declarations were read at authoring time, **not** Agda-kernel rechecked on this PR head. Reconcile current branch and import owners before new code.

## One reusable theorem, many consumer instances

For situated states `S`, an observer/coarse projection `pi : S -> V`, and an authorised consumer `q : S -> Q`:

`FactorsThrough(pi,q) := Sigma (g : V -> Q). forall s, q(s) = g(pi(s))`.

Consumer sufficiency means `pi x = pi y -> q x = q y`. For sectioned projections the repo already supplies the explicit-factorization/descent equivalence. A collision `pi x = pi y` with `q x != q y` refutes sufficiency and *any* post-composition/rechart of `pi`. Correct refinement must add consumer-relevant evidence that separates the collision, not relabel a compressed state. `pairObserver` is a least joint refinement in the information order, but separate axes alone do not prove the joint consumer adequate.

A sparse hyperfabric must preserve the source/revision/world/observer/authority fibre needed for a given query, not materialize the entire Cartesian product of dimensions. Acquire the **first typed residual** and rerun the consumer; the acquisition produces a candidate, not automatically a fact. A source claim, a proof derivation, a map rendering, and a kernel-accepted theorem are different authority types.

## Original 39 gates — retain as WebKB-specific targets

A1–A6: `webKBFLParsePrintRoundTripExact`, `webKBSourceQualifiedIdentifierInjective`, `webKBRelationSymbolInterpretationExact`, `webKBPartitionSyntaxPreservesClosure`, `webKBSourceSpanProvenancePreserved`, `webKBCanonicalDAGIdempotent`.

B1–B8: `ontologySubtypeReflexiveTransitiveClosureExact`, `ontologyReachabilityDecisionSoundComplete`, `ontologyMultipleInheritancePathPreserved`, `ontologyInstanceSubtypeTransport`, `ontologyEquivalentClassesQuotientSound`, `ontologyDisjointSubtypeContradictionWitness`, `ontologyCompletePartitionCoverageExact`, `ontologyRelationSignatureTypingPreserved`.

C1–C7: `webKBBinaryCodeDecodeRoundTrip`, `webKBBinaryCodeSpecializationSound`, `webKBBinaryCodeSpecializationComplete`, `hyperfabricMultiParentUnionExact`, `hyperfabricIncrementalEdgeInsertionExact`, `hyperfabricCanonicalQueryInvariant`, `hyperfabricIndexedReachabilityBisimulation`.

D1–D7: `ontologyAssertionProvenanceNonErasure`, `ontologyCrossSourceEqualityNotAutomatic`, `ontologyContextualConflictWitnessExact`, `ontologyBeliefRevisionNonDestructive`, `worldIndexedAssertionIsolation`, `worldTransitionPreservesDeclaredInvariants`, `ontologyWorldTransportRequiresBridge`.

E1–E5: `theoremWorldQualifiedConstantIdentity`, `theoremWorldDependencyGraphExact`, `theoremWorldOntologyAlignmentWitness`, `theoremWorldRetrievalSoundness`, `theoremWorldKernelAcceptanceFirewall`.

F1–F6: `pnfOntologyStateEmbeddingExact`, `pnfTransitionGraphSimulation`, `learnerMemoryProvenanceReconstruction`, `learnerKVSemanticCacheNoFalseReuse`, `learnerOntologyConstraintSoundMask`, `learnerOntologyConstraintCoverage`.

These are **target names**, not 39 absent generic lemmas or 39 successful Agda kernel checks. Reuse exact existing owners; make only WebKB-specific source transport, typed bridge and conditional index implementations.

## New observer and physical gates

**G1–G10:** `webKBSituatedObserverConsumerFibreExact`; `webKBConsumerDescentFromExistingCore`; `webKBNonDescentWitnessFromOntologyCollision`; `webKBRechartingCannotRestoreExcludedAxis`; `webKBRequiredObserverJoinIsLeastRefinement`; `webKBResidualRefinementSeparatesConsumerCollision`; `webKBSufficientForQueryNotWorldComplete`; `webKBHyperfabricLocalToGlobalRequiresCompatibility`; `webKBProvenanceReopeningPreservesOriginalClaim`; `webKBContextualAuthorityNonPromotion`.

**H1–H8:** `webKBFLGrammarCoverageForPinnedFixture`; `webKBClosedExclusionSoundAgainstPartition`; `webKBCodeBitOrderValidation`; `webKBCodeCandidateFilterNoFalseNegative`; `webKBOriginalByteRevisionHashSameObject`; `webKBHyperfabricIndexedQueryCertificate`; `webKBIncrementalSelectiveInvalidationExact`; `webKBSLRRoundTripEvidenceAndRevisionExact`.

**Hard mathematical cut:** same pinned original source/graph for A2/A3/A5→B1/B2/B4/B6/B7→G2/G3/G6/G7→C2/C3/C7+H4/H6. Native code alone cannot answer what an unseen node's claim means.

## Phased deliverables

| Phase | Owner | Required exit |
| --- | --- | --- |
| P0 | Agda ontology | Existing declaration reuse ledger, exact PR head and source hash |
| P1 | ITIR importer | Native FL grammar, source-span/revision receipt, unsupported-form handling |
| P2 | Agda | Kernel checked conditional subtyping, partition, conflict and consumer obstruction |
| P3 | hyperfabric + SLR | Indexed query parity, same-object proof receipts and revision invalidation |
| P4 | PNF/world | World-indexed claims, situated observer joins, first residual, candidate-only source admission |
| P5 | SLR/ITIR | Persist/reload byte/identity provenance, source coverage and no-answer diagnostics |
| P6 | Lean/LeechTransformer | Kernel theorem firewall; matched learner retrieval/context/cache ablations |
| P7 | all participating repos | One rollup PR each; pinned source/commit/test logs, no false source promotion |

## Discriminating tests

T1 diamond multi-parent; T2 cycle/preorder; T3 closed partition; T4 same-world conflict witness; T5 same lexical label/other namespace; T6 increment/rebuild parity; T7 cross-world isolation; T8 KV concept-match/context-mismatch; T9 unverified equivalence mapping firewall; T10 exhaustive finite digraph parity; T11 collision→residual repair; T12 postcompose no-recovery; T13 canonical provenance preservation; T14 query sufficiency≠world completeness.

A separate local Python reference harness was run with **14/14 tests PASS** on 2026-11-15, exhaustively comparing finite closure vs indexed closure for all 64 directed graphs on three labelled nodes. It does **not** implement native WebKB FL or source codes, cannot certify T3/T8, and is not an Agda/SLR/ITIR verification receipt. Attach source-hash-matched test artifacts and rerun before accepting this as a repository test gate.

## Explicitly open / no promotion

1. Real immutable original WebKB revision and bytes + licence/terms; source-native grammar and partition semantics.
2. Actual WebKB binary-code interpretation, sound/complete conditional index and original graph parity.
3. Kernel-checked WebKB-specialized G/H bridges; verified source provenance, conflict and revision/world transport.
4. SLR persist/reload and native ITIR acquisition/source workflows.
5. Lean-world theorem certificates and learner matched TinyStories/KV effectiveness/latency experiments.
6. Exact-head branch Agda and cross-repo CI/local verifier receipts.

No automatic `asserted relation -> truth`, `source label -> same object`, `coarse query sufficiency -> world coverage`, `local hyperedge -> compatible global section`, `evidence candidate -> user authority`, or `similar concept -> identical KV tensors`.

## Source and attribution

- WebKB-2 top categories: https://www.webkb.org/kb/top/theKB_categs.html
- DASHI existing original owners: https://github.com/chboishabba/dashi_agda/tree/master/DASHI/Core
- Existing ontology/trie/NORA rollup: https://github.com/chboishabba/dashi_agda/pull/1506
- Intersectional framing: Kimberlé Crenshaw, *Mapping the Margins* (1991); DASHI formalization is an independent mathematical interpretation.
- Typed hyperfabric source calibration: Duta et al., *Sheaf Hypergraph Networks*, arXiv:2309.17116; no empirical claims imported.
