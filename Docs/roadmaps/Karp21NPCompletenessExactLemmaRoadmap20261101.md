# Karp 21 NP-completeness: full exact-lemma roadmap (2026-11-01)

**Authority:** DASHI Agda source is golden; `chboishabba/dashi_lean4` and `openai/math` supply independently attributed Lean donors.  
**Delivery PR:** [dashi_agda #1445](https://github.com/chboishabba/dashi_agda/pull/1445).  
**Scope:** all *21 historical problems*, all *20 historical direct reduction edges*, and the eight follow-up topics (some outside the 21).  
**Status principle:** code in a GitHub branch != Agda kernel-accepted theorem != source-paper result != same-object port. No general NP-completeness or P != NP is claimed by this roadmap.

## O/R/C/S/L/P/G/F: objective and contracts

- **O — Objective:** one typed executable, bounded and independently auditable reduction network preserving Karp (1972) problem definitions. Exactly one DAG owner per distinct mathematical proposition.
- **R — Prior art:** Cook (1971), DOI `10.1145/800157.805047`; Karp (1972), DOI `10.1007/978-1-4684-2001-2_9`; Zuckerman (1996), DOI `10.1137/S0097539794266407` (non-standard constrained approximation variants); Ford and Fulkerson (1956) and Edmonds and Karp (1972) (separate max-flow line); Goemans and Williamson (1995) (separate MAX CUT approximation). Original priority is not reassigned to DASHI or OpenAI.
- **C — Code:** reuse `DASHI.Mathematics.Complexity.PolynomialReductionExact`, `CookLevinCircuitGCTBoundary`, `PNotEqualsNPClayCoreExact`, and `Karp21ReductionTransportExact`. New graph semantics in #1445 are not a substitute for finite, size-bounded reductions.
- **S — Safety/claims:** keep historical decision, optimization, approximation, integer/signed weights, nonnegative capacities, and scheduling variants distinct. Boolean proof-of-status flags, search hits and finite numerical regressions never close a theorem.
- **L — Lemmas:** names below are *required exact target declarations*, NOT currently proved symbols unless explicitly named in the status inventory.
- **P — Preconditions:** finite bitstrings with a canonical parser/serializer, explicit input length, well-formedness/invalid-input policy, polynomial clock, and bounded witnesses. All reductions must handle rejected/ill-formed encodings in a specified manner.
- **G — Gates:** independent mathematical proof term, syntactic check in focused Agda root, actual pinned-toolchain check, axioms/postulates/hole audit, executable regression as secondary evidence, consumer parity, exact source commit attribution.
- **F — Follow-through:** after each edge, add the checked reduction to a *single* 21-node graph and propagate completeness using the existing `transportNPComplete` rather than creating 21 copied proofs.

## A. Honest current status (audited against #1445 GitHub tree)

| Proof owner / receipt | Verified object | State |
| --- | --- | --- |
| `DASHI/Mathematics/Complexity/PolynomialReductionExact.agda` | generic `composeReduction`, `pullbackPAlongReduction`, `npCompleteInPImpliesPEqualsNP` over a common `Word` and assumed cost-model laws | prior source owner; *not* 21 concrete instances |
| `.../CookLevinCircuitGCTBoundary.agda` | literal Boolean formula evaluator and a sample tautology; Cook–Levin `Simulation` is a record of **unfilled obligations** | partial |
| `.../PNotEqualsNPClayCoreExact.agda` | SAT-not-in-P ↔ P!=NP *assuming* standard completeness premises | conditional |
| `.../Karp21ReductionTransportExact.agda` | `npCompleteIsHard`, `transportNPHard`, `transportNPComplete` given costed reductions | source-written in #1445, kernel acceptance **not checked here** |
| `.../Karp21CliqueVertexCoverExact.agda` | `karpCliqueCoverSemanticEquivalence` over Boolean selected-vertex predicates; off-diagonal semantics | source-written; cardinality/bit cost unpaid |
| `.../Karp21CliqueSetPackingExact.agda` | `karpCliquePackingSemanticEquivalence` on symmetric adjacency and vertex-indexed nonedge-incidence subsets | source-written; finite instance/duplicate sets/bit cost unpaid |
| `.../Karp21WeightedCutObjectiveExact.agda` | `cutObjectiveFlip`, `flipThresholdCut`: global side reversal preserves edge-list objective | source-written; PARTITION→cut exact polynomial map unpaid |
| `.../Karp21Everything.agda` | focused import/check root for above | source-written; no pinned Agda receipt shown |
| `scripts/check_karp_partition_maxcut.py` | exhaustive positive-list PARTITION/cut identity and threshold finite regression | 19,530 cases passed in an independently executed local Python audit; not a proof |
| `dashi_lean4` PR #78 | pinned `openai/math` vendor + catalogue, `OAI.OptimalMaxCut.main` and `OAI.VertexCover.every_fixed_factor_below_two` routing | sources inspected; no Agda same-object port |
| `DASHI/Planning/NetworkFlowCapacityCongestionExact.agda` | qualitative toy joint-capacity no-promotion | not Ford–Fulkerson or maxflow/mincut |
| `DASHI/Computation/BellmanFordRelaxationScheduleFibreExact.agda` | shortest-path Bellman–Ford schedule fibre | **not** Ford–Fulkerson |

**Checked end-to-end Karp problem completions in this PR: 0/21. Checked direct concrete Karp reductions with polynomial time proof: 0/20.** Four named Agda implementation owners are source-written; their semantics do not discharge NP-hardness without the resource/certificate adapters. Do not overwrite these counts based on module names.

## B. Canonical shared obligations (finish once; all problem nodes consume)

| ID | Required exact lemma/declaration | Statement and done condition |
| --- | --- | --- |
| K00a | `parseEncodeRoundTrip` | parsed canonical finite instances recover same instance; `decode(encode(x)) = x`, malformed cases deterministic |
| K00b | `encodingLengthPolynomial` | bits of every encoded finite graph, set-family, schedule, integer matrix/weights are polynomial in explicitly measured source bit-length |
| K00c | `heterogeneousReductionToWord` | embed `A:InstanceA→Set`, `B:InstanceB→Set` into common `Word` without changing truth; no oracle or unproved cost assumption |
| K00d | `polynomialMapComposeConcrete` | prove actual clock polynomial composition/bit-comparison cost, instantiate `PR.PolynomialMapComposition` |
| K00e | `verifierPolynomialWitnessLength` | witness has finite encoded length polynomial in input size; verifier computes in bounded time, *including* arithmetic bit complexity |
| K00f | `reductionMalformedInputIff` | every source input, including bad encodings, reduces to a correctly classified target input |
| K00g | `costModelNonDegenerate` | polynomial predicates tied to concrete machine/size model; no vacuous model assigning all maps polynomial |
| K00h | `canonicalKarpNPCompleteTransport` | instantiate existing `transportNPComplete` with a concrete Karp edge and target NP certificate |
| K00i | `cookLevinSATRoot` | **actual** Cook–Levin tableau/circuit compiler, polynomial cost, iff acceptance/satisfiability on shared SAT language; not a record field assumed inhabited |
| K00j | `completeHistoricalReductionDAG` | exact 21 distinct typed nodes, exactly 20 source-labelled directed edges, proof of reachability from SAT and transport for all 21 |

For every node `Nxx`, use `<stem>Instance`, `<stem>Accepts`, `<stem>VerifierSound`, `<stem>VerifierComplete`, `<stem>CertificateBound`, `<stem>VerifierPolyTime`, `<stem>InNP`. The six latter declarations are **required** and currently unpaid for every new concrete Karp instance, except for any independently kernel-verified earlier owner established by source lookup. Semantic, clock and NP claims must be explicit; `InNP` must assemble them.

## C. Exact 21-node matrix (historical decision problems)

Each row's exact named `<stem>InNP` is the final NP-membership lemma; the uniform six supporting obligations above apply to that same `stem` (not implicit).

| Node | Karp 1972 problem / decision formulation | Exact terminal NP lemma | Current status |
| --- | --- | --- | --- |
| N01 | CNF SAT — satisfying Boolean assignment exists | `karpSATInNP` | BooleanFormula evaluator exists; canonical CNF/certificate/cost incomplete |
| N02 | 0–1 INTEGER PROGRAMMING — integer matrix equation feasibility with Boolean variables, **no optimisation** | `binaryIntegerProgrammingInNP` | open |
| N03 | CLIQUE — simple undirected graph has a clique of cardinality ≥ k | `karpCliqueInNP` | graph-selected predicate semantics only |
| N04 | SET PACKING — at least k pairwise disjoint indexed subsets | `karpSetPackingInNP` | clique/packing semantic duality only |
| N05 | NODE COVER / VERTEX COVER — cover all edges with ≤ k vertices | `karpVertexCoverInNP` | clique/complement-cover semantic duality only |
| N06 | SET COVERING — cover full universe using ≤ k indexed sets | `karpSetCoverInNP` | open |
| N07 | FEEDBACK NODE SET — delete ≤ k vertices to make directed graph acyclic | `karpFeedbackVertexSetInNP` | open |
| N08 | FEEDBACK ARC SET — delete ≤ k arcs to make directed graph acyclic | `karpFeedbackArcSetInNP` | open |
| N09 | DIRECTED HAMILTON CIRCUIT — single directed cycle visits every vertex once | `karpDirectedHamiltonianInNP` | open |
| N10 | UNDIRECTED HAMILTON CIRCUIT — single undirected cycle visits every vertex once | `karpUndirectedHamiltonianInNP` | open |
| N11 | SAT with at most 3 literals per clause — 3-CNF satisfiability | `karpThreeSATInNP` | OAI 378 CNF source donor; exact shared bridge open |
| N12 | CHROMATIC NUMBER — proper colouring with ≤ k colours | `karpColouringInNP` | open |
| N13 | CLIQUE COVER — partition vertices into ≤ k cliques | `karpCliqueCoverInNP` | open |
| N14 | EXACT COVER — pairwise disjoint indexed subsets cover universe exactly | `karpExactCoverInNP` | open |
| N15 | HITTING SET — choose ≤ k elements intersecting every family set | `karpHittingSetInNP` | open |
| N16 | STEINER TREE — connect required terminals with length/weight ≤ k | `karpSteinerTreeInNP` | open |
| N17 | 3-DIMENSIONAL MATCHING — disjoint triples cover designated three sets | `karpThreeDimensionalMatchingInNP` | open |
| N18 | KNAPSACK — Karp's *subset-sum-like* feasibility variant; not a generic utility optimisation | `karpKnapsackInNP` | open |
| N19 | JOB SEQUENCING — single machine, deadlines, durations, tardiness penalties and budget | `karpJobSequencingInNP` | open; NOT Job-shop scheduling |
| N20 | PARTITION — split positive integer multiset into equal sums | `karpPartitionInNP` | Python finite identity only |
| N21 | MAX CUT — weighted graph has cut with weight ≥ threshold, Karp's sign/weight domain preserved | `karpWeightedMaxCutInNP` | generic edge-objective/reversal only |

For Karp's exact historical variants, normalize against the 1972 original before fixing the machine encoding. For example, clique-cover convention (partition versus cover) and negative-edge/zero-weight domains require explicit variant bridges if the original and modern statements differ. Do not silently substitute an easier optimization variant.

## D. Exact 20 reduction-edge matrix (historical adjacency; all currently resource-open)

Every `reduce...` below is a concrete **polynomial-time total encoder**; every `...Iff` is source yes iff target yes **for every accepted encoding**; and every `...Cost` proves an actual polynomial time / bit-length bound. These three statements are all required for each row. `...Hardness` then invokes the existing generic transport.

| Edge | Reduction | Exact function | Iff lemma | Time/size lemma |
| --- | --- | --- | --- | --- |
| E01 | N01 SAT → N02 0–1 IP | `reduceSATToBinaryIP` | `satBinaryIPIff` | `satBinaryIPCost` |
| E02 | N01 SAT → N03 CLIQUE | `reduceSATToClique` | `satCliqueIff` | `satCliqueCost` |
| E03 | N01 SAT → N11 3-SAT | `reduceSATToThreeSAT` | `satThreeSATIff` | `satThreeSATCost` |
| E04 | N03 CLIQUE → N04 SET PACKING | `reduceCliqueToSetPacking` | `cliqueSetPackingIff` | `cliqueSetPackingCost` |
| E05 | N03 CLIQUE → N05 VERTEX COVER | `reduceCliqueToVertexCover` | `cliqueVertexCoverIff` | `cliqueVertexCoverCost` |
| E06 | N05 VERTEX COVER → N06 SET COVER | `reduceVertexCoverToSetCover` | `vertexCoverSetCoverIff` | `vertexCoverSetCoverCost` |
| E07 | N05 VERTEX COVER → N07 FEEDBACK NODE SET | `reduceVertexCoverToFeedbackVertex` | `vertexCoverFeedbackVertexIff` | `vertexCoverFeedbackVertexCost` |
| E08 | N05 VERTEX COVER → N08 FEEDBACK ARC SET | `reduceVertexCoverToFeedbackArc` | `vertexCoverFeedbackArcIff` | `vertexCoverFeedbackArcCost` |
| E09 | N05 VERTEX COVER → N09 DIRECTED HAMILTON CIRCUIT | `reduceVertexCoverToDirectedHamiltonian` | `vertexCoverDirectedHamiltonianIff` | `vertexCoverDirectedHamiltonianCost` |
| E10 | N09 DIRECTED → N10 UNDIRECTED HAMILTON CIRCUIT | `reduceDirectedToUndirectedHamiltonian` | `directedUndirectedHamiltonianIff` | `directedUndirectedHamiltonianCost` |
| E11 | N11 3-SAT → N12 CHROMATIC NUMBER | `reduceThreeSATToColouring` | `threeSATColouringIff` | `threeSATColouringCost` |
| E12 | N12 CHROMATIC NUMBER → N13 CLIQUE COVER | `reduceColouringToCliqueCover` | `colouringCliqueCoverIff` | `colouringCliqueCoverCost` |
| E13 | N12 CHROMATIC NUMBER → N14 EXACT COVER | `reduceColouringToExactCover` | `colouringExactCoverIff` | `colouringExactCoverCost` |
| E14 | N14 EXACT COVER → N15 HITTING SET | `reduceExactCoverToHittingSet` | `exactCoverHittingSetIff` | `exactCoverHittingSetCost` |
| E15 | N14 EXACT COVER → N16 STEINER TREE | `reduceExactCoverToSteinerTree` | `exactCoverSteinerTreeIff` | `exactCoverSteinerTreeCost` |
| E16 | N14 EXACT COVER → N17 3D MATCHING | `reduceExactCoverToThreeDimensionalMatching` | `exactCoverThreeDimensionalMatchingIff` | `exactCoverThreeDimensionalMatchingCost` |
| E17 | N14 EXACT COVER → N18 KNAPSACK | `reduceExactCoverToKarpKnapsack` | `exactCoverKnapsackIff` | `exactCoverKnapsackCost` |
| E18 | N18 KNAPSACK → N19 JOB SEQUENCING | `reduceKarpKnapsackToJobSequencing` | `knapsackJobSequencingIff` | `knapsackJobSequencingCost` |
| E19 | N18 KNAPSACK → N20 PARTITION | `reduceKarpKnapsackToPartition` | `knapsackPartitionIff` | `knapsackPartitionCost` |
| E20 | N20 PARTITION → N21 WEIGHTED MAX CUT | `reducePartitionToMaxCut` | `partitionMaxCutIff` | `partitionMaxCutCost` |

**Every E01–E20 must also export** `<edge>PolynomialReduction : PR.PolynomialManyOneReduction cost source target` and `<edge>NPComplete`, *using* `Karp21ReductionTransportExact.transportNPComplete`, after proving the target's NP lemma. Avoid materializing multiple alternate proof owners.

### Concrete proof obligations on the currently closest edges

- **E04/Set Packing:** finite universe of nonedge pairs, vertex-indexed sets and optional unique private tokens; `nonedgeIncidenceCorrect`, `packingPairwiseDisjointIffClique`, `packingIndexInjective`, `packingPreservesAtLeastK`, `packingSetListSizeQuadratic`, `packingBitEncodingPoly`. If duplicate empty sets collapse in a set-of-sets carrier, the reduction is invalid without an indexed-family or uniqueness repair.
- **E05/Vertex Cover:** `simpleComplementOffDiagonal`, `complementSymmetric`, `cliqueCoverFiniteCardinalityComplement` (|V\\S|=n-|S|), `cliqueVertexCoverThresholdIff` (k↔n−k, explicit k>n cases), `complementGraphBitsQuadratic`, `cliqueVertexCoverPoly`. Existing `karpCliqueCoverSemanticEquivalence` handles the pointwise predicate, not these bounds.
- **E20/Max Cut:** `partitionCompleteGraphWeights`, `partitionCutProductIdentity` (cut(S)=A(T−A)), `partitionCutSquareIdentity` (4cut=T²−(T−2A)²), `partitionCeilThresholdIffEquality` (cut≥⌈T²/4⌉ ↔ 2A=T), `partitionCutWeightedGraphEncodingPoly`, `partitionMaxCutReductionPoly`. Positive integer input, binary input size, empty/zero corner cases and loop/duplicate handling explicitly fixed. The 19,530-case Python regression is **not** these lemmas.
- **E01/Binary IP:** `binaryClauseInequalityIff`, `slackVariableBound`, `inequalityToEqualitiesIff`, `satToBinaryIPWitnessEquivalence`, `binaryCoefficientBitCost`.
- **E03/SAT→3SAT:** `tseitinExtensionIff` (existential rather than unique unless actually proved), `threeSATWidthBound`, `threeSATClausesLinear`, `threeSATCompilerCost`, `threeSATSharedOpenAISemantics` (cross-repo exact literal identity only once proved).

## E. Eight follow-on topics / exact external boundaries

These are *not* extra nodes in Karp's 21. Keep as lanes consuming common graph/NP interfaces.

| Lane | Exact target declarations | In-repo donors and non-conflation |
| --- | --- | --- |
| X01 Integer programming optimisation | `binaryIPFeasibleIffKarp`, `ipObjectiveDoesNotChangeFeasibility`, `lpRelaxationDirection`, `totalUnimodularityIntegralityUnderHypotheses` | Karp's N02 is **feasibility**. LP, integer optimisation, and TUM each require additional hypotheses |
| X02 Set packing optimisation | `maximumPackingObjective`, `packingCliqueThresholdIff`, `packingApproximationRatioBridge` | E04 supplies decision hardness, *not* approximation hardness |
| X03 Vertex cover optimisation | `minimumVertexCoverObjective`, `minimumCoverComplementMaximumClique`, `vertexCoverGapSameObjectWithOAI` | upstream `openai/math/lean/OAI/Computability/VertexCover/Main.lean` theorem `OAI.VertexCover.every_fixed_factor_below_two`: separate α<2 approximation-gap donor |
| X04 Job-shop scheduling | `jobShopInstance`, `jobShopScheduleSoundComplete`, `jobSequencingEmbeddingHypotheses`, `jobShopFeasibilityCost` | Karp N19 is single-machine job sequencing; never rename it Job-shop |
| X05 MAX CUT/APX | `maxCutDecisionOptimizationBridge`, `maxCutNonnegativeFiniteApproxObjective`, `maxCutGapSameObjectWithOAI`, `maxCutGoemansWilliamsonRatioCertificate` | upstream `OAI.OptimalMaxCut.main` is gap/hardness for unweighted finite simple graphs, not E20; OAI #1438 27-grid example is finite |
| X06 Minimum k-cut | `kCutPartitionSound`, `kCutObjective`, `minSTCutIsTerminalConstrainedTwoCut`, `fixedKPolynomialWithCost`, `variableKDecisionHardness` | separate MINIMUM objective; nonnegative capacities; k=2 *global* cut is not an s-t mincut without specified terminals |
| X07 APX | `NPOObjectiveEncoding`, `approxFactorValid`, `apReductionPreservesApproxGuarantee`, `lReductionPreservesGap`, `apxMaxCutMembership`, `apxVertexCoverMembership` | zero-optimum, negative-weight, minimization/maximization, fixed-factor and PTAS domains explicit. Normal many-one reductions do not imply approximation preservation |
| X08 Ford–Fulkerson | `residualCapacityNonnegative`, `augmentPathPreservesFlowFeasibility`, `augmentRaisesFlowValue`, `noAugmentingPathProducesCut`, `flowValueLeqCutCapacity`, `maxFlowMinCutEquality`, `edmondsKarpBFSRuntimePolynomial` | no same-object algorithm found on indexed `dashi_agda` master; `NetworkFlowCapacityCongestionExact` is toy; Bellman–Ford shortest paths is unrelated |

**Historical/algorithmic caveats:** Karp's `MAX CUT` accepts signed weights in its original formulation; standard approximation theory generally assumes nonnegative edges and nonnegative optimum. Minimum k-cut is polynomial for fixed k and NP-hard when variable; an `O(n^{f(k)})` guarantee is not FPT. Ford–Fulkerson with integer capacities yields a bounded number of unit augmentations but may be pseudo-polynomial in binary capacity; Edmonds–Karp's BFS selection supports `O(V E²)`.

## F. Priority cut / dependency order (Pareto and snowball)

**Tier 0 — proof-system blockers (must precede any "21 done" claim):**
- K00a–K00j, especially concrete word encoding, actual cost model, Cook–Levin and malformed-input handling. Existing `PR.InNP` and `PR.NPComplete` records are typed *interfaces*, not globally supplied proofs.

**Tier 1 — shortest reusable graph triangle:**
- E03 and E02 SAT/CNF bridges → E04 CLIQUE/SET PACKING → E05 CLIQUE/NODE COVER → E06 SET COVER.
- Aim first for the concrete *E05* theorem using #1445's `karpCliqueCoverSemanticEquivalence`, then E04 using `karpCliquePackingSemanticEquivalence`. Build finite cardinality once and reuse it throughout vertex- and set-indexed constructions.

**Tier 2 — arithmetic terminal:**
- E17 EXACT COVER→KNAPSACK → E19 KNAPSACK→PARTITION → E20 PARTITION→MAX CUT.
- In parallel, E01 integer constraints and X01 arithmetic optimization (without conflating feasibility).
- Reuse bit-cost exact arithmetic from existing number-theory modules, not literal numerology analogies.

**Tier 3 — complete historically remaining branches:**
- E07–E10 feedback and Hamiltonian; E11–E16 colouring/clique cover/exact cover/hitting set/Steiner/3DM; E18 sequencing.

**Tier 4 — independent approximation/flow graph:**
- X03, X05, X07 consume the actual OAI Lean declarations after pinned toolchain and same-object audit; X06/X08 consume a separate finite flow network with residual arcs and conservation.
- Report Karp decision completeness separately from APX/flow and from the Clay P != NP frontier.

## G. Mechanical acceptance checklist (per lemma, per edge, per 21-node closure)

1. Source owner path and earliest actual implementation SHA/time, original author DOI/date; later source ports keep *both* provenances.
2. Well-formed and ill-formed inputs; exact instance and certificate encoding, duplicate-index, parity, empty, weight signs, loop convention; prove parser roundtrip.
3. Explicit `forward` and `backward` proof terms, no `postulate`, `sorry`, unconstrained boolean status, or `Set` field used as a disguised theorem.
4. Actual polynomial **machine** steps plus output-bit budget. Do not infer a cost theorem merely from a total Agda function.
5. Finite exhaustive regression on small instances, including at least one YES/NO per edge and malformed controls, is *secondary* evidence.
6. `scripts/run_agda29_parallel_check.sh DASHI/Mathematics/Complexity/Karp21Everything.agda` for draft; repository-pinned Track A Agda for final acceptance. Do not claim either passed unless an actual run/receipt is attached.
7. Same-object Agda ↔ Lean bridge (if used), pinned original source, kernel/axiom report, regression and TOE consumer after successful independent verification.
8. Update this roadmap with exact lemma names and close only a lemma whose file/line and kernel receipt can be inspected.

## H. Source bibliography / exact URLs

- Cook (1971): https://doi.org/10.1145/800157.805047
- Karp (1972): https://doi.org/10.1007/978-1-4684-2001-2_9
- Karp original/tree overview: https://en.wikipedia.org/wiki/Karp%27s_21_NP-complete_problems
- Zuckerman constrained approximation distinction: https://doi.org/10.1137/S0097539794266407
- OpenAI original Max-Cut Lean: https://github.com/openai/math/blob/main/lean/OAI/Computability/MaxCut/Main.lean
- OpenAI original Vertex Cover Lean: https://github.com/openai/math/blob/main/lean/OAI/Computability/VertexCover/Main.lean
- In-repo Lean OpenAI atlas PR #78: https://github.com/chboishabba/dashi_lean4/pull/78
- In-repo finite same-object Max-Cut graph: in `dashi_agda` PR #1438 (not a general NP-completeness proof).
- Ford–Fulkerson background: https://en.wikipedia.org/wiki/Ford%E2%80%93Fulkerson_algorithm
- Minimum k-cut distinction: https://en.wikipedia.org/wiki/Minimum_k-cut
