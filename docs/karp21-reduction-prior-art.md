# Karp's 21 NP-complete problems: proof-ownership and reduction plan

**Canonical full current roadmap:** [`Docs/roadmaps/Karp21NPCompletenessExactLemmaRoadmap20261101.md`](../Docs/roadmaps/Karp21NPCompletenessExactLemmaRoadmap20261101.md). This shorter research note is not the authoritative status ledger; use the linked file for exactly 21 nodes, 20 historical edges, eight follow-on subjects, and named remaining lemmas.

## 2026-11-01 full finite-network completion (NOT proof completion)

All 20 historical source-labelled edges now have a bounded executable candidate and independently checked finite truth-equivalence controls, via:
- `scripts/check_karp_historical_reductions.py` (15 edges);
- `scripts/check_karp_remaining_four_gadgets.py` (E09, E11, E13, E16);
- `scripts/check_karp_partition_maxcut.py` (E20 signed/zero-total arithmetic).
- `scripts/run_karp21_reduction_regressions.py` runs all three fail-closed.

Independent local finite audit: **55,824 edge-instance checks** (the sum of per-edge test rows, including 23,436 E20 positive/signed instances). The committed GitHub scripts are source-written and have **not** been executed from an exact branch checkout in this session.

Agda DAG owner `Karp21HistoricalDagExact.agda` defines all 21 problem constructors, 20 edge constructors, and the source-written `allNodesHistoricallyReachable`. The new `Karp21CertifiedDagTransportExact.agda` is a structural completeness *proof compiler*: `allTwentyOneNPCompleteIfCertified` would derive all 21 results from **actual** `PR.PolynomialManyOneReduction` certificates and membership witnesses. No caller currently supplies those general certificates; no Agda pinned-toolchain receipt has been run. The formal end-to-end completion count remains **0/21**.

**Attribution precision:** Karp explicitly credits Cook (1971) for SAT→3-SAT, a Cook (1970) implicit construction and Raymond Reiter for SAT→CLIQUE, Cornell's Algorithms Seminar for NODE COVER→FEEDBACK NODE SET, Eugene Lawler and Karp jointly for NODE COVER→FEEDBACK ARC SET, Lawler for EXACT COVER→3-DIMENSIONAL MATCHING, and Robert Tarjan for DIRECTED→UNDIRECTED HAMILTONIAN CIRCUIT. Keep the original discoverers separate from Karp's 1972 network and DASHI's 2026 executable/formal reconstructions.

The original 1972 HITTING SET is **exactly one** selection from every transposed set, not ordinary modern at-least-one hitting. Signed KNAPSACK→PARTITION requires DASHI's extra digit-guarded positive normalization before applying the nonnegative historical two-extra-number gadget. These are semantic requirements, not cosmetic renamings.


### Signed E20 and Cook E03 exact Agda lemma tranches (2026-11-01)

- `Karp21PartitionCutQuadraticExact.agda` reuses the repo's prior integer `RingZ` algebra, defines the actual triangular complete-graph crossing-edge sum (not an assumed scalar objective), proves `signedTotalDecomposes`, `completeGraphCutEqualsPartitionProduct`, `completeGraphCutQuadratic`, and `balancedSelectionIffExactMaximum`: the exact signed identity `4*cut = total²` holds iff the two sides sum equally. This is substantive source-written proof code, **not a pinned Agda kernel receipt**, and the original Karp *decision* threshold `ceil(total²/4)` still needs a discrete inequality/rounding proof and machine cost.
- Karp 1972 p.100's printed typography can be read literally as `ceil(sum(cᵢ²)/4)`; this is **not equivalent** to the source PARTITION predicate. The explicit counterexample `(2,1)` has NO equal partition, but a cut of weight 2 meets literal threshold 2. The corrected mathematical construction uses `ceil((sum cᵢ)²/4)=3`, which rejects the same instance. An independent local Python check verified the counterexample. Keep the *printed source claim*, *corrected DASHI mathematical reconstruction*, and *later secondary explanation* separately attributed. See `scripts/check_karp_partition_maxcut.py`.
- `Karp21SATToThreeSATGadgetExact.agda` credits **Cook 1971** as the original 3-literal reduction owner; it proves the constructive local four-to-three clause splitting equivalence, with `x = c∨d` as the forward fresh-bit witness. The standalone independent Python truth-table audit passed all 16 Boolean source assignments, and checked both choices of the new bit. The full recursive clause compiler and binary machine clock remain open.
- E09's source-written directed Hamiltonian gadget now maps zero/negative node-cover budgets to fixed NO instances when required, rather than raising/asserting or incorrectly accepting an empty graph with a negative budget.

No source paper, number of sampled instances, or loop-free Agda source automatically establishes an Agda kernel-accepted NP-completeness theorem.


### 2026-11-01 semantic max-cut continuation: scaled E20 + E05 + machine-reduction assembly

**New DASHI Agda source owners:**
- `Karp21ScaledThresholdExact.agda`: `scaledThresholdIffBalanced` proves the *ordered* signed integer cut-threshold witness iff by reusing the earlier integer no-zero-divisors and nonnegative-square results; `nonzeroTotalSquareIsPositiveThreshold` certifies `T²` is positive whenever `T≠0`.
- `Karp21PartitionScaledInstanceExact.agda`: each signed input element carries a separate Boolean label (multiplicity preserved); `signedPartitionScaledCutInstanceIff` gives *existential* source/target equivalence, `zeroTotalPartitionYES` supplies the empty-side witness, and `totalPartitionToPositiveCut` / `totalPartitionPositiveCutIff` handle the full zero/nonzero split with proof-bearing positive target thresholds. The target is currently algebraically represented as a signed complete graph, not yet an explicitly serialized bitstring.
- `Karp21HeterogeneousEncodingExact.agda`: `compileHeterogeneousKarpReduction` is a generic proof-term assembler from a heterogeneous semantic iff, faithful source/target byte contracts and an actual word-polynomial-time witness to the existing `PR.PolynomialManyOneReduction`. No polynomial clock is fabricated by this proof.
- `Karp21FiniteCliqueCoverCardinalityExact.agda`: `karpCliqueCoverFiniteThresholdIff` proves for every finite Boolean vertex selection and natural `k`, including `k>n`, the exact equivalence between `k≤chosenCount` and `complementCount+k≤n`; 26,622 independent local finite Boolean/threshold controls pass.
- `Karp21PartitionCutQuadraticExact.agda` now also source-writes `historicalPartitionEquationIffBalanced`, explicitly identifying the original signed source equation `2A=T` with the equal-side predicate.

**Scaled E20 construction and source priority:** Karp (1972) owns the PARTITION→MAX CUT reduction. DASHI's equivalent integer-scaled variant chooses edge weights `4*c_i*c_j` and target weight threshold `T²`, with a special fixed positive-threshold YES graph for `T=0`. It is correct at the witness arithmetic level and **does not require the historical ceiling step**. The earlier ceiling-route proof obligation remains only for literal unscaled reconstruction; for the scaled route the remaining gap is an explicit faithful labelled graph edge-list/word codec, actual general polynomial machine time, MAX CUT NP verifier, and Agda kernel acceptance.

**Independent source-computation result:** 23,436 positive/signed instances independently checked for the scaled formula and the original signed source witnesses; no counterexamples found. This is a finite arithmetic regression, not kernel evidence. The PR does not add a new unconditional NP-completeness theorem.

### 2026-11-01 signed spectral/MAX CUT provenance cross-pollination

**Original reduction mathematics:** Richard M. Karp (1972) defines MAX CUT with signed integer weights and a positive decision threshold; his proof of PARTITION→MAX CUT is distinct from graph optimization/approximation, nonnegative graph spectral inequalities, and AO work-frontier scheduling. The classical `s_i∈{−1,+1}` Laplacian quadratic identity `4CUT(s)=Σ_(ij)w_ij(s_i−s_j)²` is reused, not claimed as a new original physical theorem.

**Earlier DASHI mathematical donors and restrictions:** [Agda #1438](https://github.com/chboishabba/dashi_agda/pull/1438) `GraphColouring369PantsWeightedMaxCutExact` proves a maximal checkerboard cut of **54 enumerated native ternary-grid edges with Nat nonnegative weights**, not the arbitrary signed Karp problem; its `TrialecticGraphWaveConsumerLossCutExact` also exhibits C3-averaging information loss. [Agda #1415](https://github.com/chboishabba/dashi_agda/pull/1415) world/macro-eigen/sub-eigen/fibre separation and [#1416](https://github.com/chboishabba/dashi_agda/pull/1416) hierarchical spectral Pareto boundaries are prior shared queueing/source-contract owners. [Lean #102](https://github.com/chboishabba/dashi_lean4/pull/102) is the downstream mirror and explicitly withholds physics and Goemans–Williamson ratio proof claims. [Lean #78](https://github.com/chboishabba/dashi_lean4/pull/78) vendors distinct `OAI.OptimalMaxCut.main` / VertexCover proof sources; no Agda same-object transport claimed.

**New source-written DASHI result:** `Karp21SignedLaplacianCutExact.agda` imports the **existing N21 exact weighted-edge certificate evaluator**, not an independently written pseudo-graph, and constructs `fourCutEqualsSpinQuadratic`, `karpCutEqualsSignedLaplacianQuadratic` for **all signed input weights**, Z₂ global vertex-label flip symmetry (`signedMaxCutGlobalFlipInvariant` / `signedLaplacianGlobalFlipInvariant`) and the negative one-edge spectral counterexample `negativeEdgeSignedQuadratic`, which equals −4. These are source-written mathematical proof terms; independent Agda kernel acceptance remains outstanding. The supplemental `check_karp_signed_laplacian.py` enumerates bounded signed graphs and checks all finite labels, and is incorporated into `run_karp21_reduction_regressions.py`.

**Cross-repository observations are never imported as mathematical premises:** ITIR-suite [#20](https://github.com/chboishabba/ITIR-suite/pull/20), [#63](https://github.com/chboishabba/ITIR-suite/pull/63), [#70](https://github.com/chboishabba/ITIR-suite/pull/70); SLR [#75](https://github.com/chboishabba/slr/pull/75), [#76](https://github.com/chboishabba/slr/pull/76); SensibLaw [#508](https://github.com/chboishabba/SensibLaw/pull/508), [#509](https://github.com/chboishabba/SensibLaw/pull/509), [#510](https://github.com/chboishabba/SensibLaw/pull/510). These contain candidate scheduling, source/digest fidelity, non-promotion and nested progress controls. No code edits were made to ITIR-suite, SLR, SensibLaw or the Lean mirror in this tranche, and no candidate AO score, graph eigenvalue or formal routing receipt was promoted into a Karp polynomial-reduction theorem.

**Still unpaid:** source signed list → full labelled finite indexed complete-graph E20 edge-list bridge, actual N21 graph/assignment canonical binary codec, real polynomial machine verifier and certificate bound, all remaining E01–E19 costed reduction theorems, N01–N20 membership lemmas, K00 uniform Cook–Levin root, pinned kernel receipts. The DAG's 20 labels are not 20 certified polynomial reductions.

### 2026-11-01 PNF actual signed Δ₀, corrected-PSD clustering and SSP/Cheeger ternary BIDI

**Inherited PNF theorem owners now directly reopened:** `DASHI/Interop/PNFSpectralFieldGraph.agda`, `PNFHodgeResidualTopology.agda`, `PNFSignedResidualDelta0Exact.agda`, `PNFTernaryCycleSpectralExact.agda`. The *original* PNF signed triangle is **0→1 partial(+1), 1→2 noTypedMeet(+3), 2→0 contradiction(-9)**, with source-owned exact `BᵀWB` and signed indefiniteness. The 0/1/2-cell source and evidence class remain authoritative; no generic Karp target can imply PNF truth/authority or forget directed/source provenance. **New source-written** `Karp21PNFSignedTriangleSameObjectExact.pnfLiteralSignedDelta0CutIdentity` reconstructs those precise weights via PNF constructors and proves `4cut(b)=s(b)ᵀΔ₀s(b)` on the literal finite triangle. Kernel check pending.

**Two different signed graph formalisms:** Karp's 1972 MAX CUT maximizes signed edge crossings `Σw[cross]` and *penalizes* crossing negative edges. The signed clustering / frustration objective for repulsive negative edges **minimizes** `Σ_{w>0}w[cross]+Σ_{w<0}|w|[same]`. Its absolute-degree corrected PSD Laplacian is `D_|W|−W` with `Σ|w|(s_i−sign(w)s_j)²`. The added `Karp21SignedFrustrationBidiExact` algebraically derives `frustration(E,b)=signedCut(E,b)+Σ|negative weights|` and `signedPSDenergy=4*frustration` on the **same signed finite graph**, so maximizing signed Karp cut maximizes (not minimizes) that frustration. This is not a contradictory "two Laplacians are equal" claim. Source roots: Cartwright–Harary (1956); Kunegis et al. (2010) DOI 10.1137/1.9781611972801.49; Atay–Liu (2020) DOI 10.1016/j.disc.2019.111616. Finite signed `BᵀWB` is indefinite; changing to `D_|W|−W` is a change of operator and objective, not a counterexample to the original 4cut identity.

**Canonical ternary used, no new trit type:** `Karp21SSPTernaryMaskedCutExact` imports `DASHI.Foundations.SSPTritCarrier`, proves exact `Q_ternary=Q_induced+Q_bleed` on arbitrary signed edge lists and the original binary ±1 specialization. A neutral endpoint gives `w` for each active-neutral edge, **not** silent deletion. Separately `Karp21SSPDualCheegerSignlessOneExact` gives `|x_i+x_j|` values 0/1/2 on SSP trits with nonnegative natural weights and list additivity. It does not claim the full dual Cheeger constant, nonlinear eigenvalue theory, normalized Cheeger inequalities or worst-case approximation ratio. Primary signed-graph Cheeger: Atay–Liu 2020. Signless 1-Laplacian / dual Cheeger: Bauer–Hua–Jost 2012 arXiv:1207.3410; Shao–Yang–Zhang (2016 preprint, 2025) DOI 10.1007/s11425-024-2376-2. Yang–Mills Lawler–Sokal reversible/Markov Cheeger already in DASHI is a distinct same-object constraint, not this discrete graph theorem.

**E20 actual complete graph (now source-written):** `Karp21FiniteCompleteGraphGeneratorExact` emits canonical-looking upper-triangle `Fin n` edges without seeing labels, proving `n(n−1)/2` output count; `Karp21FiniteCompleteGraphObjectiveExact.e20CompleteGraphToWeightedCutEdgeListIff` and `e20ScaledIndexedGraphExactCut` establish the universal same-object signed score identity; `Karp21SignedPartitionIndexedGraphDecisionExact.karpPartitionActualIndexedGraphYESIff` transports the original dependent List/Selection into that finite graph. `Karp21SignedPartitionActualGraphYESExact.sourcePartitionActualPositiveGraphIff` now builds a literal positive-threshold `Cut.WeightedCutGraph` and YES certificate in the zero-total exceptional branch and reuses square-positive proof for nonzero. **No Word binary codec, actual polynomial machine clock, NP membership or pinned Agda receipt** is claimed by these proof terms.

**Independent finite numerical controls:** 8 exact binary spins on the original PNF triangle; 63 SSP signed-edge/gap/mask controls; 251,023 signed finite graph/label frustration/PSD controls (n=0..4); 111,111 signed-partition/indexed-complete-graph all-label cases (n=0..5). Exact committed script `scripts/check_karp_pnf_signed_ternary.py` was added to the existing Karp runner; finite Python testing does not discharge any mathematical quantifier or kernel check. Source-written code and reviewed external papers must never be promoted into original-proof attribution.

### 2026-11-02 K00/E04/E06/E20/N21 typed and executable-word continuation

**Original theorem ownership remains** Cook (1971), Karp (1972). The source-written finite E04 Clique→nonedge-incidence Set Packing proof is in `Karp21FiniteCliquePackingDecisionExact`, reusing `Karp21CliqueSetPackingExact`, `Karp21SimpleGraphComplementExact`, and `Karp21FiniteCliqueVertexCoverCombinedExact`. E06 Node Cover→edge-incidence Set Cover is in `Karp21FiniteNodeSetCoverDecisionExact`, reusing `Karp21VertexSetCoverIncidenceExact`. Neither new module reconstructs the original historical reduction independently; both upgrade earlier generic witness proof terms to finite existential same-object decisions with the same Boolean choice and cardinality budget. Target bitsets, parser policy, resource clocks and kernel acceptance remain separate.

**E20 upper-pair provenance:** `Karp21IndexedUpperPairBijectionExact` defines typed upper-triangular positions on `Fin n`, proves their endpoint distinctness and endpoint injectivity, and proves membership-backed coverage of every off-diagonal pair. This uses `Karp21FiniteCompleteGraphGeneratorExact`, whose missing Nat-addition import was repaired. It must still be connected to the exact Gen edge-list weights and list no-duplicate occurrence invariant, with compiler receipt pending.

**N21 bitword certificate:** `Karp21MaxCutCertificateBinaryCodecExact` reuses the exact N21 `WeightedCutGraph` verifier and the repository's established `List Bool` binary codec practice from `PNotEqualsNPCookFormulaBinaryCodecExact`. The new source gives an exact-length total n-bit decoder, roundtrip, malformed-extra-bit rejection, soundness, completeness, and existential bit-certificate iff for each concrete finite graph. It does **not** supply the complete signed graph decoder or certified polynomial verifier.

**Shared K00 malformed-word totality:** `Karp21MalformedWordTotalReductionExact.TotalMalformedSource` proves that a real fixed-NO target plus target word-faithfulness and valid-source instance semantics yield a TOTAL Word reduction correct on invalid as well as valid source inputs. It only creates a costed `PR.PolynomialManyOneReduction` once supplied a real polynomial-time machine-map certificate; a paper or script claiming "executable" alone cannot fill that premise.

**Executable reference transducer (not Agda kernel):** `scripts/karp21_signed_cut_binary_codec.py` defines a self-delimiting `gamma(n+1)` + zigzag signed-integer binary source/target codec, a fixed-NO target on malformed source words, a fixed-YES unit-edge graph on zero-total valid sources, strict canonical sorted/unrepeated undirected target edges, positive integer W, and an n-bit cut-label verifier rejecting malformed words. This is a new DASHI Python reference implementation of a mathematically equivalent Karp 1972 E20 route; it is not source-written 1972 code, a formally proved compiler, or an independently checked Agda theorem. `scripts/check_karp_binary_codec.py` adds 3906 finite signed-source vectors, 111111 label combinations, 54 large signed 1024-bit envelope controls, graph invalid-input cases and integer prefix-code controls. The **new exact committed scripts were not run in this turn**; their case counts are specified test-space sizes, not executed receipts. A full `PR.polynomialTimeMap` proof and real N21 `PR.InNP` remain outstanding.

**Contributor attribution distinction:** Signed PNF original triangle (partial/noTypedMeet/contradiction severities) and the existing Δ₀ signed incidence identity continue to belong to their original DASHI owner. The E20 signed decision formulation is Karp 1972. Finite witness equivalences, canonical upper-pair addresses, new bitword certificate formalisation and Python codec are separately sourced new PR #1445 constructions. Source-written != compiler accepted != finite executable regression != Turing-time polynomial theorem != general NP-completeness.

## Historical provenance
- Stephen Cook (1971), *The Complexity of Theorem-Proving Procedures*, DOI 10.1145/800157.805047: original SAT complexity root.
- Richard Karp (1972), *Reducibility Among Combinatorial Problems*, DOI 10.1007/978-1-4684-2001-2_9: the original 21-problem reduction network.
- DASHI's own generic proof owner is `DASHI/Mathematics/Complexity/PolynomialReductionExact.agda`. The derived transport owner is `Karp21ReductionTransportExact.agda`.

## What is actually proved in this tranche
Given a shared encoded word carrier, polynomial-time-map composition, an NP-hard or NP-complete source and a **supplied** reduction to a target, transport NP-hardness; with target membership in NP, transport NP-completeness. This is proof composition, not a construction of any particular Karp reduction. No claim of local kernel acceptance or executed CI is made until compiled.

## Historical reduction graph (arrows mean polynomial many-one reducibility)
- SAT -> 0-1 integer programming; clique; SAT with at most 3 literals per clause.
- Clique -> set packing; vertex cover.
- Vertex cover -> set covering; feedback vertex set; feedback arc set; directed Hamiltonian cycle.
- Directed Hamiltonian cycle -> undirected Hamiltonian cycle.
- 3-SAT -> chromatic number.
- Chromatic number -> clique cover; exact cover.
- Exact cover -> hitting set; Steiner tree; 3-dimensional matching; knapsack (Karp's subset-sum-like variant).
- Knapsack -> sequencing; partition.
- Partition -> max cut.

The graph is the historical source diagram. Validate individual transformations against Karp's original definitions before turning each edge into a theorem. Do not infer the proof of any edge merely from the presence of these names.

## Required concrete interfaces
1. Heterogeneous polynomial reductions: source and target encoded instance types can differ. Encode both into a common bitstring or prove an explicit polynomial encoding/decoding bridge. No silent assumption that polynomial execution follows from definability.
2. For every node: precise decision predicate; bounded certificate, certificate verifier, size bound, and polynomial verification proof.
3. For every edge: executable transformation, forward/backward membership equivalence, explicit cost bound with bit-length accounting, and local witnesses.
4. Compose verified edges with `transportNPComplete`; record the precise upstream edge attribution and DASHI proof module ownership separately.
5. SAT root: connect the concrete SAT certificate representation to the existing `CookLevinCircuitGCTBoundary` literal BooleanFormula carrier; an abstract `satNPComplete` *field* in `PNotEqualsNPClayCoreExact` is an assumption, not the Cook-Levin proof.

## Highest-reuse edges / roadmap
- **K00**: heterogeneous encoded reductions and cost-model bridge (or explicit common-word encoding).
- **K01**: CNF SAT and 3-SAT certificates and truth-preserving clause gadgets.
- **K02**: SAT -> CLIQUE and CLIQUE -> VERTEX COVER (finite graph complement, compatible literals; 3-SAT->CLIQUE is an optional alternative route, not the displayed historical edge).
- **K03**: CLIQUE -> SET PACKING; VERTEX COVER -> SET COVER (finite set incidence).
- **K04**: 3-SAT -> CHROMATIC NUMBER and the EXACT COVER/3-DIMENSIONAL MATCHING cluster.
- **K05**: EXACT COVER -> Karp KNAPSACK -> PARTITION -> weighted threshold MAX CUT (explicit arithmetic base/carry, signed weights and thresholds).
- **K06**: remaining feedback-set, Hamiltonian, Steiner tree, hitting set, and sequencing edges.
- **K07**: all 21 NP-membership proofs and end-to-end reduction-chain composition, runtime/encoding audit, independent verification.

## 2026-11-01 extended tranche: eight user-selected subjects, with exact semantic ownership

| Subject | Original Karp variant / separate definition | In-repo or upstream prior art | Unpaid edge |
| --- | --- | --- | --- |
| Integer programming | #2 is **0–1 feasibility of integer equations** Cx=d, not arbitrary optimisation or real LP. SAT clause inequalities require a proof-preserving 0–1 equality/slack encoding and polynomial bit bound. | `PolynomialReductionExact`; Cook source evaluator; Lean OAI SAT-378 staged compiler is distinct | SAT -> binary IP (full equations and slack) |
| Set packing | #4: choose at least k pairwise disjoint sets; Karp's CLIQUE reduction uses vertex-indexed sets of **nonedges**. | `Karp21CliqueSetPackingExact` proves abstract indexed nonedge-incidence semantic equivalence; no finite encoded set lists yet | CLIQUE -> SET PACKING incidence and cardinality |
| Vertex cover | #5 NODE COVER: choose at most ℓ vertices meeting all edges. Original CLIQUE -> cover on complement graph with ℓ = n-k. | `Karp21CliqueVertexCoverExact` proves carrier-polymorphic constructive semantic equivalence for fixed vertex predicates; OAI source `OAI/Computability/VertexCover/Main.lean` derives separate approximation gap | Finite count lemma: |complement S|=n-|S|, bit-graph implementation, polynomial time |
| Job-shop scheduling | **Not Karp's #19**. Karp's #19 is single-machine JOB SEQUENCING with processing times T, deadlines D, penalties P and total late penalty ≤ k. Job-shop additionally imposes multi-machine precedence/resource constraints. | OAI `ThreeMachine` is another different scheduling object | KNAPSACK -> Karp JOB SEQUENCING; independently typed job-shop instance bridge |
| Maximum cut | #21 weighted threshold cut with integer edge weights and W>0, from PARTITION; not a generic DAG planning max-cut. | New `Karp21WeightedCutObjectiveExact` proves global-side-flip invariance of a weighted edge-list objective and threshold-witness transport. OAI `OptimalMaxCut.main` proves source-written strong **unweighted simple graph approximation-gap hardness**, separate from Karp's weighted exact decision variant. `#1438` 27-grid is a finite objective/test, not general NP-hardness. | Exact PARTITION -> weighted threshold MAX CUT, integer and binary-bit-size proofs; OAI general graph same-object bridge and transferred gap |
| Minimum k-cut | Minimisation partition into k parts, not MAX CUT; fixed k has polynomial algorithms, variable k is NP-complete and parameterized-k hardness has separate results. For k=2 connects to s-t mincut (with terminal separation) and global mincut, but **not** MAX CUT. | Existing network-capacity planning owner is only qualitative | Positive-weight graph, k-partition exact objective; fixed-k/variable-k distinctions and algorithm/cost bridge |
| APX | Class of NPO problems with constant-factor polynomial approximation. **Decision Karp reductions do not automatically preserve approximation ratios.** | OAI `OAI.OptimalMaxCut.main` gap construction, `OAI.VertexCover.every_fixed_factor_below_two`; these are family 102 and VertexCover source declarations, not copied proof ownership | AP-reduction / L-reduction and approximation-ratio transport (zero-optimum/weight-sign assumptions explicit) |
| Ford-Fulkerson | Max **flow** through directed capacitated network, not maximum cut; value equals minimum *s-t* cut capacity. Integer capacities give pseudo-polynomial generic augmentations O(E·|f*|), BFS Edmonds–Karp O(V E²); irrational capacities may not terminate under path choice. | `DASHI/Planning/NetworkFlowCapacityCongestionExact.agda` is a toy shared-capacity counterexample, **not** a residual-network/max-flow formalization. `DASHI/Computation/BellmanFordRelaxationScheduleFibreExact.agda` concerns Bellman–Ford shortest-path schedule, **not** Ford–Fulkerson. No same-object algorithm owner found in indexed Agda head. | Explicit residual graph, flow conservation, augmentation preservation, no augmenting path -> min-cut certificate and machine cost |

### Pin the concrete OpenAI math prior art, without a status promotion

- `chboishabba/dashi_lean4` PR #78 imports upstream `openai/math` via a pin, and separately indexes a newer 208-declaration catalogue. Its `SourceAtlas` routes family 102 `OAI.OptimalMaxCut.main`; source inspection at `openai/math/lean/OAI/Computability/MaxCut/Main.lean` shows a Lean theorem constructing gap reductions for every alpha strictly above the Goemans–Williamson ratio, α ≤ 1, with finite TM and soundness/completeness fields.
- OAI `lean/OAI/Computability/VertexCover/Main.lean` proves `VertexCover.every_fixed_factor_below_two` from an explicit gap reduction and a hypothesized α-approximation algorithm (1 ≤ α < 2). It does not establish P ≠ NP.
- Comparator challenge files may include `sorry`; cite actual solution modules and kernel receipts, **not comparator statements**. Neither upstream theorem is automatically an accepted DASHI Lean port or Agda theorem.
- The source-written `scripts/check_openai_maxcut_orbit_objective.py` computes finite quotient objectives, with a strict-loss example when a symmetry-constrained cut excludes unrestricted optima. This is a finite regression, **not** Karp NP-hardness, OAI gap-hardness, or global optimality after quotient.

### Additional exact Agda modules now owned by DASHI

1. `Karp21CliqueVertexCoverExact.agda`: constructive equivalence of a chosen clique and its complementary vertex cover in the complementary adjacency graph, for off-diagonal edges, both directions. It intentionally does not assume the quantitative ℓ=n−k identity; that must be proved for a concrete finite graph before claiming a reduction.
2. `Karp21WeightedCutObjectiveExact.agda`: finite edge-list objective over any carrier/weight type/zero/combine, proves that reversing every Boolean side label preserves the objective, and transports threshold witnesses. This algebraic identity is valid even for **signed** weights. It is **not** a polynomial search algorithm.
3. `Karp21ReductionTransportExact.agda`: inherited NP-completeness across a **supplied** concrete costed many-one reduction.

### Highest-alpha next receipts

- **K02a** concrete finite complement graph, exact vertex-count identity and polynomial bit-complexity witnesses.
- **K03a** the carrier-polymorphic nonedge-incidence family and disjointness-iff-clique theorem are source-written in \`Karp21CliqueSetPackingExact\`, using symmetry. Still owed: finite graph encoding, exact certificate cardinality, polynomial bit/runtime, and pinned Agda kernel check.
- **K05a** Karp PARTITION -> MAX CUT weighted complete graph algebra. For c_i and T=Σc_i, the cut weight is (Σ_{i∈S} c_i)(T-Σ_{i∈S} c_i). Target threshold must be chosen with integer rounding to distinguish equality from near misses. Prove the sign/threshold and binary bit-size cases, not only this formula.
- **K08a** APX / approximation-preserving reduction interfaces for OAI MaxCut and VertexCover with executable same-object source and author credit.
- **K09a** residual max-flow and min s-t cut, exposing a direct graph-cut objective bridge but explicitly **no** mincut-to-maxcut equivalence.
- **K10a** job sequencing versus job-shop typed adapters and upstream ThreeMachine provenance audit.

## Exact finite historical graph

`Karp21HistoricalDagExact.agda` source-writes 21 problem constructors, 20 historical edge constructors, the two list-length equations `twentyOneNamedNodes` / `twentyHistoricalEdges`, and `allNodesHistoricallyReachable`. Those are finite historical **graph indexing** lemmas; they are not proofs that the edges preserve truth or execute in polynomial time. The module is included in `Karp21Everything.agda` for focused later pinned Agda checks.

## Important boundaries
The phrase *max-cut* used for research prioritization in DASHI is not Karp's weighted graph MAX CUT. Likewise Yang-Mills finite compatibility cliques are not the general CLIQUE NP-completeness result. Keep the two uses separate. Optimization and decision variants must be connected by explicit bridges.

Do not promote conditional assumptions, synthetic receipts, small test cases, or source-written code into kernel-verified completeness theorems.

## Executed bounded arithmetic check, and independent Agda build gate

- `scripts/check_karp_partition_maxcut.py` contains the original signed-integer E20 arithmetic check, including zero-total inputs with a fixed positive-threshold YES graph. **Independent local Python checks passed 19,530 positive + 3,906 signed/zero cases = 23,436 total on 2026-11-01**, enumerating all cuts in the same input ranges. The updated committed script itself has not been executed from an exact GitHub checkout.
- The exact arithmetic identity inspected in each case is `4 * score = T*T - (T - 2*A)**2`, with `A` the sum of one side and threshold `ceil(T*T/4)`. This validates the restricted **positive**-integer source transformation experimentally, not the unbounded algorithm, encoded complexity or Agda proof.
- Focused check root: `DASHI/Mathematics/Complexity/Karp21Everything.agda` imports original polynomial reductions plus the four new theorem modules. For a worker with the pinned toolchain: `scripts/run_agda29_parallel_check.sh DASHI/Mathematics/Complexity/Karp21Everything.agda` is fast feedback, but Track A flake remains final promotion authority. **No Agda kernel or checkout-native Python check has been run in this PR yet.**
