# Changelog

This changelog is append-only. Older mentions of `false` are historical wave
records unless the entry explicitly states it is describing the current live
monitor surface.

## 2026-07-19 — Wetsuit seam optimisation boundary

- Added `DASHI.Geometry.WetsuitSeamOptimisationBoundary`, a fail-closed typed
  carrier for body-zone design priors, material/panel budgets,
  manufacturability evidence, weighted seam cost, admissibility, relative
  optimality, validation gates, and split advice.
- Added `DASHI.Geometry.WetsuitSeamOptimisationRegression` with canonical
  underarm/inner-leg preference and shoulder/spine avoidance prior receipts,
  while keeping continuum optimality and manufacturing authority explicitly
  unpromoted.
- Added the compact aggregate `DASHI.Geometry.WetsuitSeamOptimisation`.
- The module formalises the optimisation and obligation surface only; it does
  not claim universal biomechanics, continuum-mechanics closure, or certified
  manufacture. `DASHI.Everything` was not run in this connector-backed pass.

## 2026-07-13 — P06 duplicate-free valid-walk enumeration

- Added and focused-checked `P06GeneratedWalkUniqueness.agda`.  Under the
  canonical neighbour adapter it proves extension-block `NoDuplicates`,
  recursive block disjointness, and
  `generatedWalkVertexListsNoDuplicates` without postulates or proof-heavy
  `WalkObject` equality.
- Added `GeneratedWalkVertexListSemantics`, packaging generated valid-walk
  lists, extensional completeness, duplicate-freedom, and the single
  `countWalks ≡ length` bridge.
- Added focused-checked additive `P06ConcreteEnumerationEndpoint.agda` and
  `P06SkeletonEnumerationSurface.agda`.  The former makes DFS membership an
  explicit field of a membership-indexed map; neither module touches the
  legacy total-index API.
- Added focused-checked `P06ConcreteSkeletonWitness.agda`, which proves all
  individual-candidate chooseN facts and packages the remaining skeleton list
  obligations (`complete`, vertex-list uniqueness, and count agreement)
  without pretending they are derivable from an arbitrary list.
- Added focused-checked `P06DFSValidWalkSurface.agda`.  It packages the
  minimal per-skeleton `WalkObject` plus equality to `dfsWalkRange`, derives
  generated-list membership and soundness, and adapts map witnesses to the
  membership-indexed endpoint.  It deliberately does not infer path validity
  from `DFSCover` coverage alone.
- `Everything.agda` was not run.  The remaining P06 mathematical blocker is
  now the genuine DFS-valid-walk membership witness; the legacy total-index
  record remains compatibility-only.

## 2026-07-13 — Corrected P06 walk status

- Corrected the P06 record: recursive walk completeness has landed through
  `walkObjectsCompleteByVertices`, and successor-membership inversion has
  landed through `walkObjectsSucMemberByVertices` and
  `walkObjectExtendMemberByVertices` in
  `DASHI/Physics/YangMills/GraphCombinatorics.agda`.

## 2026-10-29 — Weighted directed 3×3 graph inside 369/trialectics

- Added `TrialecticWeightedDirectedGraph369Exact`: exact integer-tenths graph/matrix equivalence, six nonzero directed arcs, asymmetric reversal, a genuine order-three vertex permutation and a counterexample to weighted C3 invariance.
- Reused the canonical trialectic attached-face non-descent constructor to prove that identical complete weighted graph projections can carry distinct irreducible triadic faces.
- Bridged existing opposition, McCall category strategies, SSP hypervoxel address, typed hyperfabric compatibility and 27-pants adjacency *without* promoting analogies into proof authority; connected both TOE roots, the relational rollup, Unified.Everything and 369 max-cut.
- Source prompt: Tivadar Danka's 26 October 2026 educational illustration; mathematical matrix/graph correspondence remains standard prior art. Kernel verification and downstream situated gluing remain open; ESD surfaces untouched.

- Follow-on: exhibited a real source-directed `TypedHyperfabric` with compatible outgoing-row section; independently proved the missing direct A→C arrow has nonzero length-two weight 2.2 through B. Seam remains conditional on a branch-channel interpretation and `InterfaceMatch`.

## 2026-10-30 — Native 27-grid/pants graph isomorphism, checkerboard and six S3 permutations

- Reused pre-existing one-ternary-step `HypervoxelAdjacent` and
  voxel↔pants depth-three carrier round trips. Source-wrote exact
  graph homomorphisms in both directions; did not invent arbitrary
  adjacency, a new pants manifold or a new graph ontology.
- Added C3 coordinate rotation, independent second-slot reflection,
  all six distinct S3 labelled coordinate permutations and typed
  adjacency-preserving actions.
- Added checkerboard 2-colour properness, explicit one-colour
  obstruction, and palette-colouring transport under finite actions.
- Mirrored the finite graph results in the downstream Lean branch,
  and added standalone exhaustive Python combinatorics checks.
- Extended TOE/max-cut and Ibrahim/Pareto/snowball facades, preserving
  local-vs-global, source-vs-proof, graph-vs-hyperedge, 3B ownership,
  and discrete-vs-smooth non-promotion rules. All **kernel gates pending**.

## 2026-10-30 — Selected graph/face-to-depth carry

- Added `TrialecticWeightedGraphFaceMediationSelectedExact`, reusing
  existing Grothendieck face mediation and next-depth carry interfaces.
- Constructed one explicitly labelled synthetic three-case face policy
  and a selected 27-cell output, proving source-written non-factorability
  of that output through the original complete weighted graph.
- Mirrored the exact finite non-descent surface in Lean. No general
  social/physical mediation, higher stack, Monster3B, smooth pants,
  external source authority or kernel verification promoted.

## 2026-10-30 — Weighted native graph max-cut, QID identity and both-ended directed fabric

- Added golden `GraphColouring369PantsWeightedMaxCutExact`: checkerboard
  edgewise saturation and universal maximum cut for finite supported
  native 27-grid edges with arbitrary nonnegative Nat weights;
  constructed 54 unit edge witnesses with source-level length/weight
  candidates, separate from Python 54-edge exhaustive semantics audit.
- Added `GraphColouring369PantsQidParetoSnowballExact`: verified
  Q131476, Q1137726, Q727035, Q504843, Q174733, Q303100,
  Q3385162, Q942557, Q840247 and Q184410; unresolved synthetic
  fixture; QID, 2019 Shitov, 2026 Inoue et al., DSNN/DSHN original
  authors and prior Ibrahim/Monster3B proof ownership remain distinct.
- Reused `TypedHyperfabricCore` in
  `TrialecticDirectedSourceTargetHyperfabricExact`: both-ended
  source/target restriction maps, compatible oriented-edge global
  section, explicit forward/reverse asymmetry and a self-loop.
- Added downstream Lean mirrors, wired existing focused TOE roots,
  corrected `GraphColouringRecolourPantsSnowballExact` citation from
  2026 arXiv v2 to inspected v3 (revised 1 October 2026); updated
  deterministic Python companion with heterogeneous weights and QIDs.
- No Agda/Lean kernel, transitive `--safe`, CI, DSNN performance,
  real-world semantics, physical field theory, Monster same-object,
  or smooth pants certification has been performed or claimed.

## 2026-10-30 — QID role-typed Snowball refinement

- Extended the verified QID atlas with typed knowledge roles and a
  directly inspected directed-graph Dewey 511.54 coordinate, reusing
  the existing Snowball KnowledgeCoordinate constructor; general
  graph theory 511.5 remains a broader classification.
- Mirrored these role types in Lean; independent Python finite audit
  sampled nonuniform weights totalling 344 on all 54 native edges.
  No role coercion, source QID, or computed equality upgrades proof
  ownership, semantic face authority, physical theory or kernel state.

## 2026-10-30 — Orientation normal form and S3-fixed optimal cut

- Added `GraphColouring369PantsEdgeCoverageExact`: actual three-axis
  one-step adjacency admits a 54-slot increasing-edge chart with
  explicit reversal classification, an exact witness-list rechart and
  a closed 0..53 slot census.
- Added `GraphColouring369PantsSymmetryCutInvariantExact`: all six
  S3 permutations and the second-coordinate sign reflection fix the
  selected bipartite maximum-cut partition, not just proper-colouring
  existence. No arbitrary directed-weight equivariance promoted.
- Added Lean edge-coverage/Nodup and symmetry-fixed-cut downstream
  mirrors. Extended native Python audit with 54 unique undirected
  charts, all 108 oriented edges, 162 S3 and 27 reflection checks.
- Updated ICLR 2026 directed-sheaf/hypergraph and asymmetric-generator
  author-level primary-source comparisons via the canonical QID/source
  atlas; no DOI/QID identity or inherited proof ownership invented.
- Kernel/--safe certification, global seam semantics and general
  same-object/physical promotion remain explicitly open.

- Extended canonical edge chart with a source-written propositional
  `NoDuplicateSlots` proof for the exact 54-slot list, rather
  than equating a raw Boolean field or numeric census with proof.
  Generic index/endpoint injectivity and kernel certification remain
  separate.

## 2026-10-30 — Actual C3-invariant orbit sum of an asymmetric directed graph

- Added `TrialecticC3WeightedOrbitSymmetrizationExact`, which
  creates a NEW exact cyclically invariant Nat-weight function
  from three rotations of the original 3×3 directed graph.
- Recorded the new `[[5,50,22],[22,5,50],[50,22,5]]`
  integer-tenths matrix and explicit non-identity witness against
  the original; no new Monster representation claimed.
- Reused existing two-ended directed hyperfabric roles and
  restrictions to instantiate a compatible section with pointwise
  C3 outgoing/incoming row transport.
- Added and imported the downstream Lean mirror and wired the
  golden TOE and Ibrahim/Pareto roots; kernel validation pending.

## 2026-10-30 — graph-wave consumer-loss max-cut for twin-prime and Pickover transfer

- Added `DASHI/Reasoning/TrialecticGraphWaveConsumerLossCutExact.agda`: two actual directed 3-vertex graphs have identical C3-symmetrised 3×3 weighted adjacency matrices but different selected directed-weight and original `WaveAlgorithmLift` signed-trit consumers. Instantiates existing consumer-indexed collision and proves a generic no-postprocessing theorem for any deterministic wave/spectrum of the averaged matrix.
- Original graph's full matrix BIDI recovers the selected edge; both fine directed hyperfabric global sections remain compatible. Thus neither orbit averaging nor compatible sheaf-like gluing automatically preserves a terminal signed consumer.
- Related exact first-principles obligations to PR #1408 (actual prime correlation and cofinal analytic separation) and PR #1260 (true `π` phase enclosure at factorial index) in the graph documentation. No analytic twin or sine-sign theorem promoted, no independent Ibrahim/Pareto/Snowball/QID ownership changed.
- Four canonical graph/TOE import roots updated; independent integer 3×3 audit passed; checker committed. Source-written Agda, kernel pending, no ESD edit or CI.

- Added an exact finite four-phase wave parity counterfeit to graph-wave consumer-loss Agda source: nonnegative four-site f=(1,1,0,0), DFT modes (2,1−i,0,1+i), mode norms (4,2,0,2), but zero +2 correlation and zero signed spectral numerator. Reuses existing `ShiftDiscreteWaveStep` and `ShiftUnitaryLikeConstraint`; independent exact integer test PASS. This is an analytical *method-discriminator*, not prime distribution or terminal sine-sign proof. Attribution and authority boundaries unchanged.

- Completed the **positive** graph-wave residual repair: original unaveraged matrix is an inhabited consumer-sufficient residual for selected directed-weight and signed finite-wave observers, and `fullDirectedMatrixStrictlyRefinesC3Orbit` proves original source-owned strict refinement. This is all-graph source-level proof, not just the fixture. Agda kernel pending.
