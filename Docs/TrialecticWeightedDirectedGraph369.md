# Weighted directed matrices inside DASHI 369/trialectics

**Status (29 October 2026):** source-written exact finite Agda adapter committed on a
separate branch; **kernel not run**. No `--safe` / no-postulate / totality
certification is claimed without exact-head `agda` and trust-escape checks.

## Origin and reused owners

- Prompt source: an image from Tivadar Danka's 26 October 2026
  “Matrices are graphs” post. A weighted matrix-to-directed-graph
  encoding is standard mathematics; do **not** attribute the invention
  of matrix graph representation to the post.
- DASHI proof ownership: `DASHI/Reasoning/TrialecticWeightedDirectedGraph369Exact.agda`
  adapts `TrialecticObserverMatrix369Exact` (three vertices and nine
  source-target slots), `TrialecticBoundaryFaceNonfactorabilityExact`
  and `ConsumerDescentMinimalObserverExact` (attached-face non-descent),
  `Trialectic369RubikRefinementExact` (nine-trit observer chart), and
  `ArgumentResponseNonGeometricOppositeBidiExact` (structured
  argumentative response ≠ negation or geometric antipode).
- Intersections/category strategies: Leslie McCall, “The Complexity
  of Intersectionality”, *Signs* **30**(3):1771–1800 (2005),
  DOI [10.1086/426800](https://doi.org/10.1086/426800).
  `McCallCategoryStrategyBoundaryExact` is the existing authority
  boundary; no category strategy is derivable from an edge matrix.
- The geometric/pants and fibre authority surfaces remain owned by
  `Trialectic369RubikRefinementExact`, `TypedHyperfabricCore`,
  `GraphColouring369PantsHomomorphismBoundaryExact`, and
  `TypedHyperfabricPantsGluingBridgeExact`. Their separately sourced
  incidence/interface, transport, identity, time and provenance
  obligations are **not** discharged by this example.
- Preserve original mathematical author attribution, independent
  DASHI proof ownership, upstream/meta-introspector source roots and
  prior Ibrahim Monster 3B ownership. This bridge gives no Monster,
  VOA, smooth topology or sociological evidence claim.

## Exact finite instance

With `row = source, column = target` and integer-tenths units, the image is

```text
     A   B   C
A    5  10   0
B    2   0  22
C   18  20   0
```

That is the decimal-weight matrix
`[[0.5,1,0],[0.2,0,2.2],[1.8,2,0]]`, not a ternary-valued matrix.
There are **six** nonzero directed arcs, including one self-loop.
In particular A→B has weight 1 and B→A has weight 0.2;
reversal is not weight preservation, much less logical negation.

The generic 3×3 matrix/chart ↔ directed two-endpoint weight function is
bidirectionally inverse on all nine source/target slots. This is a
**binary relation indexed by a ternary set**. It is not a 3-ary edge.

Let `r : A↦B, B↦C, C↦A`. The vertex permutation satisfies `r³=id`.
But the weighted graph is **not** C₃-equivariant: `w(A,A)=5` and
`w(r(A),r(A))=w(B,B)=0`. A 3-object carrier is not evidence of an
automorphism or associated Monster representation.

## Attached 2-cell and descent obstruction

Define a typed pair `(weightedGraph, attachedFace)`. Two states
sharing *all nine weighted entries* but carrying respectively
`reciprocalFace` and `coerciveFace` have identical graph
projections and different triadic outputs. By the canonical
`ConsumerNonDescentWitness` construction, **no decoder from the graph
projection alone can recover the attached face**.

This is stronger than an ordinary 3-edge boundary counterexample:
even six observed arrows, weights, and every absent edge cannot
recover additional triadic meaning without an independently supplied
face-mediation witness. It does not assert a specific empirical
three-person relationship.

## Matrix powers, typed outgoing-row hyperfabric and binary-in-ternary codec

The direct A→C entry is zero, but the path A→B→C has scaled weight
`10×22 = 220` in hundredths: `(A²)[A,C] = 220/100 = 2.2`.
This is an exact finite two-step-walk calculation (consistent with the
existing `BalabanFiniteSpeedLocalInfluencePathExact` path-support owner),
not a new locality or continuum-semigroup result.

The new owner also instantiates `TypedHyperfabricCore` rather than merely
citing it. Each vertex stalk is its complete outgoing weight row; an
`OrderedEdge(source,target)` has the weight as its edge stalk, with an
`OutgoingIncidence` witness only at the source. The restriction evaluates
the row at the edge target, and `outgoingWeightSection` has an explicit
`compatible` proof. The exact edge-illustration provenance is retained.
The canonical `HyperfabricPantsGluing` is still only an *obligation*:
a domain-specific map from weights to branch channels and a real
`InterfaceMatch` must be supplied before claiming any seam.

## Ternary codec, hypervoxel and pants

The observer's *positions* are an existing nine-slot chart and an
`ObserverMatrix3 SSPTrit ↔ TernaryAddress 3 3` chart, with
`27³=19683` addresses. Values in this screenshot are exact
nonnegative integer-tenths; they **cannot** be silently treated as
SSP trits. A weight codec would require a separately defined
encoding and round-trip proof.

The graph's vertices, oriented arrows, labels and support can serve
as a typed base for local fibres, but a graph adjacency matrix alone
does not define restriction maps, matching sections, an incidence
preserving pants map, smooth gluing, or an intersectional category
translation. Reuse the existing seam compatibility and failure
boundaries rather than promoting shape analogies to theorem authority.

## Max-cut / verification ledger

- [x] Search and reuse canonical observer, face, opposition, hypervoxel,
  typed fabric, McCall and pants owners before introducing the bridge.
- [x] Construct exact matrix ↔ directed graph two-sided round trips.
- [x] Prove the six-arrow fixture and demonstrate asymmetric reversal.
- [x] Exhibit a vertex-level C₃ action and a weighted C₃
  non-equivariance counterexample.
- [x] Reuse non-descent to show the complete weighted graph does not
  determine an attached trialectic face.
- [x] Connect to `EverythingRelationalTrialecticHyperfabric`,
  `TOE369MaxCutKernelBidiTernaryExact`, both focused TOE roots and
  `Unified.Everything`.
- [ ] **Kernel gate:** run exact-head Agda check, inspect
  `--safe`, postulates, unsolved metas, termination escape hatches.
- [ ] **Independent Lean mirror:** ensure mirror statements are
  no stronger than golden Agda and compile under the pinned Lean toolchain.
- [x] Construct a finite outgoing-row `TypedHyperfabric`, explicit
  source-directed incidence, restrictions and a compatible global section.
- [x] Prove the mediated two-step A→B→C contribution despite no direct A→C arc.
- [ ] **Conditional next leaf:** justify a situated weight→pants branch-channel
  interpretation and matching interface if desired. For a 27-voxel pants graph
  homomorphism, first supply *that carrier's* adjacency, not this 3-vertex example.
- [ ] **No silent semantics:** find situated sources for any
  intersectional, psychological, legal, or physical interpretation.

## 2026-10-30 — Native 27-grid/pants adjacency maximal finite cut

**Source-written, not Agda/Lean kernel-verified.** Inspect the actual
existing owner `Base369Ternary27HypervoxelFabricGeometryExact.agda`:
it ALREADY defines `TritGridStep` with only -1↔0↔+1 and
`HypervoxelAdjacent` changing exactly one axis. Do not accidentally
substitute arbitrary unequal-coordinate adjacency (which would connect
-1 directly to +1), or reuse the unrelated three-vertex weighted fixture.

`GraphColouring369PantsGridAdjacencyExact.agda` constructs the new typed
`SlotGridStep` using the existing slot↔SSP bridge, and an explicit
three-path `Pants3Adjacent`. It then constructs:

- actual `GraphHom` terms between the **native** 27-grid and the
  **declared** depth-three pants path graph, both directions, with the
  pre-existing inverse vertex round trips (graph isomorphism as two
  graph-homomorphisms, not a smooth-space equivalence);
- C₃ coordinate rotation commuting with the voxel→pants rechart,
  involutive second-coordinate reflection preserving adjacency, plus
  the **six distinct** coordinate permutations of S₃: ABC, BCA, CAB,
  BAC, CBA, ACB. Their actions on the all-distinct labelled anchor are
  pairwise distinct, and each transports declared adjacency;
- a nontrivial **two-colour checkerboard** using XOR of the three
  middle-trit indicators. Every one-step grid edge changes the parity.
  A concrete origin→positive-X edge rules out a singleton proper
  palette. Consequently this finite graph and its isomorphic pants
  graph have exactly two colours as a minimal proper palette;
- proper-colouring pullbacks along C₃ rotation and seam flip without
  claiming a 4-colour theorem, Hedetniemi equality, topology, physical
  coupling, or empirical social interactions.

An independent exhaustive Python evaluation of the combinatorial
semantics finds **27 vertices, 108 oriented nearest-neighbour arcs
(54 undirected edges)**, degrees 3×8, 4×12, 5×6, 6×1; it checks the
six permutations, reflection and two-colouring. The source for the
reproducible audit is
`scripts/verify_trialectic_369_graph_pants_finite.py`. These are
finite computational receipts, not Agda/Lean kernel verification.

**Conservative live status:** the existing
`GraphColouring369PantsHomomorphismBoundaryExact` canonical flags
stay false for kernel-certified closure. New source-written terms
and an explicit candidate status have been exposed separately.
Do not silently promote source-writing to typechecking.

### Snowball and Pareto bridge

`BalabanIbrahimParetoSnowballTOEExact` consumes the source-written
finite colouring/rotation/flip and imports the already-authored
`GraphColouringRecolourPantsSnowballExact` and
`IbrahimSnowballDependencyNDimLocalGlobalProofSearchBidiExact`
non-promotion gates. An admissible local proper colouring **does not**
automatically pay a globally compatible pants seam or source authority.
No inherited Ibrahim Monster3B results or original historical authorship
are reassigned.

**Next live max-cut (dependency order):**
1. Golden Agda `--safe` exact-head check and trust-escape/termination scan;
   fix each concrete compiler error; then pinned Lean mirror exact-head check.
2. Prove branch-channel interpretation and real `InterfaceMatch` for a
   *specified situated consumer* if one exists. Do not invent authority,
   continuous pants or source-independent human categories.
3. For higher-order trialectic emergence, provide an actual existing
   `FaceMediationLaw` / `SecondOrderCellGluing` instance and transport
   an independently sourced attached 2-cell; full weighted graph or
   proper colouring alone cannot recover that face.
4. Retain compatibility with actual six-permutation S₃, restricted C₃
   and asymmetric weighted counterexamples. Never promote the 3-node
   image to a C₃-invariant weighted graph.
5. Only after source/semantic conditions are met, transport to
   Ibrahim, Pareto, legal and physics consumers with separate
   theorem/receipt authority.

### Sources and attribution

- Existing formal geometry, ternary path, 2026-10-26 Danka educational
  matrix image, and exact finite Agda/Lean proofs are attributed
  separately: the **matrix-as-digraph correspondence is standard prior
  art** and the new graph-isomorphism/checkerboard adapter belongs to
  the DASHI repository authors.
- Michael F. Atiyah, *Topological quantum field theory* (1988),
  DOI 10.1007/BF02698547: topology/gluing terminology, **not**
  certification that a discrete pants path is a smooth cobordism.
- Aida Abiad et al., *Hypergraphs and simplicial complexes in focus*
  (2026), DOI 10.1088/2632-072X/ae3c4e: higher-order networks vs
  pairwise interactions, **no theorem imported**.
- Stefano Fiorini, Hakan Emre Aktas, Iulia Duta, Pietro Morerio,
  Alessio Del Bue, Pietro Liò, Stefano Coniglio,
  *Sheaves Reloaded: A Direction Awakening*, ICLR 2026
  (https://proceedings.iclr.cc/paper_files/paper/2026/hash/0954a37c03775409e295fb4b99b664c7-Abstract-Conference.html):
  direction-aware cellular sheaf comparison only; no DSNN experiments
  or directed Laplacian results have been proved in DASHI by this work.
- Shitov, 2019 Hedetniemi counterexample; Inoue et al., 2026
  four-colour work; original meta-introspector/Ibrahim and
  Monster3B sources retain the ownership already specified in the
  canonical source atlas. Their proofs are **not** claimed here.
