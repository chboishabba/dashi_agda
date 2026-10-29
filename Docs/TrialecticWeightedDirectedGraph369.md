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
- [ ] **Conditional next leaf:** instantiate an actual
  provenance-bearing `TypedHyperfabric` over this graph only after
  choosing relevant fibres, incidence/restrictions and compatible
  global sections. For a 27-voxel pants graph homomorphism, first
  supply *that carrier's* adjacency, not this 3-vertex example.
- [ ] **No silent semantics:** find situated sources for any
  intersectional, psychological, legal, or physical interpretation.
