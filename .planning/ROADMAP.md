# Roadmap: DASHI Agda Closure

## Overview

Stabilize the empirical geometry layer (Fejér/prox/MDL/cone with snap exceptions), then sweep remaining postulates and formalize signature elimination and closure harness wiring.

## Domain Expertise

None

## Phases

- [ ] **Phase 1: Geometry Seam Hardening** - snap signatures, cone interior predicates, Lyapunov wiring.
- [ ] **Phase 2: Postulate Sweep** - replace remaining low‑risk postulates with constructive proofs.
- [ ] **Phase 3: MDL Integration** - make Lyapunov/MDL claims explicit across closure layers.
- [ ] **Phase 4: Signature Elimination** - encode orbit‑profile discriminator and masked‑Q elimination seam.
- [ ] **Phase 5: Closure Harness** - consolidate empirical→full wiring and documentation.

## Phase Details

### Phase 1: Geometry Seam Hardening
**Goal**: Formal snap exception class + cone interior predicate + Lyapunov witness wiring.
**Depends on**: None
**Research**: Unlikely
**Plans**: 2 plans

Plans:
- [x] 01-01: Define snap signature instance and cone interior predicate for shift.
- [x] 01-02: Wire cone‑monotone‑except‑snaps to shift operator.

### Phase 2: Postulate Sweep
**Goal**: Remove remaining low‑risk postulates (e.g., periodicity, simple order properties).
**Depends on**: Phase 1
**Research**: Unlikely
**Plans**: 2 plans

Plans:
- [x] 02-01: Scan for postulates in numeric/finite modules; replace with stdlib lemmas.
- [x] 02-02: Validate compile of affected modules.

### Phase 3: MDL Integration
**Goal**: Make MDL Lyapunov/Fejér concrete in closure adapters.
**Depends on**: Phase 1
**Research**: Unlikely
**Plans**: 2 plans

Plans:
- [ ] 03-01: Provide MDL Lyapunov witness in empirical→full adapter.
- [x] 03-02: Add beta‑space seam instance or hook to CSV evidence.

### Phase 4: Signature Elimination
**Goal**: Encode masked‑Q rank / orbit‑profile discriminator as signature lock seam.
**Depends on**: Phase 1, 3
**Research**: Likely (mapping empirical evidence to Agda predicates)
**Research topics**: Masked‑Q screening assumptions, orbit‑profile fingerprint constraints
**Plans**: 2 plans

Plans:
- [x] 04-01: Define `SignatureLock` instance shape + eliminator lemma skeleton.
- [x] 04-02: Wire empirical mask ranking into signature lock stub.

### Phase 5: Closure Harness
**Goal**: Consolidate wiring and update project docs.
**Depends on**: Phase 2–4
**Research**: Unlikely
**Plans**: 2 plans

Plans:
- [ ] 05-01: Merge empirical harness with full closure pack.
- [ ] 05-02: Update `.planning/CONTEXT.md` and `.planning/COMPACTIFIED_CONTEXT.md`.

## Progress

| Phase | Plans Complete | Status | Completed |
|-------|----------------|--------|-----------|
| 1. Geometry Seam Hardening | 2/2 | Complete | 2026-02-28 |
| 2. Postulate Sweep | 2/2 | Complete | 2026-02-28 |
| 3. MDL Integration | 1/2 | In progress | - |
| 4. Signature Elimination | 2/2 | Complete | 2026-03-01 |
| 5. Closure Harness | 0/2 | Not started | - |

## 2026-10-29 — Weighted directed graph / trialectics 369 seam

- [x] Reuse three-position observer matrix, attached two-cell, non-geometric argument opposition, ternary hypervoxel and typed pants owners.
- [x] Source-write exact rational-in-tenths 3x3 ↔ directed weighted graph round trips, 6-arc specimen, C3-weight obstruction and full-matrix attached-face non-descent.
- [x] Wire relational rollup, TOE roots, Unified aggregate and 369 Max Cut facade.
- [ ] Golden Agda exact-head kernel check, --safe/no-postulates/no-metas/no-termination-escape scan; no certification until run.
- [ ] Check Lean mirror against golden proof statements under pinned toolchain.
- [ ] Supply separately sourced hyperfabric stalk/incidence/section compatibility and 27-pants adjacency if advancing beyond the finite graph boundary.

See `Docs/TrialecticWeightedDirectedGraph369.md` for attribution, the weight convention, proofs and non-promotion obligations.

- [x] Follow-on: finite weight-graph outgoing-row hyperfabric section with incidence/restriction compatibility and mediated two-step path result (A²)[A,C]=2.2.

## 2026-10-30 — Pareto/max-cut revision: native pants adjacency

- [x] Inspect existing `TritGridStep`/`HypervoxelAdjacent`, pants-path
  round trips, generic `GraphHom`, and snowball/Ibrahim proof boundaries.
- [x] Source-write explicit nearest-neighbour `Pants3Adjacent` and
  both directions of native voxel/pants graph homomorphisms.
- [x] Source-write C3 rotation, second-slot seam flip, all six distinct
  S3 coordinate permutations, and adjacency transport.
- [x] Source-write a nontrivial two-colour proper colouring,
  a singleton-colour obstruction and colour pullbacks.
- [x] Add independent finite exhaustive semantics audit and
  Pareto/snowball/Ibrahim non-promotion consumption; link TOE roots.
- [ ] **P0 verification**: exact-head safe Agda; then pinned Lean;
  synchronize branch if master moves; no CI obligation in this tranche.
- [ ] **P1 situated seam**: independently supplied branch-channel
  mapping, `InterfaceMatch`, matching restrictions and provenance.
- [ ] **P2 triadic mediation**: existing `FaceMediationLaw` /
  `SecondOrderCellGluing` with original graph retained.
- [ ] **P3 stronger actions**: preserve typed colourings and sourced
  consumer invariants under specific permissible group actions.
- [ ] **P4 TOE/physics**: only theorem-bearing cross-domain transport,
  no 3B/smoothness/continuum/scientific authority from numerology.

For the precise finite cut and citations, see
`Docs/TrialecticWeightedDirectedGraph369.md`. Older MDL / signature
closure obligations in the five-phase roadmap above are independent;
this 369 lane does not mark those completed.

## 2026-10-30 — P2 finite medial instance (not semantic closure)

- [x] Reuse existing `FaceMediationLaw`,
  `GrothendieckFaceMediatedSection`, `promoteGrothendieckMediated`
  and non-descent witnesses.
- [x] Source-write one explicitly selected synthetic policy, an
  inhabited carry and a proof candidate that the selected output
  fails to descend from the complete weighted graph.
- [ ] A **situated, source-authorized** mediation law and admissible
  interfaces (separate from finite selected demonstration).
- [ ] Exact-head `--safe` Agda and downstream pinned Lean verification
  for both the pants graph/colour and selected mediation owners.

## 2026-10-30 P0/P1 native weighted max-cut and QID high-alpha cut

Maximal edgewise two-way cut can be derived from existing proved-candidate
checkerboard properness. This bridges the user's graph-as-matrix
example and 27-grid without falsely identifying them. Reuse graph
isomorphism and a transported palette witness. QIDs are concept-only
coordinates and cannot provide source, semantics, physics, or authority.

- [ ] Source-write edge-saturated maximum cut for any nonnegative native
  graph edge weights; record unit-weight 54 edge finite audit separately.
- [ ] Verify QIDs against live Wikidata labels and source-atlas ownership.
- [ ] Integrate into Ibrahim/Pareto snowball and downstream Lean.
- [ ] Kernel-check each construction on exact branch head; keep
  source-written and kernel-paid status split until then.

## 2026-10-30 additional P1: directed two-ended fabric

Source-side outgoing-row hyperfabric is already a finite fixture.
The higher-value next cut is a **both-endpoint compatible section**
that preserves the orientation and witnesses asymmetry. Reuse the
existing `TypedHyperfabricCore`, not a new sheaf/hypergraph ontology.
QIDs and 2026 directed-sheaf sources are attribution/comparison only.

## 2026-10-30 source-written closure ledger — weighted max-cut/QID

- [x] Native edgewise cut saturation and generic Nat-weighted
  finite-list optimality, plus exact source-level 54-edge unit witnesses.
- [x] Actual QID identities for ten graph/colouring/max-cut concepts;
  specific fixture identity remains unresolved.
- [x] Two-ended directed hyperfabric compatible section with
  independently oriented source/target restriction maps.
- [x] Golden TOE/import and Lean downstream mirrors synchronised.
- [ ] Agda/Lean kernel verified status; exact-head transcript and safe,
  metas, termination, postulate scans. No CI dependency.
- [ ] 54-edge formal completeness/uniqueness and genuine selected
  situated pants/gluing or face mediation interface.

## 2026-10-30 QID role-typing refinement

- [x] Type QID graph concept roles; distinguish discipline,
  structure, representation, morphism, problem, theorem.
- [x] Reuse existing Snowball Dewey/QID coordinate and inspected
  511.54 directed graph vs 511.5 graph theory parent.
- [x] Lean mirror role-indexed concept vocabulary.
- [ ] Exact-head kernel checks and situated face/seam authority.

## 2026-10-30 — further high-alpha 369 edge-coverage / symmetry cut

- [x] Source-write native adjacency orientation canonicalisation
  covering each of the three axes and four directed step cases.
- [x] Source-write 54-slot chart, explicit map into existing
  54-unit-edge witnesses and exact closed 0–53 slot-index census.
- [x] Source-write all six S3 actions and the seam reflection as
  *fixing the actual selected cut*, not just proper-colouring existence.
- [x] Mirror both finite surfaces downstream in Lean; extend local
  Python test with 54-edge/108-orientation and 162+27 action checks.
- [x] Attach 2026 CSNN/Directo author/source roots to existing
  attributed-source atlas; do not import algorithms or benchmarks.
- [ ] Golden exact-head kernel, Lean pinned kernel, and Agda
  abstract slot-index injectivity/list Nodup certification.
- [ ] Sourced, consumer-specific higher-order face/pants transport
  and real direction-preserving weighted representation actions.


## 2026-10-30 reuse-first local Python / Max-Cut / QID cut

- [x] Inspected **actual existing** `GraphColouring369PantsWeightedMaxCutExact.agda`, `GraphColouring369PantsSymmetryCutInvariantExact.agda`, `GraphColouring369PantsQidParetoSnowballExact.agda`, and Lean mirror `AgdaMirror/Reasoning/GraphColouring369PantsMaxCutQid.lean`. Do not duplicate the native 27-vertex graph, its 54 edges, its already source-written all-nonnegative-weight saturating checkerboard theorem, or its typed QID identities. These are **source declarations, kernel acceptance pending**.
- [x] Extend **existing** `scripts/verify_trialectic_369_graph_pants_finite.py` (commit `0615b1452cdf3c6f8ff05119ced21f8896c7fa56`) with deterministic BFS over 54 native undirected edges; show all 27 vertices reachable; for each initial colour, forced edge-crossing propagation uniquely reconstructs the checkerboard or complement. The classical connected-bipartite-graph implication says **when all 54 weights are strictly positive**, every optimum cut must saturate every edge, and these two partitions are the only optima. No enumeration of all `2^27` partitions is claimed. The updated exact branch script was not executed from a checkout.
- [x] Independently execute local Python `verify_dashi_27grid_maxcut.py`: 27 vertices, exactly 54 undirected edges, six coordinate S3 symmetries, three coordinate reflections, 750 seeded nonnegative-weight assignments and 150,000 sampled challenger cuts. All passed; this is a computational fixture receipt, **not** Agda/Lean kernel acceptance.
- [x] Inspect existing graph-QID source: **maximum cut Q942557**, **bipartite graph Q174733**, and other ten prior concept IDs; checked those two against current Wikidata item pages. These identify concepts, not the private DASHI native-grid instance, not historical publication priority, not the underlying proof, not the distinct 27-function conjugation quotient, and not the Monster 3B representation. Reuse `SnowballExternalIdentityAvailabilityExact`, typed `KnowledgeRole`, and the independently authored Ibrahim provenance custody.
- [ ] **Genuine Agda uniqueness theorem** for strict positive weights and whole 54-edge grid needs a canonical connected path/certificate and extensional comparison of all optimal partitions to the two checkerboards; BFS Python is not a kernel theorem.
- [ ] Source-checked same-object adapter to OpenAI family-102 **simple unweighted** `Graph.cutSize` with `u<v` orientation and canonical binary graph printer; distinguish the closed native bipartite class (trivial exact optimum) from unrestricted hardness. No unrestricted graph 102 theorem or SAT 378 speedup follows from this native fixture.
- [ ] Exact-head Agda and Lean compiler receipts; no CI dependency and no ESD edit.
