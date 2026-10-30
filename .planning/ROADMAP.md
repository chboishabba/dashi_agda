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
