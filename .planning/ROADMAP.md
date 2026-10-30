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


## 2026-10-30 — PR #1407 finite cyclotomic sampled-to-index proof cut

Owner: `Docs/papers/R2P2ThreeModeBinaryTernaryNSAliasingMaxCut.md`, section **5j**. This cross-project cut does **not** redefine the historical Feb–Mar geometry closure phases above. Golden: original Agda first, Lean semantic donor second.

- [x] Read original 27/729 and 41/81 Agda index/orbit machinery, exact `BilinearCyclotomicPadCutExact`, C3 Fourier authority boundary, YM finite Fubini, NS finite permutation, newest #1437/#1438 Agda and current #1433 NS, plus actual dashi_lean4 NS files.
- [x] Source-write Q(i) and Q(ζ5) addition/multiplication and distributive laws in the existing scalar owners; instantiate the same generic algebra.
- [x] Source-write generic finite Fubini/add/swap/scale/append/map/concat-map, **original 27×27→729** distributive expansion, and original C4/C5 group-character addition; project into all three TOE roots.
- [x] Independently execute exact arithmetic: 8/64 scalar ring basis triples, 5+5 arbitrary 729-product input pairs, 64/125 original table-derived character-index clauses. Regression scripts extended in place; committed-checkout tests not run.
- [ ] **P0:** kernel type-check each new and previously source-written 365/41, C4/C5 finite owner on the pinned Agda head (no CI requested); repair concrete errors before any machine-checked claim.
- [ ] **P0:** using the generic 729 product/Fubini/character layer, prove `retainedSampledBilinear = fourGridGaussianIndexConvolutionAt` and `fullSampledBilinear125 = indexedFiveGridBilinearAt` for arbitrary actual fields/targets.
- [ ] **P1:** once source and kernel align, attach the same-object Complex3/Leray/Galerkin operator with physical divergence-free energy and signed coefficients; do not import unmerged unrelated lanes silently.
- [ ] **P2:** preserve original R440/R736/B4 physical analytic and real-ODE walls, Ma 87Sr versus R2P2 neutral-Yb measurements, Ibrahim/Monster 3B provenance; no same-object promotion from indices.
