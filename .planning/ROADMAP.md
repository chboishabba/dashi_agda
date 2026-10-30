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


## Alexander horned ternary ABC/S3 max-cut — 2026-10-30 (PR #1244 draft)

This is a scoped additional research lane and does not replace earlier
closure phases. Source-owned plan:
\`Docs/topology/AlexanderHornedRelativeThreeChildHandlebodyProofCut20261029.md\`
and \`Docs/topology/AlexanderHornedABCSixPermutationOrbit20261030.md\`.

- [x] Reinspect existing six-permutation S3 Agda owners, SSSP ABC
  ordering quotient, external-sector S3, current #1244 Agda,
  conditional HornedC3 Lean and current #1414/#1438/#103 PRs.
- [x] Extend the canonical ternary boundary Agda owner with six
  anchored source-word images and a three-class unoriented pairing.
- [x] Add 36-case S3-equivariant algebraic word-family calculations
  and extend the original signed meridian Python regression.
- [ ] Run exact-head golden Agda module kernel typecheck with pinned
  stdlib and (where appropriate) strict safe/trust-escape audit.
  **No kernel success is currently claimed; CI intentionally omitted.**
- [x] New G2/G4 obstruction: compute the source-owned exact threefold
  Nielsen conjugator norm `phi²(q)phi(q)q=w^-1` and the selected
  based normalizer's third iterate `Inn(w)≠id` on free generators.
  Apply classical free-group cyclic centralizers to show every
  other same-peripheral conjugator `q w^k` has residual exponent
  `3k-1`, never zero. See
  `Docs/topology/AlexanderHornedPeriodicCapCocycleMaxCut20261030.md`.
- [x] Separate Newman (1931) periodicity barrier: a nontrivial
  finite-order handlebody automorphism cannot fix a nonempty
  OPEN disk in its connected boundary pointwise; a cap preserved
  merely setwise is different. This is a classical paper
  argument, not an Agda geometry kernel receipt.
- [ ] G2: cap-collar-disjoint actual **non-periodic** supported
  PL Nielsen slide homeomorphism and inverse; do NOT demand
  nontrivial finite order plus pointwise-open-cap fixing.
- [ ] G3: embedded once-punctured torus in actual child complement.
- [x] Check the six source-owned genus-one commutator presentations,
  all 36 algebraic S3 transport cases, and the 36-case equivalence
  between middle-child label p(b) and unoriented parent class.
  These are finite source-written Agda, not 3D G3/G4 completion.
- [ ] G4: prove actual based inclusion of either
  (a) one selected parent class and its stabilizer,
  (b) a geometrically implemented S3-indexed six-boundary
  family, or (c) weak/groupoid relative transport with the
  **nontrivial central boundary twist**.  Strict order-three
  based normalization of the selected nonlinear phi is ruled out;
  changing q by w^k does not repair it.
- [ ] G5–G6: coherent wild satellite limit, collars, and actual
  exterior \`pi1\` via existing conditional van Kampen/colimit.
- [ ] Only after golden Agda acceptance, add a faithful downstream
  Lean finite mirror; do not promote current unverified Lean
  conditional topological consumers.

Priority by max-cut/alpha: actual G2–G4 complement-side construction
before adding more abstract 3/6/9 spectra, polynomial S3 receivers,
trialectic graphs, sonic analogies, or Monster identities. Preserve
Alexander/Hatcher/Nielsen, original DASHI/PR owners and Ibrahim 3B
attribution, and no ESD edits.
