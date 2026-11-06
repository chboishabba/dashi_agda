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


## Cross-domain geometry lane: Gielis × Base369 (November 2026)

**Authority:** [GielisBase369Roadmap.md](../Docs/support/reference/GielisBase369Roadmap.md).
**Implementation:** [PR #1466](https://github.com/chboishabba/dashi_agda/pull/1466), draft;
the original closure phases above remain unchanged.

- [x] Phase G0: prior-art owner mapping (dihedral, Nyquist/Shannon, MDL/Kolmogorov, SO(3)/torque, log-polar spiral).
- [ ] Phase G1: G01/G06 native C18 and 36-sector exact proofs **kernel-accepted**; three new sources present but compiler receipt outstanding.
- [ ] Phase G2: G02–G05/G08–G09 ordinary-real Gielis identity, cyclic/dihedral continuum, area/curvature.
- [ ] Phase G3: G07/G10–G12/G19 native Fourier, sampling and convergent Dirichlet spectrum.
- [ ] Phase G4: G13–G16/G21 original Kozyrev HTML raymarcher same-apparatus reproduction, calibrated angular impulse, non-369 controls, CI and Pareto.
- [ ] Phase G5: G17/G18/G20 inverse/MDL/product-symmetry proofs, reproducible paper and independent physical validation.

**Deliverables:** D0 prior-art map; D1 kernel receipt; D2 continuous geometric
library; D3 spectral certification; D4 source/geometry parity; D5
control/Pareto benchmark; D6 empirical validation; D7 inverse compiler and
publication. The exact G01–G21 lemma list, dependencies, owners, tests and
nonpromotion rules live exclusively in the linked lane roadmap.

### Gielis round-2 mathematical certificates, separate from Golden acceptance

- [x] Paper-level exact special-case Gielis identity, smooth star boundary,
  3/6/9 dihedral symmetry, and common area `sqrt(2)*pi` (E01–E03).
- [x] Paper-level normal/curvature formulas and 3/6/9 nonconvexity (E04).
- [x] Full finite cyclic-group projector identity and exact selected 36-sample
  bandlimited reconstruction, with 18-sample aliasing counterexample (E05–E06).
- [x] Standard-theorem argument for Dirichlet compact resolvent and disk/Faber–Krahn
  first-eigenvalue bounds; **not** a mesh-error proof (E07).
- [x] Correct wall-versus-ray impulse sign and derive conditional optical
  power-to-SI-torque conversion; no measured power claim (E08).
- [x] Explicit zero-modulation inverse-identifiability counterexample and
  C27 versus C3^3 nonisomorphism; computational prefix code (E10–E11).
- [ ] G01–G05/G07/G08/G09/G10/G11/G19: **ordinary-real Agda kernel**
  certificates for the paper mathematics and finite carrier transport.
- [ ] G12: rigorous numerical PDE eigenvalue discretization convergence/errors.
- [ ] G13–G16/G21: original HTML Kozyrev mirror source/collision parity,
  committed-head executable receipt, optical power calibration and CIs.
- [ ] P5: independent physical measurements and replication.

See [Proof theorems](../Docs/support/reference/GielisBase369ProofTheorems.md)
for E01–E11 and [exact gate roadmap](../Docs/support/reference/GielisBase369Roadmap.md)
for G01–G21, status, phases, dependencies and D0–D7.
