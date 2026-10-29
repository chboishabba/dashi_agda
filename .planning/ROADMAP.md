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


## 2026-10-29 — AO fleet discriminator and Max Cut convergence

### Current problem

The previous fleet view mixed spectral basis coordinates, semantic topics, subtopics, fibres, and executable goals. It also treated capacity-bounded worker width as if it implied full W = 20 concurrency.

The corrected hierarchy is:

```text
MP eigenspace basis
→ primary topic quotient
→ subtopic orbit
→ complete-link fibre
→ typed unblocked goal
```

The two supported spectral truncation choices are K = 50 and K = 100.

Topic admission rejects lexical noise before quotienting. Hex literals, pointer-like memory addresses, raw UI tokens, and raw DOM tokens cannot become topic labels.

### Reuse

Use the existing #1415/#1416/#1417 theorem owners as donors.

Do not create a second residual, Pareto, or conductor calculus.

Reuse existing finite Laplacian, Yang–Mills commutator, and Navier–Stokes commutator owners for the Max Cut bridge.

### New acceptance gates

- [x] Golden Agda defines all five scale levels.
- [x] Golden Agda records K = 50 and K = 100 explicitly.
- [x] Golden Agda defines a typed token-admission firewall.
- [x] A full schedule is total over twenty worker slots.
- [x] Every scheduled goal is unblocked.
- [x] Every scheduled goal is Pareto eligible.
- [x] Every distinct scheduled pair has noTypedMeet evidence.
- [x] Finite Max Cut has explicit partition, crossing-edge, Laplacian, and SDP-receipt interfaces.
- [x] Max Cut operator reuse does not promote a Yang–Mills or Navier–Stokes same-object theorem.
- [x] Lean mirrors the golden public contract.
- [x] dashiBRAIN tests the concrete token filter, stratifier, full-width scheduler, and finite cut diagnostics.

### Live non-promotion boundary

Spectral rank does not create truth.

Topic clustering does not create theorem authority.

A finite graph cut does not create a gauge equation.

An SDP relaxation does not create a PDE estimate.

Worker occupancy does not create proof authority.
