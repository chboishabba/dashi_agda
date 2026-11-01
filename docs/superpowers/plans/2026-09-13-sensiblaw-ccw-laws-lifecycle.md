# SensibLaw CCW/LAWS Lifecycle Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a reusable, source-bounded SensibLaw lifecycle for international instruments, instantiate the September 2026 CCW/GGE LAWS state, and connect it to the existing defensive counter-UAS authority boundary.

**Architecture:** Keep lifecycle/legal-effect/applicability coordinates orthogonal and source-bound. Reuse query-indexed non-factorability to prove textual consensus alone cannot determine binding legal effect, then add only a thin application bridge to #913.

**Tech Stack:** Agda, existing DASHI authority/provenance/query-adequacy cores, GitHub Actions focused Agda 2.9 workflow.

**Spec:** `docs/superpowers/specs/2026-09-13-sensiblaw-ccw-laws-lifecycle-design.md`

## Global Constraints

- Primary/official source first for legal-status claims.
- Do not invent DOI, QID, Dewey, OEIS, treaty status, or authority metadata.
- Citation/source identity never promotes into legal authority or applicability.
- September 2026 GGE consensus elements remain distinct from an adopted/in-force instrument.
- Do not add operational jamming, waveform, targeting, power, or defeat-recipe content.
- Preserve acquisition-order independence while forbidding downstream payment from skipping unpaid lifecycle dependencies.

---

### Task 1: RED regression surface

**Files:**
- Modify: `DASHI/Applications/CounterUASDroneShieldRegression.agda`

**Interfaces:**
- Consumes: existing #913 regression root.
- Produces required names from the future lifecycle, CCW fixture, and application bridge so the focused Agda job must fail before implementation exists.

- [ ] Add imports for `DASHI.Law.SensibLawInternationalInstrumentLifecycleExact`, `DASHI.Law.SensibLawCCWLAWS2026Exact`, and `DASHI.Applications.CounterUASSensibLawAuthorityBridgeExact`.
- [ ] Add regression fields requiring the consensus/legal-effect adequacy defect, the joined-observer adequacy repair, the September 2026 unresolved instrument nature, source-atlas non-promotion, and the counter-UAS international-law no-promotion boundary.
- [ ] Commit and observe the focused workflow fail specifically because one or more imported production modules are missing.

### Task 2: Generic international-instrument lifecycle

**Files:**
- Create: `DASHI/Law/SensibLawInternationalInstrumentLifecycleExact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.QueryIndexedProjectionAdequacyExact`, `DASHI.Core.ObserverRefinementLatticeExact`, `DASHI.Core.Prelude`.
- Produces: `NegotiationStatus`, `InstrumentNature`, `LegalEffectStatus`, `ApplicabilityStatus`, `consensusOnlyBindingAdequacyDefect`, `consensusAndInstitutionalDetermineBinding`, and explicit no-promotion firewalls.

- [ ] Implement orthogonal lifecycle carriers.
- [ ] Construct two worlds with the same consensus-text surface but different binding legal effects.
- [ ] Prove `consensusOnlyBindingAdequacyDefect` and `consensusOnlyCannotDetermineBinding`.
- [ ] Join textual and institutional status using `Observer.pairObserver` and prove adequacy/restored factorisation.
- [ ] Add negative firewalls: consensus != treaty; adoption != entry into force; entry into force != every-state binding; state binding != factual applicability.
- [ ] Commit.

### Task 3: 2026 CCW/GGE LAWS source fixture

**Files:**
- Create: `DASHI/Law/SensibLawCCWLAWS2026Exact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.AttributedSourceCore`, generic lifecycle owner.
- Produces: official-source atlas, September 2026 lifecycle snapshot, source-atlas non-promotion theorem, and status firewalls.

- [ ] Encode official UN/UNODA source records for the 2026 agenda/mandate and Chair summary using `mkNoDOISource`; do not invent DOI/QID.
- [ ] Record document symbols, dates, issuing body, canonical UNODA URLs, source kind, and bounded formalisation relationship.
- [ ] Encode September 2026 as `consensusElements` + unresolved instrument nature + no newly established binding effect from the consensus-elements status alone.
- [ ] Encode existing-IHL applicability as a separate coordinate/proposition from new-instrument creation.
- [ ] Add an attributed source atlas receipt and prove it is non-promoting.
- [ ] Commit.

### Task 4: Thin counter-UAS/SensibLaw bridge

**Files:**
- Create: `DASHI/Applications/CounterUASSensibLawAuthorityBridgeExact.agda`

**Interfaces:**
- Consumes: `CounterUASDroneShieldExact`, generic lifecycle, CCW 2026 fixture.
- Produces: legal-context record and firewalls preserving domestic mitigation authority vs IHL/LAWS applicability.

- [ ] Define a small contextual record joining technical/threat state, domestic authority, and international-law applicability/lifecycle state.
- [ ] Prove/encode that domestic mitigation authority does not establish armed-conflict status, LAWS classification, or international-law applicability.
- [ ] Encode that technical autonomy/capability does not establish lawful autonomous engagement.
- [ ] Reference the September fixture without claiming every counter-UAS event falls within it.
- [ ] Commit.

### Task 5: GREEN integration and workflow

**Files:**
- Modify: `DASHI/Applications/CounterUASDroneShieldRegression.agda`
- Modify: `.github/workflows/counter-uas-droneshield.yml`

**Interfaces:**
- Consumes: Tasks 2-4.
- Produces: one focused regression root covering all new owners.

- [ ] Fill the regression constructor with the concrete lifecycle defect/repair and non-promotion witnesses.
- [ ] Add all three new files to the workflow `paths` filter while retaining `CounterUASDroneShieldRegression.agda` as the checked Agda root.
- [ ] Inspect the resulting workflow run; only claim Agda certification if the runner reports success.
- [ ] Audit changed files for `postulate`, accidental authority promotion, invented identifier metadata, and out-of-scope operational content.
- [ ] Commit final integration.

## Self-review

Coverage: lifecycle status, source attribution, September snapshot, application bridge, and focused CI all have tasks. No generic topology migration is required. No placeholder identifiers are permitted. Type names used by later tasks are fixed above and must be implemented verbatim.