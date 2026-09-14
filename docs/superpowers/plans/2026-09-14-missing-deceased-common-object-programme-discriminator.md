# Missing/Deceased Common Object / Programme Discriminator Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build an object-first, falsifiable H0/H1/H2/H3 discriminator above the existing twenty-scientist science/custody BIDI and seed it with the strongest current candidate object/programme classes and cross-person evidence search.

**Architecture:** Reuse the existing science capability BIDI, UAP adversarial claim discriminator, geography discriminator, role-capability fibre and attribution/same-object machinery. Add one generic owner for programmes, objects, required capabilities, person-capability receipts, literal cross-person receipts, typed event chronology and hypothesis discrimination. Add a focused static contract first, then an initial source-attributed investigation fixture and aggregate wiring.

**Tech Stack:** Agda, repo-native DASHI evidence/provenance types, shell static contracts, GitHub source acquisition.

**Spec:** `docs/superpowers/specs/2026-09-14-missing-deceased-common-object-programme-discriminator-design.md`

## Global Constraints

- Capability fit does not pay programme identity.
- Temporal clustering does not pay coordination.
- Programme identity does not pay targeting.
- Geography and technical adjacency do not pay common cause/programme.
- H3 requires operational evidence.
- Programme/object membership requires literal same-object/cross-person receipts.
- Do not claim shell/Agda GREEN without an executed receipt.

---

### Task 1: Focused RED contract

**Files:**
- Create: `scripts/check_missing_deceased_common_object_programme_discriminator.sh`

**Interfaces:**
- Consumes: none.
- Produces: static requirements for the new owner, first investigation fixture and aggregate import.

- [ ] Write a shell contract requiring `HypothesisClass`, `CandidateProgramme`, `CandidateObject`, `CrossPersonProgrammeReceipt`, `EventChronologyReceipt`, all nine firewalls, four initial candidate classes, and the focused aggregate import.
- [ ] Commit the contract.
- [ ] Fetch `DASHI/Culture/MissingDeceasedCommonObjectProgrammeDiscriminatorExact.agda` on the branch and verify 404 as the structural RED checkpoint.

### Task 2: Generic object/programme discriminator

**Files:**
- Create: `DASHI/Culture/MissingDeceasedCommonObjectProgrammeDiscriminatorExact.agda`

**Interfaces:**
- Consumes: `MissingDeceasedTwentyScientistScienceCapabilityBidiExact`, `MissingDeceasedUAPAdversarialClaimDiscriminatorExact`, `MissingDeceasedSouthwestGeographyDiscriminatorExact`.
- Produces: `HypothesisClass`, `CandidateProgramme`, `CandidateObject`, `RequiredCapability`, `PersonCapabilityReceipt`, `CrossPersonProgrammeReceipt`, `EventClass`, `EventChronologyReceipt`, `HypothesisDiscriminationReceipt`.

- [ ] Implement H0/H1/H2/H3.
- [ ] Implement the programme/object/capability/evidence records.
- [ ] Add candidate-score tuple coordinates without collapsing to one scalar.
- [ ] Add four initial candidate programme/object classes.
- [ ] Add all nine firewalls from the spec.
- [ ] Commit.

### Task 3: Typed event-time concentration surface

**Files:**
- Create: `DASHI/Culture/MissingDeceasedEventTimeConcentrationExact.agda`

**Interfaces:**
- Consumes: event classes from Task 2.
- Produces: exact/range dates, event-type grouping, lag coordinates and a fail-closed population-comparison status.

- [ ] Encode event-type distinctions for disappearance, death, homicide/accident/illness where source-backed, retirement/separation, stale surface, posthumous publication and role transition.
- [ ] Encode calendar-proximity and publication/work-date firewalls.
- [ ] Keep population-level significance unpaid until a sourced comparison population exists.
- [ ] Commit.

### Task 4: First object-first investigation fixture

**Files:**
- Create: `DASHI/Culture/MissingDeceasedCommonObjectProgrammeInvestigationExact.agda`

**Interfaces:**
- Consumes: Task 2 generic discriminator and current source-backed science/custody receipts.
- Produces: source-attributed search states for candidate programmes/objects and literal cross-person evidence.

- [ ] Search for exact programme/contract/grant/facility/work-package identifiers naming two or more relevant scientists/components.
- [ ] Record positive literal receipts separately from thematic/capability-only adjacency.
- [ ] Record search residuals as residuals, not absence.
- [ ] Include ordinary-engineering negative controls.
- [ ] Assign current H0/H1/H2/H3 discrimination status without promoting H3 absent operational evidence.
- [ ] Commit.

### Task 5: Focused aggregate and verification

**Files:**
- Create: `DASHI/Culture/MissingDeceasedCommonObjectProgrammeEverything.agda`
- Modify: relevant broader culture aggregate only if an existing narrow import point is obvious.

**Interfaces:**
- Consumes: Tasks 2–4.
- Produces: one discoverable investigation surface.

- [ ] Add the focused aggregate.
- [ ] Re-fetch the owner, event-time surface, investigation fixture and aggregate from the exact branch.
- [ ] Inspect exact-head PR/workflow state.
- [ ] Report source-written status only unless an executed shell/Agda receipt exists.
