# Twenty-Scientist Science Capability BIDI Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a repo-native BIDI object that carries all 20 scientists' source-backed science kernels into intended and bounded possible applications, while compiling application requests back into exact proof/custody obligations.

**Architecture:** Add one roster-specific adapter over existing `ScientificCapabilityCarrier`, `ApplicationTransformation`, `CapabilitySynthesis`, and factorisation machinery. Keep per-person fibres independent, combine them only through a system-level capability-design surface, and encode hard false boundaries against historical-programme/event promotion.

**Tech Stack:** Agda; shell static-contract checks; existing DASHI Core/Culture capability machinery.

**Spec:** `docs/superpowers/specs/2026-09-12-twenty-scientist-science-capability-bidi-design.md`

## Global Constraints

- Reuse existing capability/application/factorisation machinery; no new planner.
- Exactly 20 retained scientists: 11 U.S. + 9 Chinese.
- Intended application and possible application are differently typed claims.
- Possible application never promotes historical deployment, common programme, targeting, disappearance cause, or homicide.
- Amy and Chavez remain attribution/identity-gated where the repo says they are gated.
- Static source checks are not Agda/kernel certification.

---

### Task 1: RED static contract

**Files:**
- Create: `scripts/check_missing_deceased_twenty_scientist_science_capability_bidi.sh`

**Interfaces:**
- Consumes: design spec and existing Round-6 roster names.
- Produces: a failing contract requiring `MissingDeceasedTwentyScientistScienceCapabilityBidiExact.agda` and its aggregate import.

- [ ] **Step 1: Write the failing shell contract**

Require `twentyScientistScienceFibres`, `twentyScientistScienceFibreCount = 20`, `integratedTwentyScientistCapability`, the seven named false firewalls, all 20 person names, and the aggregate import.

- [ ] **Step 2: Verify RED**

Use GitHub file lookup for `DASHI/Culture/MissingDeceasedTwentyScientistScienceCapabilityBidiExact.agda` and confirm 404 before production creation. If an executable checkout becomes available, run `bash scripts/check_missing_deceased_twenty_scientist_science_capability_bidi.sh` and expect failure on the missing owner.

- [ ] **Step 3: Commit the RED contract**

Commit message: `test: require twenty-scientist science capability BIDI`.

---

### Task 2: Per-scientist BIDI fibres

**Files:**
- Create: `DASHI/Culture/MissingDeceasedTwentyScientistScienceCapabilityBidiExact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.ScientificCapabilityCarrierBidiExact`, `DASHI.Core.ApplicationTransformationCapabilityBidiExact`, `DASHI.Core.CapabilitySynthesisHypergraphExact`, `DASHI.Core.QueryFactorisationSufficiency`, `MissingDeceasedTwentyScientistRound6ScienceSuccessionExact`.
- Produces: `ScientistTechnologyFibre`, `ApplicationClaimStrength`, 20 named fibres, `twentyScientistScienceFibres`.

- [ ] **Step 1: Define application-strength and reverse-obligation types**

Create `ApplicationClaimStrength` with `sourceBackedIntended`, `documentedEngineeringInterface`, `crossDomainCandidate`, `speculativeOnly`. Define `ApplicationUse` and `BidiReverseObligation` records carrying application text, source/boundary text, transformation coordinates and acquisition/proof leaves.

- [ ] **Step 2: Define `ScientistTechnologyFibre`**

Fields: person, science kernel/object/identifier, capability carrier, intended application, optional/bounded possible application expressed as an `ApplicationUse`, science proof leaf, custody leaf, reverse obligations, and attribution boundary text.

- [ ] **Step 3: Instantiate all 20 fibres**

Use the science objects and identifiers fixed in Round 6. Do not invent person possession, application deployment, or same-programme receipts.

- [ ] **Step 4: Add roster invariant**

Define `twentyScientistScienceFibres : List ScientistTechnologyFibre` and `twentyScientistScienceFibreCount : Nat; ... = 20`.

- [ ] **Step 5: Commit per-person fibres**

Commit message: `feat: add twenty-scientist science capability fibres`.

---

### Task 3: Integrated BIDI capability surface

**Files:**
- Modify: `DASHI/Culture/MissingDeceasedTwentyScientistScienceCapabilityBidiExact.agda`

**Interfaces:**
- Consumes: all 20 fibres plus existing `CapabilitySynthesis`/`ApplicationTransformation` coordinates.
- Produces: `IntegratedScienceCapabilityBidi`, `integratedTwentyScientistCapability`, subsystem-role assignments, reverse application obligations.

- [ ] **Step 1: Define integrated subsystem roles**

Use roles for modelling/inference, power/control, sensing/diagnostics, materials/extreme-environment, autonomy/guidance, life-science sensing, environmental prediction, security/governance, and flow actuation.

- [ ] **Step 2: Define the integrated object**

The integrated object carries all 20 fibres, existing documented/cross-domain synthesis references, intended benign system-level usage, and reverse obligations. It is an abstract research/engineering platform, not an operational weapon design.

- [ ] **Step 3: Add reverse BIDI compiler surface**

Given an application class/role, expose required `TransformationCoordinate`/carrier/custody targets such as geometry, calibration, operating window, validation corpus, algorithm implementation, qualification, process window and handover.

- [ ] **Step 4: Add hard firewalls**

Set exactly:
`possibleApplicationImpliesHistoricalDeployment = false`,
`technicalCompatibilityImpliesSameProgramme = false`,
`integratedCapabilityImpliesRosterCollaboration = false`,
`scienceCarrierImpliesPersonPossession = false`,
`institutionContinuityImpliesExactCapabilityTransfer = false`,
`applicationCandidateImpliesEventCause = false`,
`allTwentyFibresPresentImpliesOneHistoricalSystem = false`.

- [ ] **Step 5: Commit integrated surface**

Commit message: `feat: compose twenty-scientist integrated capability BIDI`.

---

### Task 4: Aggregate wiring and verification

**Files:**
- Modify: `DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda`
- Test: `scripts/check_missing_deceased_twenty_scientist_science_capability_bidi.sh`

**Interfaces:**
- Consumes: completed owner.
- Produces: normal inspection/import surface for the round-robin programme.

- [ ] **Step 1: Import the new owner in the round-robin aggregate**

Add `import DASHI.Culture.MissingDeceasedTwentyScientistScienceCapabilityBidiExact`.

- [ ] **Step 2: Verify source-level contract**

Fetch the new owner and aggregate at the exact branch head and confirm required literals are present. If a runnable checkout exists, run the focused shell checker.

- [ ] **Step 3: Check exact-head workflows**

Query workflow runs for the final SHA. Do not claim Agda/kernel success unless a fresh exact-head run or local Agda invocation proves it.

- [ ] **Step 4: Commit aggregate wiring**

Commit message: `chore: wire twenty-scientist science capability BIDI`.

---

### Task 5: Next executable-science tranche

**Files:**
- No production file required in this task; emit the next Pareto frontier from the BIDI reverse obligations.

**Interfaces:**
- Consumes: per-scientist science proof leaves.
- Produces: ranked next implementation targets for domain-specific executable witnesses.

- [ ] **Step 1: Rank by reusable proof machinery and cross-fibre value**

Prefer science leaves that can be implemented with existing repo machinery and reused by the integrated object: Loureiro finite Hermite/KREHM witness, McCasland finite Gramian-placement witness, Zhang Xiaoxin finite forecast pipeline, Fang inverse-design finite witness, Zhou SI structure-property witness, Maiwald finite action-spectrum carrier.

- [ ] **Step 2: Keep all twenty live**

Even when deeper work focuses on the highest-alpha executable witnesses, preserve one explicit science and one custody reverse target for every scientist.
