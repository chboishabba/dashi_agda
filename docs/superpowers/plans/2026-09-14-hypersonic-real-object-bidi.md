# Hypersonic Real-Object Application BIDI Implementation Plan

> Execute with Superpowers TDD discipline. This plan continues the approved object-first investigation on the isolated branch.

**Goal:** Add a reusable real-engineering-object BIDI, instantiate a source-attributed hypersonic/scramjet research vehicle, and classify all twenty retained scientists without promoting engineering fit into historical participation or event cause.

**Architecture:** Thin adapter over `ScientificCapabilityCarrierBidiExact`, `ApplicationTransformationCapabilityBidiExact`, `AttributedSourceCore` and existing scientist owners. The generic adapter owns fit-strength semantics; the hypersonic owner owns engineering requirements and source atlas; Round 17 owns the all-20 incidence slice.

**Spec:** `docs/superpowers/specs/2026-09-14-hypersonic-real-object-bidi-design.md`

### Task 1 — RED contract

- Create `scripts/check_missing_deceased_round17_hypersonic_real_object.sh` first.
- Require `DASHI/Core/RealObjectApplicationBidiExact.agda` with the five fit strengths and generic firewalls.
- Require `DASHI/Culture/MissingDeceasedHypersonicAirbreathingVehicleBidiExact.agda` with subsystem taxonomy, NASA source atlas, seven strong scientist fits and rocket/scramjet thermodynamic firewalls.
- Require `DASHI/Culture/MissingDeceasedTwentyScientistRound17HypersonicObjectProgressExact.agda` with all 20 names, count 20, seven strong fits and zero historical/H2/H3 promotions.
- Require focused aggregate imports.
- Commit checker, then fetch a production owner and verify 404.

### Task 2 — Generic real-object adapter

Create `DASHI/Core/RealObjectApplicationBidiExact.agda`:

- `FitStrength = directSourceFit | engineeringTransfer | methodTransfer | analogyOnly | noFit`.
- `RealObjectRequirement` with subsystem/need, source-backed requirement and reverse transformation targets.
- `ScientistObjectFit` linking person, science owner/carrier description, requirement, fit strength, evidence and reverse leaf.
- `RealEngineeringObject` with source atlas/reference and requirement list.
- Generic firewalls: fit != participation; multiple fits != common programme; transfer != qualification; method transfer != deployed implementation; real-object fit != event cause/H2; no-fit is informative.
- Reuse `AttributedSourceCore` rather than introducing source metadata.

### Task 3 — Hypersonic canonical object

Create `DASHI/Culture/MissingDeceasedHypersonicAirbreathingVehicleBidiExact.agda`:

- source-attributed NASA rocket/scramjet/inlet engineering context;
- `HypersonicSubsystem` covering inlet/compression, isolator/SBLI, combustion/mixing, hot structure, TPS, sensing/actuation, fault-tolerant control, hardware verification, guidance/autonomy and qualification;
- explicit thermodynamic firewalls: normal inlet compression != air liquefaction; scramjet != oxidizer-carrying rocket; rocket != scramjet; staged rocket boost + scramjet cruise can coexist;
- map Yan/Fang/Zhou/Reza/McCasland/Chen/Zhang Daibing using direct/engineering/method transfer only;
- preserve source DOI/project attribution and reverse qualification leaves;
- zero historical participation/common-programme/event-cause promotion.

### Task 4 — Round 17 all-20 incidence slice

Create `DASHI/Culture/MissingDeceasedTwentyScientistRound17HypersonicObjectProgressExact.agda`:

- exactly 20 rows in canonical roster order;
- seven strong fits from Task 3;
- remaining rows explicitly `analogyOnly` or `noFit` rather than forced interfaces;
- record next engineering leaf and next historical-object-link leaf separately;
- `round17ScientificCohortCount = 20`;
- `round17StrongFitCount = 7`;
- `round17HistoricalParticipationPromotionCount = 0`;
- `round17H2PromotionCount = 0`;
- `round17H3PromotionCount = 0`;
- `round17NoFitReducesInventedInterfaceDebt = true`.

### Task 5 — Integrate and verify

- Update `MissingDeceasedCommonObjectProgrammeEverything.agda` to import the generic/hypersonic/Round17 surfaces as appropriate (generic core is imported by object owner, not necessarily aggregate).
- Fresh-fetch all new owners.
- Fetch exact branch head, PR #915 state and exact-head workflow runs.
- Report only source-written/static-contract integration unless a command/workflow receipt exists.

### Next Pareto after Round 17

- Engineering: instantiate long-duration space/fission, high-energy experimental and molecular/chemical-biology real objects using the same generic adapter.
- Investigation: search exact NPU/BIT/DICP/NUDT/AFRL programme identifiers spanning two retained scientists on the hypersonic object; fit alone contributes zero H2.
- Science: deepen Yan response curves, Fang high-temperature/material geometry, Zhou thermal cycling, Reza hot-air/fuel qualification, McCasland vehicle failure family, Chen target-specific verification corpus and Zhang Daibing vehicle-specific dynamics/control law.
