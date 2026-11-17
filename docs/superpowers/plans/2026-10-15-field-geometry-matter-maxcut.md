# Field–Geometry–Matter Max-Cut Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement a thin same-object conservation/control/promotion spine over existing DASHI physics owners, with concrete quantum-material, thermodynamic, plasma/MHD, anomalous-force, quantum-stress-energy and FTL consumers.

**Architecture:** Reuse existing `ConsumerDescent`, attribution, GR stress-energy, Casimir, MAGNOTHERM, FRC, Rocketdyne and exotic-gravity owners. Add only mechanism-neutral conservation/control records, domain adapters and fail-closed promotion/obligation owners; no universal `PhysicalSystem` ontology.

**Tech Stack:** Agda, shell/static regression checks, GitHub Actions where available.

**Spec:** `docs/superpowers/specs/2026-10-15-field-geometry-matter-maxcut-design.md`

## Global Constraints

- External sources pay only source-bounded facts; DASHI cross-domain synthesis remains DASHI-owned.
- Cross-pollination may transfer theorem shape/experimental-design grammar, never mechanism, material identity, calibration, empirical values, causal authority, gravitational interpretation or historical intent.
- No residual directly promotes to antigravity/reactionless drive/new physics.
- Energy-condition violation is distinct from quantum admissibility and engineering realizability.
- Quantum/state teleportation, analogue spacetime and superluminal-looking observables do not promote to FTL signalling/matter transport.
- No kernel-green/physical-validation claim without exact-head receipts.

## Review Focus

- Missing ledger channels must not be silently treated as zero.
- Same coarse force/temperature/entropy observation with different nuisance state must remain consumer-distinguishable.
- Same Lorentz-force form must not collapse fusion nozzle and hypersonic-flow mechanisms/efficiencies.
- QFT-negative-energy/Casimir objects must not skip quantum-admissibility/scaling/backreaction stages.
- FTL hierarchy must reject teleportation/analogue/superluminal-peak shortcuts.

---

### Task 1: Same-object conservation/control kernel

**Files:**
- Create: `DASHI/Physics/Foundations/SameObjectConservationLedgerExact.agda`
- Create: `DASHI/Physics/Foundations/ControlledPhysicalTransitionExact.agda`
- Test: `DASHI/Physics/Foundations/FieldGeometryMatterKernelValidation.agda`

**Interfaces:**
- Consumes: existing core consumer/refinement machinery.
- Produces: `SameObjectInterval`, `AdmittedChannelSet`, `EnergyLedger`, `MomentumLedger`, `EntropyLedger`, `ChargeLedger`, `ResidualLedger`, `ControlledPhysicalTransition`.

- [ ] Write validation first requiring separate ledgers, explicit admitted-channel sets and a finite bookkeeping witness.
- [ ] Confirm production owners are absent on the branch before creation.
- [ ] Implement minimal exact records and residual definitions without asserting domain physics.
- [ ] Add a finite collision witness showing coarse observation can erase a consumer-relevant channel.
- [ ] Static-inspect validation imports and absence of holes/postulates.
- [ ] Commit.

### Task 2: Physical residual promotion boundary

**Files:**
- Create: `DASHI/Physics/Foundations/PhysicalResidualPromotionExact.agda`
- Extend: `DASHI/Physics/Foundations/FieldGeometryMatterKernelValidation.agda`

**Interfaces:**
- Consumes: `ResidualLedger` from Task 1.
- Produces: nuisance completeness, replication/scaling/apparatus-change evidence records, `AnomalousMomentumCandidate`, and explicit non-promotion boundaries.

- [ ] Add failing validation contracts for residual != antigravity/reactionless/new-physics.
- [ ] Implement typed promotion ladder requiring nuisance closure plus repetition/scaling/apparatus-change/independent replication for stronger classes.
- [ ] Add empty-type/non-constructor boundaries preventing direct promotion.
- [ ] Static-inspect and commit.

### Task 3: Four mechanism-neutral physical adapters

**Files:**
- Create: `DASHI/Physics/Foundations/FieldGeometryMatterConsumersExact.agda`
- Create: `DASHI/Physics/Foundations/FieldGeometryMatterConsumersValidation.agda`

**Interfaces:**
- Consumes: Tasks 1-2 plus existing twistronics/MAGNOTHERM/FRC/Rocketdyne/exotic-gravity owners.
- Produces: four adapter records: quantum-material entropy, programmable-thermodynamic cycle, EM body-force/momentum-flow, precision-thrust residual.

- [ ] Validation first pins four distinct adapters and cross-domain non-identity fields.
- [ ] Quantum-material adapter exposes geometry/control -> state/entropy coordinates without claiming valley/C3 physical identification or caloric utility.
- [ ] MAGNOTHERM adapter exposes cycle entropy/work/heat/loss while retaining source/device ownership.
- [ ] Plasma/MHD adapter exposes `rhoE + J×B`/field-work/boundary-momentum interfaces while separating confinement/nozzle/hypersonic applications.
- [ ] Precision-thrust adapter carries nuisance fibre including thermal, pressure, outgassing, vibration, supports/cables, electrostatic, magnetic, radiation, convection, facility and sensor channels.
- [ ] Add Rocketdyne qualification grammar as reusable shape only, with numeric/causal transfer forbidden.
- [ ] Static-inspect and commit.

### Task 4: Quantum stress-energy engineering bridge

**Files:**
- Create: `DASHI/Physics/Foundations/QuantumStressEnergyEngineeringBridgeExact.agda`
- Create: `DASHI/Physics/Foundations/QuantumStressEnergyEngineeringValidation.agda`

**Interfaces:**
- Consumes: existing Casimir/quantum-vacuum stack, GR stress-energy interfaces and energy-condition owners.
- Produces: staged quantum-stress-energy promotion ladder and GR backreaction obligation record.

- [ ] Validation first requires distinct source-backed Casimir configuration, renormalized stress model, energy-condition status, quantum-admissibility/QEI status, controllability/scaling, and backreaction.
- [ ] Implement the ordered ladder with no skip constructors.
- [ ] Encode `energy-condition violation != unphysical` and `!= engineering realizability`.
- [ ] Add initial Casimir-to-metric-perturbation obligation surface without claiming magnitude significance.
- [ ] Static-inspect and commit.

### Task 5: Causal transport / FTL / sci-fi consumer atlas

**Files:**
- Create: `DASHI/Physics/Foundations/CausalTransportFTLObligationsExact.agda`
- Create: `DASHI/Physics/Foundations/CausalTransportFTLValidation.agda`

**Interfaces:**
- Consumes: Tasks 2 and 4 plus existing wormhole/QET non-promotion owners.
- Produces: FTL0-FTL5 obligation hierarchy, teleportation/analogue/warp/wormhole boundaries, and sci-fi candidate-consumer classification.

- [ ] Validation first pins distinctions among phase/group/peak/front velocity, state/gate/QET teleportation, analogue spacetime, wormhole, warp metric and causal superluminal transport.
- [ ] Implement `CausalSuperluminalTransport` strongest record with endpoint timing/light-cone, metric/causal receipt, source/stress-energy when applicable, chronology and replication fields.
- [ ] Add warp/wormhole obligation records for metric/topology, stress-energy, energy-condition/quantum status, tidal/stability/backreaction and chronology.
- [ ] Add candidate-consumer tags for replicator, transporter, tractor beam, force field, inertial damper, artificial gravity, holodeck, self-healing spacecraft, stargate, warp drive and reactionless drive; all authority/promotion defaults false.
- [ ] Static-inspect and commit.

### Task 6: Integration, attribution regression and terminal max-cut

**Files:**
- Create: `DASHI/Physics/Foundations/FieldGeometryMatterAttributionRegression.agda`
- Create: `DASHI/Physics/Foundations/FieldGeometryMatterTerminalMaxCutExact.agda`
- Modify: `DASHI/Physics/Foundations/Everything.agda`
- Create: `scripts/check_field_geometry_matter_maxcut.sh`

**Interfaces:**
- Consumes: Tasks 1-5.
- Produces: rollup, attribution firewall regression, explicit paid/open frontier, focused checker.

- [ ] Add attribution regression: external source evidence cannot become DASHI generic theorem ownership; sci-fi/history/company claims cannot pay physical promotion.
- [ ] Add terminal owner classifying paid generic structure versus open same-object physical leaves: literal MATBG valley/BM/QTM/entropy weld; generalized caloric realization; same-run plasma/MHD momentum closure; precision-thrust nuisance closure/replication; quantum stress-energy magnitude/scaling/backreaction; warp/wormhole physical source; causal FTL transport.
- [ ] Wire into Foundations rollup without changing unrelated domain authority.
- [ ] Add focused shell checker scanning new files for holes/postulates/unsafe options and invoking Agda when available.
- [ ] Run/inspect available exact-head verification; record no kernel-green claim if unavailable.
- [ ] Open draft PR summarizing source-written status, attribution boundaries and exact remaining frontier.
