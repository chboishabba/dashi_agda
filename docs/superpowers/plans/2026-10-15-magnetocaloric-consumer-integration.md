# Magnetocaloric Consumer Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Populate all sound existing consumers of the magnetocaloric/AMR lane without introducing false physical equivalences.

**Architecture:** Add typed crosswalk modules at the SI, condensed-matter, chemistry/atomic, quantum/statistical and continuum-law boundaries. Keep the AMR device layer abstract and require evidence-bearing bridges from each lower layer.

**Tech Stack:** Agda, existing DASHI physics law and SI modules.

**Spec:** `docs/superpowers/specs/2026-10-15-magnetocaloric-consumer-integration-design.md`

## Global Constraints

- Reuse existing carriers before introducing new ones.
- Preserve source/authority boundaries and `shared carrier != shared observable` separation.
- Do not treat tesla (B) as magnetic field strength H; add A/m separately.
- Do not infer Clay NS or YM results from AMR engineering.
- No numerical material/device claim without calibration evidence.

## Review Focus

- B-vs-H dimensional confusion must be impossible at the SI type level.
- Same material state must not imply identical crystal, magnetic, electronic and thermodynamic observables.
- Atomic-shell stability must not imply magnetocaloric response without a material-identification bridge.
- A quantum Hamiltonian must not imply a calibrated partition/free-energy map without an ensemble witness.
- Continuum/NS reuse must stop at application-specific balance/transport interfaces and never promote Clay regularity.

---

### Task 1: SI magnetocaloric quantities

**Files:** modify `DASHI/Physics/Units/SI.agda`; create `DASHI/Physics/Units/MagnetocaloricSIConsumerExact.agda`; modify `DASHI/Physics/Units/Everything.agda`.

- [ ] Add exact coherent dimensions and named units for H, entropy, heat capacity, specific heat and thermal conductivity.
- [ ] Add a typed AMR calibration measurement bundle distinguishing H from B.
- [ ] Wire the consumer into the Units rollup.

### Task 2: Condensed-matter crystal/magnetic consumer

**Files:** create `DASHI/Physics/CondensedMatter/MagnetocaloricCrystalQuantumConsumerExact.agda`; modify `DASHI/Physics/CondensedMatter/Everything.agda`.

- [ ] Reuse observable-fibre and crystal-action precedent.
- [ ] Keep crystal phase, magnetic order, band energy and thermodynamic response as distinct projections.
- [ ] Add explicit promotion boundary.

### Task 3: Chemistry/atomic consumer

**Files:** create `DASHI/Physics/Chemistry/MagnetocaloricAtomicChemistryConsumerExact.agda`.

- [ ] Reuse `AtomicShellRecurrence` and `AtomicClosedShellSchurBridge` as lower-layer providers.
- [ ] Type composition/substitution/hydrogenation and material-identity transport separately from response calibration.

### Task 4: Quantum/statistical consumer

**Files:** create `DASHI/Physics/Quantum/MagnetocaloricQuantumStatMechConsumerExact.agda`.

- [ ] Expose Hamiltonian -> ensemble -> free energy -> M/S/C chain as evidence-bearing interfaces.
- [ ] Prevent model-Hamiltonian-to-device promotion.

### Task 5: Continuum / NS boundary consumer

**Files:** create `DASHI/Physics/Thermodynamics/MagnetocaloricContinuumConsumerExact.agda`.

- [ ] Connect regenerator fields to `ContinuumBalanceSystem`, `FluidDynamicsLaw`, and `DiffusionTransportLaw`.
- [ ] State explicitly that Clay NS regularity is not a dependency.

### Task 6: Reachability and terminal receipt

**Files:** create `DASHI/Physics/Thermodynamics/MagnetocaloricConsumerAtlasExact.agda`; modify `DASHI/Physics/Thermodynamics/Everything.agda`; modify `DASHI/Physics/Thermodynamics/MagnetocaloricAMRReceipt.agda` if needed.

- [ ] Import all consumer bridges into the thermodynamics rollup.
- [ ] Record which consumers are populated and the remaining physical/calibration frontier.
- [ ] Inspect branch diff/status; do not claim Agda typechecking without a compiler/status check.
