# Magnetocaloric Consumer Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Populate all sound existing consumers of the magnetocaloric/AMR lane without introducing false physical equivalences.

**Architecture:** Add typed crosswalk modules at the SI, electromagnetism, condensed-matter, chemistry/atomic, quantum/statistical, continuum-law and magnetostructural boundaries. Keep the AMR device layer abstract and require evidence-bearing bridges from each lower layer.

**Tech Stack:** Agda, existing DASHI physics law and SI modules.

**Spec:** `docs/superpowers/specs/2026-10-15-magnetocaloric-consumer-integration-design.md`

## Global Constraints

- Reuse existing carriers before introducing new ones.
- Preserve source/authority boundaries and `shared carrier != shared observable` separation.
- Do not treat tesla (B) as magnetic field strength H; use A/m separately.
- Do not infer Clay NS or YM results from AMR engineering.
- No numerical material/device claim without calibration evidence.
- Keep BIPM-owned canonical `SI.agda` unchanged when a domain-specific derived dimension can live in the consumer.
- Preserve canonical DASHI attribution: author/title/publication/DOI/source kind/formalisation relationship; primaryness is claim-relative; access carrier != authorship/authority; citation != proof; vendor/planned evidence cannot pay independent same-device calibration.

## Review Focus

- B-vs-H dimensional confusion must be impossible at the SI type level.
- Same material state must not imply identical crystal, magnetic, electronic and thermodynamic observables.
- Atomic-shell stability must not imply magnetocaloric response without a material-identification bridge.
- A quantum Hamiltonian must not imply a calibrated partition/free-energy map without an ensemble witness.
- Continuum/NS reuse must stop at application-specific balance/transport interfaces and never promote Clay regularity.
- Source identity, access transport, source claim, DASHI reconstruction and theorem/device authority must remain separate.

---

### Task 1: SI magnetocaloric quantities

**Files:** create `DASHI/Physics/Units/MagnetocaloricSIConsumerExact.agda`; modify `DASHI/Physics/Units/Everything.agda`.

**Ruling:** Derived AMR-specific dimensions remain in the consumer rather than modifying canonical BIPM `SI.agda`; this preserves the source-owned SI core while still using its `Dimension`, `Unit`, `Quantity`, and `Measurement` carriers.

- [x] Add exact coherent dimensions and named units for H, entropy, heat capacity, specific heat and thermal conductivity.
- [x] Add a typed AMR calibration measurement bundle distinguishing H from B.
- [x] Bind measurements to the magnetocaloric material carrier through explicit identification/traceability obligations.
- [x] Wire the consumer into the Units rollup.

### Task 2: Electromagnetic field consumer

**Files:** create `DASHI/Physics/Electromagnetism/MagnetocaloricFieldConsumerExact.agda`; modify `DASHI/Physics/Electromagnetism/Everything.agda`.

- [x] Reuse the existing application-facing U(1) field socket.
- [x] Require B/H constitutive convention, geometry, field-work and validation evidence.
- [x] Preserve the existing non-abelian-YM/application-electromagnetism separation.

### Task 3: Condensed-matter crystal/magnetic consumer

**Files:** create `DASHI/Physics/CondensedMatter/MagnetocaloricCrystalQuantumConsumerExact.agda`; modify `DASHI/Physics/CondensedMatter/Everything.agda`.

- [x] Reuse observable-fibre and native `GroupAction` crystal-symmetry precedent.
- [x] Keep crystal phase, magnetic order, band energy and thermodynamic response as distinct projections.
- [x] Add explicit physical-identification and promotion boundaries.

### Task 4: Chemistry/atomic/protection consumer

**Files:** create `DASHI/Physics/Chemistry/MagnetocaloricAtomicChemistryConsumerExact.agda`.

- [x] Reuse `AtomicShellRecurrence`, force-sector separation and Schur closed-shell precedent.
- [x] Type composition/substitution/hydrogenation and material identity separately from response calibration.
- [x] Type coating/inhibitor/transfer-fluid chemistry and qualified corrosion/interface evidence.

### Task 5: Quantum/statistical consumer

**Files:** create `DASHI/Physics/Quantum/MagnetocaloricQuantumStatMechConsumerExact.agda`.

- [x] Expose Hamiltonian -> ensemble -> free energy -> M/S/C chain as evidence-bearing interfaces.
- [x] Prevent model-Hamiltonian-to-device and finite-model-to-bulk promotion.

### Task 6: Continuum / NS boundary consumer

**Files:** create `DASHI/Physics/Thermodynamics/MagnetocaloricContinuumConsumerExact.agda`.

- [x] Connect regenerator fields to `ContinuumBalanceSystem`, `FluidDynamicsLaw`, and `DiffusionTransportLaw`.
- [x] State explicitly that Clay NS regularity is not a dependency.

### Task 7: Magnetostructural mechanics consumer

**Files:** create `DASHI/Physics/Thermodynamics/MagnetocaloricMagnetostructuralConsumerExact.agda`.

- [x] Reuse `ElasticityLaw` for deformation/strain/stress/stored-energy structure.
- [x] Keep magnetostriction and coating-interface mechanics calibration explicit.
- [x] Feed cyclic strain only into qualified degradation/integrity projections, never lifetime claims.

### Task 8: Reachability and terminal receipt

**Files:** create `DASHI/Physics/Thermodynamics/MagnetocaloricConsumerAtlasExact.agda`; modify `DASHI/Physics/Thermodynamics/Everything.agda`; modify `DASHI/Physics/Thermodynamics/MagnetocaloricAMRReceipt.agda`.

**Rulings:**
- Existing protected-system energy accounting already owns rotational/recovered work; no duplicate mechanical-work consumer was introduced.
- Existing continuum/Fourier surfaces already own heat transport; no duplicate heat-exchanger abstraction was introduced.
- Search found biology-specific control cores but no generic engineering-control owner suitable for AMR; importing an agency/biology controller would be an unsound coupling, so cycle synchronisation remains owned by the AMR lane.
- NS and YM are structural precedents only: NS via generic continuum/reduction machinery; YM via generic operator-reduction/symmetry factoring and the existing U(1) separation boundary.

- [x] Import all sound consumer bridges into the thermodynamics rollup.
- [x] Record populated consumers and rejected/covered candidate consumers in the atlas.
- [x] Record the remaining physical/calibration frontier in the terminal receipt.
- [x] Inspect branch diff/status. Branch is current with `master`; CodeRabbit status is successful. No Agda compiler/status check is available, so no typecheck-success claim is made.

### Task 9: Attribution firewall and empirical payment max-cut

**Files:** create `DASHI/Physics/Thermodynamics/MagnothermAttributedEvidenceExact.agda`, `MagnothermAttributionValidation.agda`, `MagnetocaloricEvidenceMaxCutExact.agda`, `MagnetocaloricEvidenceMaxCutValidation.agda`; modify `MagnothermSourceBoundary.agda`, `MagnetocaloricConsumerAtlasExact.agda`, `MagnetocaloricAMRReceipt.agda`, and `Everything.agda`.

**Rulings:**
- Replace the thin local source abstraction at the domain boundary with canonical `DASHI.Core.AttributedSourceCore` ownership rather than maintaining parallel attribution semantics.
- Treat ACS/PMC/Aalto access locations as transport/provenance carriers for the same paper, not new authors or independent scientific authority.
- The peer-reviewed six-week continued-operation result is a paid bounded aging observation. The paper's three-month microchannel result is paid only as preliminary. Its months-to-years experiment is explicitly future work and remains unpaid as lifetime evidence.
- Current MAGNOTHERM 30% work-recovery, STELLAR 5 T target, 125 kW+ module, and 250 kW+ two-module statements are primary for what the vendor claims, but remain vendor/development evidence only.
- Same-device COP/capacity, constitutive M/S/c_H response, field map, hydraulics, heat transfer, timing/control and long-duration aging remain hard acquisition/calibration frontiers.
- TDD regression modules were committed before their implementation owners. This session has no Agda compiler, so the RED/GREEN code ordering is recorded but executable typecheck payment remains explicitly unavailable.

- [x] Reuse `AttributedSourceCore` with full author/title/publication/DOI/source-kind/formalisation metadata.
- [x] Separate publisher/repository/index access carriers from authorship and authority.
- [x] Encode claim-relative primaryness, same-object status, preliminary/planned/vendor roles and claim ceilings.
- [x] Encode six-week, preliminary three-month, long-term-plan, 30%, 5 T, 125 kW+ and 250 kW+ payment rows.
- [x] Build a terminal empirical max-cut atlas covering material, quantum, field, hydraulic, thermal, timing, COP/capacity, NS and YM obligations.
- [x] Wire attribution/max-cut validation and receipts into the thermodynamics spine.
- [ ] Re-run current branch/PR/status verification after these commits; do not claim Agda typechecking without a compiler receipt.
