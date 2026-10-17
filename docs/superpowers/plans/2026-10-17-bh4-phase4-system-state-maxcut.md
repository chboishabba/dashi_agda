# BH4 Phase 4 System-State Max-Cut Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Move the BH4 lane from isolated exact reaction receipts to one executable open metabolic network with a canonical stoichiometric matrix, compartment/kinetic evidence coordinates, typed NOS-coupling transitions, and an attempted joint flux-balance feasibility certificate.

**Architecture:** Reuse `OpenMetabolicNetwork`, `MetabolicStoichiometricConservation`, `MetabolicOpenSystemBalance`, `BH4SystemStateExact`, `NitrogenOxideSpeciesCouplingExact`, and the existing 369/unified adapters. The new code consumes the generic Rhea/ChEBI panel certificate, constructs a finite species-by-reaction matrix where possible, keeps transport/exchange separate from internal chemistry, and reports feasibility/residuals without manufacturing kinetics, compartment measurements, disease causation, or clinical authority.

**Tech Stack:** Agda, Python 3, JSON/CSV/Markdown certificates, Rhea/ChEBI/UniProt evidence receipts.

**Spec:** `docs/biology/BH4Chemistry369RunnerIntegration.md`

## Global Constraints

- Do not use CI as the completion gate for this tranche.
- External identifiers and literature are evidence/provenance coordinates, not biological truth.
- Rhea-balanced and independently finite-formula-balanced remain distinct receipts.
- Missing quantitative parameters must remain explicit residuals; never substitute invented values.
- Internal stoichiometric reactions and environmental/compartment exchange remain distinct.
- `NO != N2O`; NONG/NANG naming provenance cannot create NOS mechanism.
- No disease/clinical promotion from network feasibility alone.

## Review Focus

- Duplicate species appearing under multiple ChEBI identifiers must not silently collapse without an explicit equivalence witness.
- Formula-incomplete/polymeric/R-group reactions must stay outside finite-matrix atom-balance promotion.
- Missing kinetic bounds must produce an `unknown` feasibility coordinate, not zero flux.
- Compartment exchange cannot be folded into internal stoichiometric columns.
- A feasible steady-state/allocator witness cannot by itself establish the Kitzerow disease mechanism.

---

### Task 1: Regression-first phase-4 contract

**Files:**
- Create: `DASHI/Biology/BH4Phase4SystemStateRegression.agda`
- Create: `scripts/check_bh4_phase4_system_state.py`

**Interfaces:**
- Consumes: current QDPR chemistry/369/runner owners.
- Produces: compile/static contract for matrix, parameter, NOS and feasibility owners.

- [ ] Write the regression imports and anti-promotion equations first.
- [ ] Verify the static checker is red because production owners do not yet exist.
- [ ] Commit.

### Task 2: Canonical panel stoichiometric matrix

**Files:**
- Create: `scripts/build_bh4_stoichiometric_matrix.py`
- Create: `DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda`

**Interfaces:**
- Consumes: `dashi.rhea-chebi-bh4-panel.v2` certificate.
- Produces: deterministic species index, reaction index, signed coefficient matrix, finite-audit subset and residual set.

- [ ] Add tests/static contract for signed coefficients and deterministic ordering.
- [ ] Implement matrix builder.
- [ ] Add Agda receipt/boundaries.
- [ ] Commit.

### Task 3: Compartment and kinetic evidence coordinates

**Files:**
- Create: `DASHI/Biology/BH4CompartmentKineticStateExact.agda`
- Create: `scripts/acquire_bh4_parameter_evidence.py`

**Interfaces:**
- Consumes: protein/reaction identities and source metadata.
- Produces: interval-valued amount/flux/kinetic/evidence coordinates with source/same-object/compartment/time/payment status.

- [ ] Specify measured, derived, bounded-literature and unresolved parameter states.
- [ ] Ensure unresolved != zero.
- [ ] Encode source/same-object/compartment/time coordinates and non-promotion boundaries.
- [ ] Commit.

### Task 4: NOS same-object coupling bridge

**Files:**
- Create: `DASHI/Biology/BH4NOSCouplingSameObjectExact.agda`

**Interfaces:**
- Consumes: `BH4CompartmentKineticStateExact`, `NitrogenOxideSpeciesCouplingExact`, existing TSC2/mTOR atlas edge.
- Produces: typed prerequisite/payment chain from BH4/BH2/redox/substrate state to NOS coupling/product species and downstream transport residual.

- [ ] Reuse existing coupling-state and NO/N2O boundaries.
- [ ] Keep protein presence/cofactor requirement distinct from measured coupling transition.
- [ ] Commit.

### Task 5: Joint open-system flux feasibility runner

**Files:**
- Create: `scripts/run_bh4_flux_feasibility.py`
- Create: `DASHI/Biology/BH4JointFluxFeasibilityExact.agda`

**Interfaces:**
- Consumes: stoichiometric matrix plus parameter/evidence manifest.
- Produces: feasibility status `feasible | infeasible | underdetermined`, explicit residuals, and a candidate `FluxBalanceWitness` only when every required coordinate is paid.

- [ ] Treat missing bounds as underdetermined, not zero.
- [ ] Keep transport/exchange separate from internal reaction columns.
- [ ] Emit JSON/CSV/Markdown receipt.
- [ ] Add Agda boundary preventing feasibility from becoming causal/disease proof.
- [ ] Commit.

### Task 6: Open-metabolic/unified integration and roots

**Files:**
- Create: `DASHI/Biology/BH4OpenMetabolicNetworkAdapterExact.agda`
- Modify: `DASHI/Biology/ExternalBiologyEverything.agda`
- Modify: `DASHI/Biology/KitzerowBH4EvidenceEverything.agda`
- Modify: `DASHI/Unified/BH4BiochemicalEverything.agda`
- Modify: `scripts/check_kitzerow_bh4_priority.py`
- Modify: `docs/biology/BH4Chemistry369RunnerIntegration.md`

**Interfaces:**
- Consumes: all Phase-4 owners.
- Produces: one discoverable receipt-gated BH4 open metabolic network integrated with the existing DASHI cross-scale facade.

- [ ] Reuse `OpenMetabolicNetwork` and `MetabolicOpenSystemBalance` explicitly.
- [ ] Wire focused roots and main regression.
- [ ] Update roadmap documentation and PR live residuals.
- [ ] Run focused static verification where possible; report any environment limitation exactly.
- [ ] Commit.
