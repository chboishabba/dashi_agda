# Atomic-Molecular-Reaction Lineage Hyperfabric Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Build a reusable proof-relevant hyperfabric that tracks atomic/nuclear identity, electron transport, molecular/bond/geometry state, reaction products/byproducts, biological incorporation and observer-relative coarse-graining, then validate it on Pb/Ca mimicry, BH4 metabolism and prebiotic carbon chemistry.

**Architecture:** Reuse the existing 369 atomic generator, molecular assembly boundary, chemistry TransitionKernel, admissible reaction bridge, protein/DNA 3-D adapter, ionic mimicry, consumer-relative coarse-graining and Levin/prebiotic owners. The new core adds lineage/transport receipts only where the repo currently has a seam: persistent atom/electron identity through molecule/reaction/biology and explicit residual loss under coarse observation.

**Tech Stack:** Agda; DASHI 369 chemistry, molecular, biology, Levin and core hyperfabric machinery; GitHub static validation.

**Spec:** User-approved conversation design: every atom descends from 369 atomic identity; atoms assemble into molecule/bond/geometry witnesses; reactions explicitly transport atoms/electrons and bond changes; products/byproducts retain lineage; biological/protein/DNA incorporation consumes molecular lineage; coarse observers retain residuals. Pb/Ca, BH4 and prebiotic carbon are required regressions.

## Global Constraints

- Do not redefine the 369 atomics, TransitionKernel, MolecularAssemblyBoundary, ionic mimicry, Levin, or prebiotic/carbon owners.
- Nuclear identity conservation is a chemistry-level invariant, not a nuclear-reaction theorem.
- Electron identity/transfer and charge conservation are separate obligations.
- A reaction label or stoichiometric balance does not by itself prove electron transport, geometry, kinetics, or biological effect.
- Biological incorporation does not identify a molecule with a protein/DNA/cell state.
- Coarse-observer equality never implies fine-state identity without a factorisation/separation receipt.
- Attribution and empirical promotion remain fail-closed.

## Review Focus

1. Electron bookkeeping must not be silently derived from charge balance.
2. Pb/Ca substitution must preserve ion identity distinction while allowing target-relative mimicry.
3. BH4 must be a shared literal species across synthesis/recycling/consumer reactions; shared use alone must not prove flux allocation.
4. Prebiotic carbon suitability must not imply abiogenesis or inevitability.
5. Protein/DNA/biological incorporation must preserve upstream material lineage without claiming unique conformation or phenotype.

---

### Task 1: RED validation contract

**Files:**
- Create: `DASHI/Chemistry/AtomicMolecularReactionLineageMaxCutValidation.agda`
- Create: `scripts/check_atomic_molecular_reaction_lineage_maxcut.py`

**Interfaces:**
- Consumes: expected module names and boundary projections from Tasks 2-6.
- Produces: static/max-cut contract that is initially red because owners do not yet exist.

### Task 2: Generic atomic/electron/molecular/reaction lineage core

**Files:**
- Create: `DASHI/Chemistry/AtomicMolecularReactionLineageHyperfabricExact.agda`
- Create: `DASHI/Chemistry/ElectronBondTransportExact.agda`

**Interfaces:**
- Consumes: `AtomicPeriodicTable369GenerativeExact`, `AtomicPeriodicTable369ChemistryHyperfibreBridgeExact`, `MolecularAssemblyBoundary`, `TransitionKernel`, `AdmissibleReactionTransitionBridgeExact`, `ConsumerRelativeCoarseGrainingBidiExact`.
- Produces: typed `AtomicLineage`, `ElectronLineage`, `MolecularLineageState`, `ReactionLineageTransport`, bond-change/electron-transfer receipts, and non-collapse boundaries.

### Task 3: Biology/protein/DNA incorporation adapter

**Files:**
- Create: `DASHI/Biology/AtomicMolecularBiologicalIncorporationHyperfabricExact.agda`

**Interfaces:**
- Consumes: Task 2 core plus `AtomicPeriodicTable369ProteinDNA3DAdapterExact`, cell-state and Levin/problem-space owners.
- Produces: typed incorporation receipt from molecular/reaction lineage into protein/DNA/cell carrier while retaining upstream provenance and residuals.

### Task 4: Pb/Ca mimicry regression

**Files:**
- Create: `DASHI/Biology/LeadCalciumAtomicLineageRegressionExact.agda`

**Interfaces:**
- Consumes: Task 2/3 plus `IonicMimicryGeometryExact`.
- Produces: same-charge/local-recognition collision with distinct 369 atomic identities and target-relative downstream divergence.

### Task 5: BH4 reaction/electron-lineage regression

**Files:**
- Create: `DASHI/Biology/KitzerowBH4LineageRegressionExact.agda`

**Interfaces:**
- Consumes: Task 2/3 and existing Kitzerow BH4 reaction/synthesis/cascade owners.
- Produces: explicit shared-BH4/electron-redox lineage surface; blocks `sharedSpecies => fluxReallocation` and connects literal chemistry to cascade consumers.

### Task 6: Carbon/prebiotic/Levin regression and rollup

**Files:**
- Create: `DASHI/Biology/PrebioticCarbonAtomicLineageRegressionExact.agda`
- Create: `DASHI/Chemistry/AtomicMolecularReactionLineageEverything.agda`

**Interfaces:**
- Consumes: Task 2/3, `CarbonChemicalSuitabilityLifeBoundaryExact`, `PrebioticChemistryLifeInevitabilityBidiExact`, Levin problem-space/autonomy owners.
- Produces: carbon molecular/reaction lineage into maintained nonequilibrium/agentic-material stages without abiogenesis/inevitability promotion; focused rollup.

### Task 7: Final max-cut validation

**Files:**
- Modify: `DASHI/Chemistry/AtomicMolecularReactionLineageMaxCutValidation.agda`
- Modify: `scripts/check_atomic_molecular_reaction_lineage_maxcut.py`

**Verification:**
- Require all owners and exact imports/field names.
- Require non-collapse theorems/boundaries for nuclear-vs-electron, stoichiometry-vs-electron transport, mimicry-vs-identity, shared-BH4-vs-flux, carbon-suitability-vs-life and coarse-observer-vs-fine identity.
- Agda kernel-green must be reported only if an actual compiler run is available; otherwise report source/static verification boundary explicitly.
