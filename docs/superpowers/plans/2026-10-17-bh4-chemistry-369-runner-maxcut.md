# BH4 Chemistry / 369 / Runner Max-Cut Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Carry PR #1159 from exact external protein identity into literal biochemical reaction objects, stoichiometric execution, 369/coarse-fine transport, BH4 system-state receipts, and the existing unified atoms-to-cells simulator facade.

**Architecture:** Reuse the repo's `MolecularAssemblyBoundary`, `MolecularStoichiometricConservation`, `AtomicGenerationPipelineExact`, 369 level-transport machinery, `BH4SystemStateExact`, and `CrossScaleMatterPhysics`. Add bounded adapters and a runner; do not claim first-principles chemistry, kinetics, disease causation, or atom-to-cell closure.

**Tech Stack:** Agda, Python 3 stdlib, Rhea, ChEBI, UniProt, existing DASHI receipt/provenance machinery.

**Spec:** `docs/biology/ExternalBiologyKnowledgeAcquisition.md` plus PR #1159 BH4 system owners.

## Global Constraints

- External identifiers/data remain provenance/evidence, not theorem authority.
- Gene, protein, sequence, molecule, reaction, state, and phenotype identities remain distinct.
- 369 is refinement/observer/address machinery; chemistry is not declared literally 3-6-9.
- Reaction identity/stoichiometry does not manufacture kinetics, flux, compartment state, or disease mechanism.
- Existing atomics explicitly retain open Hamiltonian/quantitative-chemistry obligations.
- No CI work is required for this max-cut.

## Review Focus

- Rhea directionality: preserve generic vs directed reaction IDs and UniProt's stated physiological direction.
- ChEBI formula/charge parsing: fail closed when a participant lacks a usable formula or charge.
- Stoichiometry: distinguish atom/charge balance from reaction/mechanism validity.
- Coarse/fine transport: prevent `BH4 availability` or `nitrogen oxide` projections from reconstructing fine state without a witness.
- Runner output: always emit non-promotion flags and explicit missing kinetic/compartment/causal payments.

---

### Task 1: Regression-first end-to-end contract

**Files:**
- Create: `DASHI/Biology/BH4Chemistry369RunnerRegression.agda`
- Create: `scripts/check_bh4_chemistry_369_runner.py`

**Interfaces:**
- Consumes existing BH4, molecular, atomics, 369 and unified owners.
- Produces failing imports/tokens for Tasks 2-6.

- [ ] Write regression owners importing the future reaction, atomic/369, runner-receipt and unified-adapter modules.
- [ ] Confirm the contract is red because those owners do not yet exist.

### Task 2: Exact Rhea/ChEBI reaction acquisition

**Files:**
- Create: `scripts/acquire_rhea_chebi_bh4_reactions.py`
- Create: `DASHI/Biology/Molecular/BH4RheaChEBIReactionExact.agda`

**Interfaces:**
- Consumes UniProt panel/reaction references.
- Produces typed reaction/participant receipts with identifiers, formula, charge, direction and source coordinates.

- [ ] Add deterministic QDPR/RHEA:17869 fixture expectations first.
- [ ] Implement acquisition and the exact QDPR reaction witness.
- [ ] Preserve RHEA generic/directed IDs and ChEBI identity independently.

### Task 3: Stoichiometric molecular bridge

**Files:**
- Create: `DASHI/Biology/Molecular/BH4MolecularStoichiometryExact.agda`

**Interfaces:**
- Consumes Task 2 reaction participants.
- Produces atom/charge inventory, balanced-reaction certificate surface, and adapter to the existing molecular stoichiometry machinery.

- [ ] Add regressions that QDPR participant accounting is balanced but does not imply kinetics/mechanism.
- [ ] Implement the finite inventory and conservation witness.

### Task 4: Atomic + 369 refinement adapter

**Files:**
- Create: `DASHI/Interop/BH4Atomic369RefinementExact.agda`

**Interfaces:**
- Consumes Task 3 molecular receipts and existing atomics/369 transport.
- Produces scale/refinement receipts from atomic inventory -> molecule/reaction -> coarse biochemical projection.

- [ ] Add anti-collapse regressions first.
- [ ] Implement the adapter while retaining open Hamiltonian and quantitative-chemistry obligations.

### Task 5: Executable reaction-network runner + BH4 state receipt

**Files:**
- Create: `scripts/run_bh4_reaction_network.py`
- Create: `DASHI/Biology/BH4ReactionNetworkRunnerReceipt.agda`

**Interfaces:**
- Consumes acquired reaction certificates.
- Produces JSON/CSV/Markdown-compatible finite network audit plus a formal non-promoting runner receipt.

- [ ] Add tests/static contract for QDPR balance, graph edges, and fail-closed promotion flags.
- [ ] Implement stoichiometric/topological runner mode; kinetics remain explicitly absent unless externally supplied.
- [ ] Project runner output into `BH4SystemState` payment coordinates without inventing measured flux.

### Task 6: Unified cross-scale integration

**Files:**
- Create: `DASHI/Unified/BH4BiochemicalCrossScaleAdapter.agda`
- Modify: `DASHI/Biology/ExternalBiologyEverything.agda`
- Modify: `DASHI/Biology/KitzerowBH4EvidenceEverything.agda`
- Modify: `DASHI/Unified/Everything.agda` if the aggregate import is bounded and already conventional.
- Modify: `scripts/check_kitzerow_bh4_priority.py`

**Interfaces:**
- Consumes Tasks 2-5.
- Produces a bounded instance of the existing `atoms -> molecules -> chemistry -> cells` scaffold.

- [ ] Add regressions that cross-scale integration does not create first-principles chemistry, cell-state prediction, or disease causation.
- [ ] Wire focused roots and static checker.
- [ ] Update PR summary with the new live residual frontier.
