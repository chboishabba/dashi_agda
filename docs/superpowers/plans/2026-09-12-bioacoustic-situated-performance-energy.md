# Bioacoustic Situated Performance-Energy Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a repo-native situated birdsong performance carrier that keeps acoustic, respiratory, cardiac, movement, energetic and context fibres distinct while proving key single-axis nonfactorability boundaries.

**Architecture:** Add one thin biology owner over existing `IntersectionalNonFactorability`, `SituatedFibreDynamicsEverything`, SI, attribution, and `BioacousticSongEnergyExpenditureBidiExact`. Validation remains static/import based; no new runtime estimator or global planner is introduced.

**Tech Stack:** Agda, Bash static contracts, existing DASHI biology/core/physics modules.

**Spec:** `docs/superpowers/specs/2026-09-12-bioacoustic-situated-performance-energy-design.md`

## Global Constraints

- Reuse `FactorsThrough` / `NonFactorabilityWitness`; do not define a parallel factorisation abstraction.
- Reuse SI units and existing energy owner; do not add unit strings as authority.
- Source citations remain non-promoting and species/context bounded.
- Do not infer metabolic cost from pitch, SPL, pressure, heart rate, breathiness, or movement alone.
- Do not reorder the existing ROI/MaleCNS Pareto execution frontier.
- No exact-head kernel/build claim without a fresh verification receipt.

---

### Task 1: Static regression contract

**Files:**
- Create: `scripts/check_bioacoustic_situated_performance_static.sh`
- Modify: `scripts/check_bioacoustic_fly_state_space.sh`

**Interfaces:**
- Consumes: expected symbols/source identifiers from the new Agda owner.
- Produces: a fail-closed static check for the owner, source DOIs, situated axes, nonfactorability witnesses, and non-promotion boundaries.

- [ ] **Step 1: Write the failing static contract**

Require the future owner to contain `SituatedPerformanceState`, `AcousticAxis`, `RespiratoryAxis`, `CardiacAxis`, `MovementAxis`, `EnergeticAxis`, `SituatedContext`, `acousticProjectionCannotDetermineSituatedEffort`, `energeticProjectionCannotDetermineSituatedDisplay`, and the five empirical DOIs from the spec.

- [ ] **Step 2: Verify RED**

Run: `bash scripts/check_bioacoustic_situated_performance_static.sh`

Expected: FAIL because `DASHI/Biology/BioacousticSituatedPerformanceEnergyExact.agda` does not yet exist.

- [ ] **Step 3: Wire the static contract into the focused checker**

Add `bash scripts/check_bioacoustic_situated_performance_static.sh` after the existing birdsong energy static check.

- [ ] **Step 4: Commit the RED contract**

Commit message: `test: require situated birdsong performance-energy owner`

---

### Task 2: Situated performance owner

**Files:**
- Create: `DASHI/Biology/BioacousticSituatedPerformanceEnergyExact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.IntersectionalNonFactorability`, `DASHI.Core.SituatedFibreDynamicsEverything`, `DASHI.Core.AttributedSourceCore`, `DASHI.Physics.Units.SI`, `DASHI.Biology.BioacousticSongEnergyExpenditureBidiExact`.
- Produces: `SituatedPerformanceState`, axis records/enums, source atlas, two concrete nonfactorability witnesses, consumer-relative debt labels, and non-promotion boundaries.

- [ ] **Step 1: Add source objects**

Create attributed sources for:
- Zollinger et al. 2011 DOI `10.1371/journal.pone.0023198`;
- Franz & Goller 2003 DOI `10.1242/jeb.00196`;
- Goller et al. 2004 DOI `10.1002/neu.10327`;
- Cooper & Goller 2006 DOI `10.1152/jn.01123.2005`;
- Ota et al. 2015 DOI `10.1038/srep16614`.

Each relationship string must name only the fibre/proposition actually supported.

- [ ] **Step 2: Add the situated carrier**

Define semantic axis types for acoustic, respiratory, cardiac, movement, energetic and situated context. Define `SituatedPerformanceState` as a record containing those six coordinates plus a physical-time reference string.

- [ ] **Step 3: Add finite nonfactorability witnesses**

Construct one pair of states with the same acoustic projection but distinct situated-effort outcome, and one pair with the same energetic projection but distinct situated-display outcome. Use `NF.NonFactorabilityWitness` directly and derive contradictions with `NF.witnessRulesOutEveryFlatFactorisation`.

- [ ] **Step 4: Add consumer-relative debt labels**

Define labels for acoustic, respiratory, cardiac, movement, energetic and context calibration debt. State explicitly that they are consumer-relative coordinates and do not scalarize or reorder the existing fly ROI frontier.

- [ ] **Step 5: Add boundaries**

Record false permissions for pitch→energy, SPL→metabolic cost, breathiness→airflow/energy, heart-rate→song-production cost, dance→vocal effort, and separate-axis product→situated sufficiency.

- [ ] **Step 6: Commit the owner**

Commit message: `feat: add situated birdsong performance-energy fibres`

---

### Task 3: Validation/export integration

**Files:**
- Modify: `DASHI/Biology/BioacousticFlyStateSpaceValidation.agda`
- Modify: `DASHI/Biology/AnimalexicEverything.agda`

**Interfaces:**
- Consumes: `DASHI.Biology.BioacousticSituatedPerformanceEnergyExact`.
- Produces: focused validation/export visibility for the new owner.

- [ ] **Step 1: Import the owner in the focused validation root**

Add `import DASHI.Biology.BioacousticSituatedPerformanceEnergyExact`.

- [ ] **Step 2: Export the owner through `AnimalexicEverything`**

Add `open import DASHI.Biology.BioacousticSituatedPerformanceEnergyExact`.

- [ ] **Step 3: Verify static GREEN**

Run: `bash scripts/check_bioacoustic_situated_performance_static.sh`

Expected: PASS.

- [ ] **Step 4: Run focused checker**

Run: `bash scripts/check_bioacoustic_fly_state_space.sh`

Expected: runtime/static checks pass; if Agda is absent, output must explicitly avoid a kernel-clean claim.

- [ ] **Step 5: Run exact Agda validation when available**

Run: `agda -i . DASHI/Biology/BioacousticFlyStateSpaceValidation.agda`

Expected: exit 0 before claiming kernel-clean.

- [ ] **Step 6: Commit integration**

Commit message: `validate: wire situated birdsong performance-energy owner`

---

## Self-review

- Spec coverage: all six situated axes, source attribution, two nonfactorability witnesses, consumer-relative debt, and validation are mapped to tasks.
- Placeholder scan: no TODO/TBD steps remain.
- Type consistency: the new owner name and required witness names are identical across static contract, validation and exports.
- Scope: no runtime estimator, no new unit system, and no change to the existing ROI/MaleCNS execution frontier.
