# Coarse/Fine Fabric Calculus Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add one minimal projection-loss theorem family over existing DASHI coarse/fine machinery and connect JCoarse/JFine, NDim, and wave refinement without creating a parallel ontology.

**Architecture:** Reuse `CoarseFineRelativeFibreExact` as the exact-reopening specialisation, add a weaker projection-only kernel for collision/non-factorability, then add thin adapters. Static nonrecoverability is separated from dynamic congruence. 369 remains downstream until the shared theorem has three grounded consumers.

**Tech Stack:** Agda, existing DASHI Core/Physics/Biology owners, GitHub Actions/static checkers where present.

**Spec:** `docs/superpowers/specs/2026-09-13-coarse-fine-fabric-calculus-design.md`

## Global Constraints

- Do not replace existing coarse/fine, NDim, wave, or J owners.
- Do not identify coarsening with refinement/reconstruction.
- Do not identify dimension with state count, candidate count, or carrier identity.
- Do not infer dynamic noncongruence from static nonrecoverability.
- Use TDD: regression first, verify RED, then production owner.
- Do not claim Agda kernel success without a fresh compiler/CI receipt.

---

### Task 1: RED regression for the shared projection-loss surface

**Files:**
- Create: `DASHI/Core/CoarseFineFabricCalculusRegression.agda`

**Interfaces:**
- Consumes: intended production module `DASHI.Core.CoarseFineFabricCalculusExact`
- Produces: compile-time requirements for `ProjectionCollision`, `consumerCannotFactorThroughProjection`, `jCoarseFineProjectionLossAdapter`, `nDimProjectionBoundaryAdapter`, and `waveProjectionStatus`

- [ ] **Step 1: Write the failing regression**

Create a regression importing `DASHI.Core.CoarseFineFabricCalculusExact` and pin the exact names above, plus boundary Booleans stating that static nonrecoverability is not dynamic noncongruence and 369 is not promoted by this tranche.

- [ ] **Step 2: Verify RED**

Run the focused Agda/checker route available to this repository, or branch CI if no local compiler is exposed. Expected failure: missing `DASHI.Core.CoarseFineFabricCalculusExact` / missing required symbols. Record inability to execute Agda as inconclusive, not PASS.

- [ ] **Step 3: Commit RED checkpoint**

Commit only the regression.

---

### Task 2: Minimal generic projection-collision theorem

**Files:**
- Create: `DASHI/Core/CoarseFineFabricCalculusExact.agda`
- Modify: `DASHI/Core/CoarseFineFabricCalculusRegression.agda` only if a type-level correction is required by the implementation; do not weaken the contract.

**Interfaces:**
- Consumes: `DASHI.Core.Prelude`, existing factorisation/reduction machinery where compatible
- Produces:
  - `ProjectionCollision`
  - `consumerCannotFactorThroughProjection`
  - a boundary/status record separating static loss from dynamics and exact reopening

- [ ] **Step 1: Define the smallest projection-only witness**

`ProjectionCollision` stores two fine states, proof that their coarse projections agree, and a consumer-separation proof.

- [ ] **Step 2: Prove non-factorability from collision**

`consumerCannotFactorThroughProjection` must show that no coarse observation can agree with the fine consumer on both colliding states. Keep this independent of exact reopening.

- [ ] **Step 3: Verify GREEN for generic core**

Run the focused checker/Agda route and confirm the regression advances past the missing generic symbols.

- [ ] **Step 4: Commit generic core**

---

### Task 3: JCoarse/JFine adapter

**Files:**
- Modify: `DASHI/Core/CoarseFineFabricCalculusExact.agda` or create a thin adjacent adapter if repository layering requires Biology not be imported from Core.
- Prefer create: `DASHI/Biology/JCoarseFineFabricCalculusAdapterExact.agda` if Core->Biology would invert dependencies.
- Modify regression imports accordingly without changing theorem semantics.

**Interfaces:**
- Consumes: `DASHI.Biology.JCoarseFineConsumerReductionBridgeExact`, `DASHI.Core.CoarseFineRelativeFibreExact`
- Produces: `jCoarseFineProjectionLossAdapter`

- [ ] **Step 1: Add/retain failing adapter requirement**

Ensure regression requires the adapter by exact name.

- [ ] **Step 2: Implement adapter by reusing existing J fine-sensitive reduction theorem**

Do not reconstruct J geometry or define a second consumer-reduction theorem.

- [ ] **Step 3: Verify**

Focused compile/static check.

- [ ] **Step 4: Commit J adapter**

---

### Task 4: NDim restriction adapter

**Files:**
- Prefer create: `DASHI/Core/NDimProjectionLossAdapterExact.agda`
- Modify regression imports.

**Interfaces:**
- Consumes: `DASHI.Core.NDimParetoHyperfabricExact`
- Produces: `nDimProjectionBoundaryAdapter`

- [ ] **Step 1: Require the NDim boundary in regression**

Pin that full dominance implies projected dominance while the converse is not promoted.

- [ ] **Step 2: Implement the thinnest adapter**

Expose NDim axis restriction as a projection/restriction manifestation. Do not fabricate a collision witness unless the existing owner provides one.

- [ ] **Step 3: Verify**

Focused compile/static check.

- [ ] **Step 4: Commit NDim adapter**

---

### Task 5: Wave refinement status/adapter

**Files:**
- Prefer create: `DASHI/Physics/WaveProjectionLossAdapterExact.agda`
- Modify regression imports.

**Interfaces:**
- Consumes: `DASHI.Physics.ShiftWaveRefinementSeam` and existing transport residual owner where needed
- Produces: `waveProjectionStatus`

- [ ] **Step 1: Inspect actual wave seam types**

Determine whether current owners provide a genuine projection collision/factorisation witness or only a refinement/transport residual.

- [ ] **Step 2: Implement only supported surface**

If a real collision exists, adapt it. Otherwise export a typed status saying the static projection-loss weld remains unpaid while retaining the existing transport residual. Do not infer dynamic failure from phase difference alone.

- [ ] **Step 3: Verify**

Focused compile/static check.

- [ ] **Step 4: Commit wave adapter/status**

---

### Task 6: Narrow rollup and verification

**Files:**
- Modify the narrowest existing `Everything`/Core rollup that already aggregates the relevant kernel, or create `DASHI/Core/CoarseFineFabricEverything.agda` if no suitable rollup exists.

**Interfaces:**
- Consumes: generic core + J + NDim + wave adapters
- Produces: opt-in aggregate only

- [ ] **Step 1: Wire narrow aggregate**

Do not alter a giant default build target.

- [ ] **Step 2: Run focused verification**

Run Agda/CI/static checks available for all new owners and regression. Distinguish kernel certification from static/import checks.

- [ ] **Step 3: Inspect diff for ontology duplication**

Confirm no new parallel definitions of existing coarse/fine reopening, Pareto order, wave carrier, or J geometry were added.

- [ ] **Step 4: Commit rollup**

- [ ] **Step 5: Record next Pareto tranche**

Rank: (a) dynamic congruence/transport defect, (b) 369 finite-fabric adapter via existing Base369-NDim chart, (c) branch/refine/local-action/reglue theorem against graph colouring + NDim reducers + wave/pants.
