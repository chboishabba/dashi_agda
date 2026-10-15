# Kitzerow BH4 Attribution Max-Cut Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement a provenance-aware Kitzerow BH4/autism candidate causal graph that is directly plugged into existing DASHI Biology, neurochemical/brain, Chemistry/Biology interop, evidence-dependence, experimental-design, and promotion-boundary machinery.

**Architecture:** Add a focused Biology tranche rather than a new generic framework. Reuse `AttributedSourceCore`, `AllostaticBodyStateExact`, `CellStateAttractor`, `NeurochemicalBrainCarrierBridge`, `GenomeSensorimotorConnectomeBridge`, `NeurochemicalGenomicExpressionBridge`, `PhysicsChemistryBiologyDNAUnificationDischarge`, `ChemistryBiologyObligations`, `NeurochemicalAuthorityBoundary`, same-trial provenance dependence, and PNF experimental backprop. Separate scientific support, chronology, exposure/contact, derivation, and legal attribution so no one axis silently promotes another.

**Tech Stack:** Agda; existing DASHI source/provenance and Biology/Chemistry/Brain interfaces; lightweight static validation script where kernel execution is unavailable.

**Spec:** `docs/superpowers/specs/2026-10-15-kitzerow-bh4-attribution-maxcut-design.md`

## Global Constraints

- Treat Kitzerow's architecture as a candidate empirical graph, not an established causal truth.
- Acquire and attribute sources Pareto-first; source identity never imports proof or authority.
- Keep scientific support, priority/chronology, exposure/contact, derivation, and legal conclusions distinct.
- Do not infer plagiarism, copying, derivation, independence, whole-model confirmation, clinical validity, or legal infringement from overlap alone.
- Reuse existing Brain/Biology/Chemistry machinery instead of duplicating it.
- Current web/contact claims remain `originatorReported...` unless a direct underlying artifact is acquired.
- Every current comparison study must have `wholeModelConfirmed = false`.

## Review Focus

1. Contact provenance: an originator-reported contact must not become verified direct access without a direct artifact.
2. Prior-art subtraction: old BH4/NOS/allostasis biology must not be attributed to Kitzerow merely because it appears in her graph.
3. Brain bridge: downstream circuit evidence must remain candidate-only and must not imply brain-state recovery or behavioural causation.
4. Chemistry bridge: BH4/redox/cofactor chemistry must enter through existing chemistry/biology authority seams and retain context/assay obligations.
5. Experimental closure: direct support for a downstream edge must leave the upstream BH4 allocation hypothesis open unless the same-edge intervention is paid.

---

### Task 1: TDD validation owner and integration contract

**Files:**
- Create: `DASHI/Biology/KitzerowBH4MaxCutValidation.agda`
- Create: `scripts/check_kitzerow_bh4_maxcut.py`

**Interfaces:**
- Consumes: planned owner module names from Tasks 2-7.
- Produces: compile/static contract requiring all owners, source-count/provenance firewalls, Brain/Biology/Chemistry imports, and non-promotion boundaries.

- [ ] **Step 1: Write failing validation imports/assertions** for the missing owner modules and exact required integration strings.
- [ ] **Step 2: Verify RED** by checking that the production files are absent on the branch and the static check cannot pass.
- [ ] **Step 3: Commit the RED validation contract.**

### Task 2: Candidate causal graph + direct Biology/Chemistry/Brain adapters

**Files:**
- Create: `DASHI/Biology/KitzerowBH4CascadeExact.agda`
- Create: `DASHI/Biology/KitzerowBH4RepoIntegrationExact.agda`

**Interfaces:**
- Consumes: `AllostaticBodyStateExact`, `CellStateAttractor`, `NeurochemicalBrainCarrierBridge`, `GenomeSensorimotorConnectomeBridge`, `NeurochemicalGenomicExpressionBridge`, `PhysicsChemistryBiologyDNAUnificationDischarge`, `ChemistryBiologyObligations`, `NeurochemicalAuthorityBoundary`.
- Produces: `CascadeNode`, `CascadeEdge`, `EdgeStatus`, canonical candidate edge set, and integration receipt proving reuse of existing owner surfaces while all clinical/brain-state promotion remains blocked.

- [ ] **Step 1: Implement graph nodes/edges/statuses with no `confirmedWholeModel` constructor.**
- [ ] **Step 2: Implement repo integration receipt with explicit Biology, Brain/neurochemical, Chemistry/Biology interop and promotion-boundary owner references.**
- [ ] **Step 3: Verify static integration requirements pass for Task 2 surfaces.**
- [ ] **Step 4: Commit.**

### Task 3: Source atlas and bounded evidence receipts

**Files:**
- Create: `DASHI/Biology/KitzerowBH4SourceAtlasExact.agda`
- Create: `DASHI/Biology/KitzerowBH4ConvergentEvidenceExact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.AttributedSourceCore`, Task 2 graph.
- Produces: attributed source groups and per-study evidence receipts with organism/context/design/exact-edge/adjacent-projection fields.

- [ ] **Step 1: Add Kitzerow primary works and inherited BH4 prior-art sources using `AttributedSourceCore`.**
- [ ] **Step 2: Add acquired comparison-study source identities with explicit exclusion boundaries.**
- [ ] **Step 3: Add canonical evidence receipts for BH4 review, NO-TSC2-mTOR, reticular thalamus, Nomura, subtype studies, Melillo, and IACC.**
- [ ] **Step 4: Prove/record every current receipt has `wholeModelConfirmed = false`.**
- [ ] **Step 5: Commit.**

### Task 4: Priority, contact, derivation, and attribution firewall

**Files:**
- Create: `DASHI/Biology/KitzerowPriorityAttributionExact.agda`

**Interfaces:**
- Consumes: Task 3 sources; existing provenance-dependence semantic pattern.
- Produces: `ChronologyRelation`, `ExposureEvidence`, `DerivationStatus`, canonical comparison rows, and explicit non-implication boundaries.

- [ ] **Step 1: Implement chronology/exposure/derivation types.**
- [ ] **Step 2: Encode Japan as comparison-earlier / independence-supported for the bounded claim; Stanford contact as originator-reported until direct artifact acquisition.**
- [ ] **Step 3: Encode Brazil/IACC/Italy/Melillo without upgrading allegation or overlap to derivation.**
- [ ] **Step 4: Add firewalls: earlier != copying, contact != use, public availability != access, access != derivation, derivation != infringement, citation absence != plagiarism.**
- [ ] **Step 5: Commit.**

### Task 5: Prior-art subtraction and dependence-aware convergence

**Files:**
- Create: `DASHI/Biology/KitzerowBH4PriorArtSubtractionExact.agda`

**Interfaces:**
- Consumes: Tasks 2-4; `DrosophilaSameTrialProvenanceDependenceExact` as the existing independence/dependence pattern.
- Produces: overlap partition into inherited biology, distinctive prior Kitzerow arrangement, later measured edge, and unresolved common-source possibility.

- [ ] **Step 1: Implement overlap partition carrier.**
- [ ] **Step 2: Add canonical partitions for at least Stanford, Nomura, BH4 review, and NO-TSC2-mTOR.**
- [ ] **Step 3: Add no-double-counting / no-independence-from-unknown-provenance boundary.**
- [ ] **Step 4: Commit.**

### Task 6: Experimental discriminator and Pareto acquisition frontier

**Files:**
- Create: `DASHI/Biology/KitzerowBH4ExperimentalDiscriminatorExact.agda`
- Create: `DASHI/Biology/KitzerowBH4ParetoAcquisitionExact.agda`

**Interfaces:**
- Consumes: graph/evidence state, `ExperimentalAssertionPNFImplicationConeExact`, `BlockedImplicationExperimentBackpropExact`, `SnowballPluralLensDiscoveryAdmissionExact`.
- Produces: missing experimental slots for the central BH4-allocation hypothesis and Pareto-ranked acquisition targets without truth ranking.

- [ ] **Step 1: Represent the unpaid central edge as an experimental-design obligation.**
- [ ] **Step 2: Specify discriminating interventions/readouts that separate upstream BH4 allocation from downstream/parallel explanations.**
- [ ] **Step 3: Add acquisition dimensions: evidentiary impact, provenance closure, primary-source authority, accessibility/cost; preserve non-scalar Pareto frontier.**
- [ ] **Step 4: Put direct contact artifacts/manuscript histories and same-object BH4 allocation experiments on the live frontier.**
- [ ] **Step 5: Commit.**

### Task 7: Rollup, Everything integration, and final validation

**Files:**
- Create: `DASHI/Biology/KitzerowBH4Everything.agda`
- Modify: `DASHI/Biology/Everything.agda`
- Complete: `DASHI/Biology/KitzerowBH4MaxCutValidation.agda`
- Complete: `scripts/check_kitzerow_bh4_maxcut.py`

**Interfaces:**
- Consumes: Tasks 2-6.
- Produces: focused entry surface reachable from Biology Everything and static/kernel validation receipts.

- [ ] **Step 1: Add focused rollup imports.**
- [ ] **Step 2: Import focused rollup from `DASHI/Biology/Everything.agda`.**
- [ ] **Step 3: Run static validation and, if an Agda executable is available, compile the validation owner plus Biology Everything.**
- [ ] **Step 4: Fix only failures attributable to this tranche.**
- [ ] **Step 5: Record honest verification boundary if kernel execution is unavailable.**
- [ ] **Step 6: Commit and review the branch diff against the approved design.**
