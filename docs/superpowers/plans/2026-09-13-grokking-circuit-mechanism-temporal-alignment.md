# Grokking Circuit-Mechanism Temporal Alignment Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a formal Stage-6/7 temporal-alignment bridge that compares predeclared circuit-beta transitions against existing horizon-aware Grokking first-passage receipts without promoting beta directly into `GrokkingMechanismWitness`.

**Architecture:** Keep the existing `DASHI.Cognition.PNF` circuit-routing owner authoritative for intervention relations and finite beta, and add a thin `DASHI.Learning` owner that imports those receipts plus `GrokkingOperatorContract`. The bridge classifies beta timing relative to `test95` under matched run identity, fixed extraction/intervention rules, paid beta certificates, declared cadence tolerance, and anti-leakage. Roadmap/docs register the new receipt family but do not alter `GrokkingMechanismWitness` or build the runtime checkpoint producer.

**Tech Stack:** Agda, existing DASHI `GrokkingOperatorContract`, `GrokkingCOLBridge`, PR #900 circuit-routing owner, repo-native regression modules, GitHub Actions/focused Agda workflow if available.

**Spec:** `docs/superpowers/specs/2026-09-13-grokking-circuit-mechanism-temporal-alignment-design.md`

## Global Constraints

- Preserve first-passage/right-censoring semantics from `DASHI.Learning.GrokkingOperatorContract`.
- Reuse PR #900 circuit/intervention/beta carriers; do not duplicate conflict, requirement, or beta ontologies.
- Held-out `test95` outcome must not select extraction rules, intervention thresholds, beta threshold, or coincidence tolerance.
- `alignmentPromotionPaid` only means the temporal comparison is admissible; it must not pay `GrokkingMechanismWitness`, contraction, MDL, or causality.
- First tranche is synthetic/formal only; no historical checkpoint reconstruction and no runtime checkpoint producer.
- TDD ordering is mandatory: regression first, verify exact missing declaration/failure, then minimal owner implementation.
- No Agda GREEN claim without a fresh kernel/typecheck receipt.

---

### Task 1: Temporal-Alignment Formal Owner

**Files:**
- Create: `DASHI/Learning/GrokkingCircuitTemporalAlignmentExact.agda`
- Create: `DASHI/Learning/GrokkingCircuitTemporalAlignmentRegression.agda`

**Interfaces:**
- Consumes: `DASHI.Learning.GrokkingOperatorContract.FirstPassage`, `GrokkingObservation`; `DASHI.Cognition.PNF.GrokkingSparseActiveColouringRoutingExact.FiniteClosedCompatibleSystem`, `betaClosedCompatible`, `maximalityPaidByFiniteExhaustion`.
- Produces: `RunIdentity`, `GrokkingCircuitMechanismObservation`, `GrokkingCircuitTrajectoryReceipt`, `TemporalClassification`, `GrokkingTemporalAlignmentReceipt`, `classifyTemporalAlignment`, `alignmentPromotionPaid`.

- [ ] **Step 1: Write the failing regression before creating the owner**

Create `DASHI/Learning/GrokkingCircuitTemporalAlignmentRegression.agda` importing the not-yet-existing owner as `Align` and require these exact behaviours:

```agda
module DASHI.Learning.GrokkingCircuitTemporalAlignmentRegression where

open import DASHI.Core.Prelude
import DASHI.Learning.GrokkingCircuitTemporalAlignmentExact as Align

betaBeforeTest95IsClassified :
  Align.temporalClassification Align.syntheticBeforeReceipt ≡ Align.betaBeforeTest95
betaBeforeTest95IsClassified = refl

betaCoincidentWithinCadenceIsClassified :
  Align.temporalClassification Align.syntheticCoincidentReceipt ≡ Align.betaCoincidentWithTest95
betaCoincidentWithinCadenceIsClassified = refl

betaAfterTest95IsClassified :
  Align.temporalClassification Align.syntheticAfterReceipt ≡ Align.betaAfterTest95
betaAfterTest95IsClassified = refl

unobservedBetaTransitionStaysUnobserved :
  Align.temporalClassification Align.syntheticUnobservedReceipt ≡ Align.betaTransitionUnobserved
unobservedBetaTransitionStaysUnobserved = refl

rightCensoredTest95StaysRightCensored :
  Align.temporalClassification Align.syntheticRightCensoredReceipt ≡ Align.firstPassageRightCensored
rightCensoredTest95StaysRightCensored = refl

mismatchedRunIdentityFailsClosed :
  Align.alignmentPromotionPaid Align.syntheticMismatchedRunReceipt ≡ false
mismatchedRunIdentityFailsClosed = refl

ruleDriftFailsClosed :
  Align.alignmentPromotionPaid Align.syntheticRuleDriftReceipt ≡ false
ruleDriftFailsClosed = refl

unpaidBetaFailsClosed :
  Align.alignmentPromotionPaid Align.syntheticUnpaidBetaReceipt ≡ false
unpaidBetaFailsClosed = refl

heldOutOutcomeDoesNotSelectCircuitRule :
  Align.heldOutOutcomeUsedForSelection Align.syntheticBeforeReceipt ≡ false
heldOutOutcomeDoesNotSelectCircuitRule = refl

admissibleAlignmentDoesNotPayMechanism :
  Align.alignmentPaysGrokkingMechanismWitness ≡ false
admissibleAlignmentDoesNotPayMechanism = refl
```

- [ ] **Step 2: Verify RED structurally**

Check the exact branch for `DASHI/Learning/GrokkingCircuitTemporalAlignmentExact.agda` before implementation. Expected result: file absent / import unresolved. Record the regression commit SHA and absence receipt in the PR body. Do not call this an executed Agda RED unless the compiler is actually run.

- [ ] **Step 3: Implement the minimal owner**

Create `DASHI/Learning/GrokkingCircuitTemporalAlignmentExact.agda` with these core surfaces:

```agda
module DASHI.Learning.GrokkingCircuitTemporalAlignmentExact where

open import DASHI.Core.Prelude
open import Data.Nat using (_∸_)
import DASHI.Learning.GrokkingOperatorContract as Grok
import DASHI.Cognition.PNF.GrokkingSparseActiveColouringRoutingExact as Circuit

record RunIdentity : Set where
  constructor runIdentity
  field
    modulusOrTaskKey : Nat
    seed : Nat
    configurationKey : Nat

record GrokkingCircuitMechanismObservation : Set where
  constructor circuitObservation
  field
    runIdentity : RunIdentity
    checkpointEpoch : Nat
    extractionRuleKey : Nat
    interventionRuleKey : Nat
    relationThresholdKey : Nat
    circuitSystem : Circuit.FiniteClosedCompatibleSystem
    activeSupport : Nat
    heldOutOutcomeUsedForSelection : Bool

record GrokkingCircuitTrajectoryReceipt : Set where
  constructor circuitTrajectory
  field
    trajectoryRunIdentity : RunIdentity
    firstPaidBetaTransition : Grok.FirstPassage
    extractionRuleStable : Bool
    interventionRuleStable : Bool
    relationThresholdStable : Bool
    allBetaMaximalityPaid : Bool
    checkpointCadence : Nat


data TemporalClassification : Set where
  betaBeforeTest95
  betaCoincidentWithTest95
  betaAfterTest95
  betaTransitionUnobserved
  firstPassageRightCensored
  notComparable : TemporalClassification

record GrokkingTemporalAlignmentReceipt : Set where
  constructor temporalAlignmentReceipt
  field
    observation : Grok.GrokkingObservation
    trajectory : GrokkingCircuitTrajectoryReceipt
    sameRunIdentity : Bool
    sameHeldOutSplit : Bool
    sameHorizon : Bool
    selectionFrozenBeforeOutcomeComparison : Bool
    temporalClassification : TemporalClassification
    alignmentPromotionPaid : Bool
    heldOutOutcomeUsedForSelection : Bool
```

Implement a finite helper for coincidence using declared checkpoint cadence only. Classification rules:

```text
mismatch / rule drift / unpaid beta / selection leakage -> notComparable + promotion false
beta transition right-censored/not recorded -> betaTransitionUnobserved
existing test95 right-censored -> firstPassageRightCensored
|t_beta - t95| <= cadence -> betaCoincidentWithTest95
t_beta < t95 -> betaBeforeTest95
t_beta > t95 -> betaAfterTest95
```

The synthetic witnesses must use fixed rule keys and must set:

```agda
alignmentPaysGrokkingMechanismWitness : Bool
alignmentPaysGrokkingMechanismWitness = false
```

- [ ] **Step 4: Verify the owner/regression if a focused Agda path is available**

Run the smallest existing focused kernel command/workflow that can typecheck `DASHI/Learning/GrokkingCircuitTemporalAlignmentRegression.agda`. If no runnable focused path is available from this environment, record that exact limitation and do not infer GREEN from source inspection.

- [ ] **Step 5: Commit the production owner separately from the RED regression**

Expected commit ordering:

```text
regression: formalise grokking circuit temporal-alignment contract
implementation: add grokking circuit temporal-alignment owner
```

---

### Task 2: Register the Stage-6/7 Receipt Seam in the Existing Roadmap

**Files:**
- Modify: `Docs/learning/GrokkingOperatorFormalism.md`
- Modify: `DASHI/Programmes/GrokkingExact.agda`
- Modify if repo convention requires aggregate import: the existing `DASHI.Learning` regression/everything surface that already imports `GrokkingRegression`.

**Interfaces:**
- Consumes: Task 1 temporal-alignment owner.
- Produces: roadmap visibility only; no new mechanism theorem.

- [ ] **Step 1: Add a regression/static assertion for roadmap status before changing roadmap production text**

If `ResearchProgramme` exposes a suitable extension/status coordinate, add a focused regression that pins the circuit lane to calibration/experiment rather than core-kernel promotion. If no such typed coordinate exists, do not invent one merely for documentation; use import-level registration only.

- [ ] **Step 2: Update `GrokkingOperatorFormalism.md`**

Add one subsection, `Circuit-mechanism temporal alignment`, stating exactly:

```text
GrokkingObservation || GrokkingCircuitTrajectoryReceipt
                    -> GrokkingTemporalAlignmentReceipt
```

Document the anti-leakage rule, the temporal classifications, and these firewalls:

```text
beta-before-test95 != causal mechanism
alignmentPromotionPaid != GrokkingMechanismWitness
cross-seed stability != cross-task stability
```

Extend the “Next scientific closure obligations” list with saved checkpoint acquisition, cross-seed replication, cross-task/config transfer, timing nulls, threshold robustness, and active-support baseline comparison.

- [ ] **Step 3: Register the seam in `DASHI.Programmes.GrokkingExact.agda` without changing programme stage**

Import or name the new temporal-alignment owner only if that matches `ResearchProgrammeExact` conventions. Preserve:

```agda
DASHIg

grokkingValidation
corePredictionInference
coreKernelDefectAdmissibility
explicitBridge
```

Do not promote the circuit receipt into `coreKernelDefectAdmissibility` or alter the existing Stage-6/7 programme classification.

- [ ] **Step 4: Commit roadmap registration**

Use a separate commit such as:

```text
docs: register circuit temporal alignment in grokking roadmap
```

---

### Task 3: Verification, PR Reconciliation, and Next-Tranche Boundary

**Files:**
- Modify: PR #900 body only if needed.
- No runtime producer files in this plan.

**Interfaces:**
- Consumes: Tasks 1-2.
- Produces: exact verification status and an explicit residual for the runtime checkpoint producer.

- [ ] **Step 1: Compare branch to `master`**

Run repository compare and record:

```text
ahead_by
behind_by
changed files
```

Confirm that the temporal-alignment tranche adds only the planned Learning owner/regression plus roadmap/docs surfaces on top of existing #900 files.

- [ ] **Step 2: Check exact-head CI/workflows**

Query workflow runs and combined statuses for the exact head SHA. Report each status literally. If no Agda workflow ran, state `Agda kernel certification unpaid`.

- [ ] **Step 3: Re-read the design success criterion against the diff**

Confirm the code can represent:

```text
For run R, under a predeclared circuit extraction/intervention protocol,
a paid beta transition occurred at t_beta; test95 occurred at t95;
the temporal relation is X.
```

Also confirm the code cannot derive `GrokkingMechanismWitness` from that receipt.

- [ ] **Step 4: Update PR #900 body with exact TDD and verification receipts**

Include the RED regression commit, production commit, roadmap commit, exact head, compare state, and CI boundary. Do not describe structural RED as compiler RED unless the compiler was run.

- [ ] **Step 5: Stop at the planned wall**

Leave the following explicit residuals unpaid for the next tranche:

```text
saved Mod97 checkpoint acquisition
runtime circuit extraction/intervention producer
cross-seed replication
cross-task/config replication
null execution
concrete adapter into GrokkingMechanismWitness
```

Do not implement them in this plan.
