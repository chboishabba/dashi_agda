# Twenty-Scientist Scientific Operator Factorisation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Factor the existing twenty scientist science fibres through six reusable scientific operator families and expose a science-only BIDI over those factorisations.

**Architecture:** Add one generic science-operator registry in `DASHI/Core`, six focused family adapters in `DASHI/Culture`, an all-20 coverage/factorisation ledger, and a science-only BIDI projection/reverse router. Reuse existing scientist science owners and `QueryFactorisationSufficiency` terminology; do not replace domain equations or imply common empirical mechanisms. The live branch already contains `Round13ReferenceKernelProgressExact`, so this tranche is numbered Round 14.

**Tech Stack:** Agda, existing DASHI `Prelude`, `QueryFactorisationSufficiency`, static shell contracts.

**Spec:** `docs/superpowers/specs/2026-09-13-twenty-scientist-operator-factorisation-design.md`

## Global Constraints

- Keep the scientific denominator exactly 20 = 11 U.S. + 9 Chinese scientists.
- Preserve Chavez as identity-gated and Amy as authorship/programme-gated.
- Operator-family sharing must not imply same equations, same empirical mechanism, collaboration, programme identity, possession, custody, historical deployment, or event cause.
- Reuse existing domain owners; adapters must be thin.
- Preserve the existing Round-13 reference-kernel tranche; do not overwrite or renumber it.
- Maintain source-written/no-kernel-claim status unless a fresh compiler/workflow receipt exists.

---

### Task 1: RED static contract

**Files:**
- Create: `scripts/check_missing_deceased_round14_scientific_operator_factorisation.sh`

**Interfaces:**
- Consumes: the design spec.
- Produces: a failing contract requiring all Round-14 owners and invariants.

- [ ] **Step 1: Write the failing checker** requiring `DASHI/Core/ScientificOperatorFamilyExact.agda`, six family adapters, `MissingDeceasedTwentyScientistScientificOperatorFactorisationExact.agda`, `MissingDeceasedTwentyScientistScientificOperatorBidiExact.agda`, counts `20/18/2`, all six family names, and aggregate imports.
- [ ] **Step 2: Verify RED** by fetching `DASHI/Core/ScientificOperatorFamilyExact.agda` on `agent/amy-memorial-bidi-mass-current` and confirming 404 before production creation.
- [ ] **Step 3: Commit** the contract only.

### Task 2: Generic scientific operator family owner

**Files:**
- Create: `DASHI/Core/ScientificOperatorFamilyExact.agda`

**Interfaces:**
- Consumes: `DASHI.Core.Prelude`, conceptual terminology from `DASHI.Core.QueryFactorisationSufficiency`.
- Produces: `ScientificOperatorFamily`, `ScientificOperatorShape`, `OperatorFactorisation`, canonical six shapes, and firewalls.

- [ ] **Step 1: Implement six family constructors:** `weakSignalInverseInference`, `resilientSensingControlVerification`, `materialsProcessStructureProperty`, `molecularSpectroscopyChemicalBiology`, `fieldPlasmaPrecisionForceDiscrimination`, `classificationEvidenceGovernance`.
- [ ] **Step 2: Define canonical shape records** with input/transform/output/reverse-obligation descriptions.
- [ ] **Step 3: Define thin factorisation record** retaining person, domain owner, family, and bounded-reading string.
- [ ] **Step 4: Add firewalls:** family sharing does not imply same equations/mechanism/programme/collaboration/common cause.
- [ ] **Step 5: Source-inspect the file** after creation.

### Task 3: Six focused family adapters

**Files:**
- Create: `DASHI/Culture/MissingDeceasedWeakSignalInverseInferenceOperatorExact.agda`
- Create: `DASHI/Culture/MissingDeceasedResilientControlOperatorExact.agda`
- Create: `DASHI/Culture/MissingDeceasedMaterialsProcessOperatorExact.agda`
- Create: `DASHI/Culture/MissingDeceasedMolecularMeasurementOperatorExact.agda`
- Create: `DASHI/Culture/MissingDeceasedFieldComparatorOperatorExact.agda`
- Create: `DASHI/Culture/MissingDeceasedClassificationEvidenceOperatorExact.agda`

**Interfaces:**
- Consumes: existing scientist domain owners and `ScientificOperatorFamilyExact`.
- Produces: named `OperatorFactorisation` values and family-specific reverse scientific leaves.

- [ ] **Step 1: Weak-signal adapter** for Grillmair, Hicks, Zhang Xiaoxin, Maiwald, Thomas.
- [ ] **Step 2: Resilient-control adapter** for LeBlanc, McCasland, Zhang Daibing, Chen, Yan.
- [ ] **Step 3: Materials adapter** for Reza, Zhou, Fang.
- [ ] **Step 4: Molecular adapter** for Maiwald, Thomas, Li Minyong.
- [ ] **Step 5: Field/comparator adapter** for Nuno, Ning, Amy; Amy explicitly gated.
- [ ] **Step 6: Classification/evidence adapter** for Feng, Liu, Chen.
- [ ] **Step 7: Source-inspect each adapter** and confirm no historical/collaboration promotion.

### Task 4: All-20 operator factorisation ledger

**Files:**
- Create: `DASHI/Culture/MissingDeceasedTwentyScientistScientificOperatorFactorisationExact.agda`

**Interfaces:**
- Consumes: six family adapters.
- Produces: exactly twenty rows and the `20/18/2` coverage invariants.

- [ ] **Step 1: Define `FactorisationStatus = paid | gated`.**
- [ ] **Step 2: Define one row per scientist** with `List ScientificOperatorFamily`, domain owner, status, next science leaf.
- [ ] **Step 3: Keep overlaps explicit** for Maiwald, Thomas, Chen and any other justified multi-family rows.
- [ ] **Step 4: Set `scientificOperatorFactorisationCount = 20`, `paidScienceFactorisationCount = 18`, `gatedScienceFactorisationCount = 2`, `everyScientistRepresented = true`.
- [ ] **Step 5: Add firewalls** for family-sharing vs mechanism/collaboration.

### Task 5: Science-only BIDI over operator families

**Files:**
- Create: `DASHI/Culture/MissingDeceasedTwentyScientistScientificOperatorBidiExact.agda`

**Interfaces:**
- Consumes: all-20 factorisation ledger and core operator shapes.
- Produces: forward reusable-role projection and reverse scientific-coordinate obligations.

- [ ] **Step 1: Define `ScientificRoleQuery` over the six operator families.**
- [ ] **Step 2: Define forward projection** from a factorised scientist row to reusable operator-role text.
- [ ] **Step 3: Define reverse obligation record** containing family, candidate fibres, missing scientific coordinate and bounded reading.
- [ ] **Step 4: Add hard firewalls** against historical deployment, person possession, custody and event cause.

### Task 6: Round-14 progress and aggregate wiring

**Files:**
- Create: `DASHI/Culture/MissingDeceasedTwentyScientistRound14OperatorFactorisationProgressExact.agda`
- Modify: `DASHI/Culture/MissingDeceasedTwentyScientistRoundRobinEverything.agda`

**Interfaces:**
- Consumes: factorisation ledger and BIDI.
- Produces: all-20 Round-14 science progress and aggregate exposure.

- [ ] **Step 1: Add twenty Round-14 rows** recording primary family/families and next science leaf.
- [ ] **Step 2: Add `round14ScientificCohortCount = 20`, `round14PaidFactorisationCount = 18`, `round14GatedFactorisationCount = 2`, `round14EveryScientistTouched = true`.
- [ ] **Step 3: Import core/operator adapters/ledger/BIDI/Round-14 owner from the focused aggregate while retaining Round 13.**
- [ ] **Step 4: Refresh the static checker** if exact symbols differ from the plan, without weakening the contract.

### Task 7: Verification

**Files:**
- Inspect: all Round-14 owners and the focused aggregate.

**Interfaces:**
- Produces: source-level verification status only unless executable CI/compiler evidence exists.

- [ ] **Step 1: Fetch every created owner from the exact branch.**
- [ ] **Step 2: Fetch PR #872 exact head metadata.**
- [ ] **Step 3: Query exact-head workflow runs.**
- [ ] **Step 4: Report `source-written/static-contract integrated` unless an actual shell/Agda run exists.**
