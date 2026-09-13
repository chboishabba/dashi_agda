# SensibLaw Legal Reasonableness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a source-bound SensibLaw adapter for Wednesbury and modern Australian legal unreasonableness over the generic situated-reasonableness core.

**Architecture:** Keep historical/doctrinal source manifestations separate from generic reasonableness structure. Reuse `AttributedSourceCore` for Wednesbury, `Li`, and `SZVFW`; reuse `ObserverSituatedReasonablenessExact` only as an abstract observer/index donor. Encode doctrinal separations and source-paid facts without importing legal authority from citation alone.

**Tech Stack:** Agda; `DASHI.Core.AttributedSourceCore`; `DASHI.Core.ObserverSituatedReasonablenessExact`; focused regression and GitHub workflow.

**Spec:** `docs/superpowers/specs/2026-09-13-institutional-norm-production-fragmentation-design.md`

## Global Constraints

- Wednesbury is a historical doctrinal formulation, not a synonym for every Australian instance of legal unreasonableness.
- Merits disagreement, factual error, relevant/irrelevant-consideration error, legal unreasonableness, and jurisdictional consequence remain distinct.
- Source identity/citation imports neither proof nor legal authority.
- BAILII pays the published Wednesbury judgment text; High Court sources pay `Li` and `SZVFW` case identity/reasons.
- Do not encode a proposition broader than the cited judgment actually supports.
- No legal advice or case-specific conclusion is produced by the formal owner.
- No Agda GREEN without exact-head execution receipt.

---

### Task 1: RED regression

**Files:**
- Create first: `DASHI/Law/SensibLawLegalReasonablenessRegression.agda`
- Create after RED: `DASHI/Law/SensibLawLegalReasonablenessExact.agda`

**Interfaces:**
- Consumes source core and generic situated reasonableness.
- Produces attributed source atlas, doctrinal lineage statuses, finite doctrine-separation boundary, and positive source-paid case receipts.

- [ ] **Step 1: Add failing regression**

Require:

```agda
module DASHI.Law.SensibLawLegalReasonablenessRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawLegalReasonablenessExact as LR

wednesbury-appeal-was-dismissed :
  LR.wednesburyAppealDismissed LR.canonicalWednesburyCaseReceipt ≡ true
wednesbury-appeal-was-dismissed = refl

li-refusal-held-unreasonable :
  LR.liTribunalRefusalHeldLegallyUnreasonable LR.canonicalLiCaseReceipt ≡ true
li-refusal-held-unreasonable = refl

szvfw-tribunal-decision-not-held-unreasonable :
  LR.szvfwTribunalDecisionHeldLegallyUnreasonable LR.canonicalSZVFWCaseReceipt ≡ false
szvfw-tribunal-decision-not-held-unreasonable = refl

wednesbury-is-not-all-australian-unreasonableness :
  LR.wednesburyFormulationDefinitionallyExhaustsAustralianLegalUnreasonableness
    LR.canonicalLegalReasonablenessBoundary ≡ false
wednesbury-is-not-all-australian-unreasonableness = refl

merits-disagreement-does-not-prove-legal-unreasonableness :
  LR.meritsDisagreementAutomaticallyLegalUnreasonableness
    LR.canonicalLegalReasonablenessBoundary ≡ false
merits-disagreement-does-not-prove-legal-unreasonableness = refl

relevant-considerations-ground-is-not-definitionally-identical :
  LR.relevantConsiderationsGroundDefinitionallyLegalUnreasonableness
    LR.canonicalLegalReasonablenessBoundary ≡ false
relevant-considerations-ground-is-not-definitionally-identical = refl
```

- [ ] **Step 2: Verify structural RED**

Confirm `SensibLawLegalReasonablenessExact.agda` is absent on the branch. If Agda execution is available, observe missing-module failure.

---

### Task 2: Minimal source-bound owner

- [ ] **Step 1: Add three attributed source objects**

Use exact source manifestations:

1. BAILII, `Associated Provincial Picture Houses Ltd v Wednesbury Corporation [1947] EWCA Civ 1`, publication year `1947`, no DOI, source kind `namedSourceKind "court judgment"`, canonical URL `https://www.bailii.org/ew/cases/EWCA/1947/1.html`.
2. High Court of Australia, `Minister for Immigration and Citizenship v Li [2013] HCA 18`, year `2013`, no DOI, court-judgment source kind, canonical HCA case page.
3. High Court of Australia, `Minister for Immigration and Border Protection v SZVFW [2018] HCA 30`, year `2018`, no DOI, court-judgment source kind, canonical HCA case page.

Relationships must state the bounded propositions each manifestation pays and explicitly deny citation-created authority.

- [ ] **Step 2: Add case receipts**

Define:

```agda
record WednesburyCaseReceipt : Set where
  constructor wednesburyCaseReceipt
  field
    source : Source.AttributedSource
    childrenUnder15SundayCondition : Bool
    appealDismissed : Bool
    relevantIrrelevantConsiderationDiscussionLocated : Bool
    noReasonableAuthorityFormulationLocated : Bool

record LiCaseReceipt : Set where
  constructor liCaseReceipt
  field
    source : Source.AttributedSource
    tribunalAdjournmentRefusalInIssue : Bool
    tribunalRefusalHeldLegallyUnreasonable : Bool
    wednesburyNotStartingOrEndPointLocated : Bool
    evidentIntelligibleJustificationLanguageLocated : Bool
    statutoryScopePurposeFrameworkLocated : Bool

record SZVFWCaseReceipt : Set where
  constructor szvfwCaseReceipt
  field
    source : Source.AttributedSource
    tribunalProceedWithoutRespondentsInIssue : Bool
    tribunalDecisionHeldLegallyUnreasonable : Bool
    factDependentLanguageLocated : Bool
    meritsReviewSeparationLocated : Bool
```

Canonical values must reflect the judgments: Wednesbury condition/appeal facts true; Li refusal held unreasonable true; SZVFW tribunal decision held unreasonable false.

- [ ] **Step 3: Add doctrine-separation boundary**

```agda
record LegalReasonablenessBoundary : Set where
  constructor legalReasonablenessBoundary
  field
    meritsDisagreementAutomaticallyLegalUnreasonableness : Bool
    factualErrorAutomaticallyLegalUnreasonableness : Bool
    relevantConsiderationsGroundDefinitionallyLegalUnreasonableness : Bool
    legalUnreasonablenessAutomaticallyJudicialMeritsSubstitution : Bool
    wednesburyFormulationDefinitionallyExhaustsAustralianLegalUnreasonableness : Bool
    harshDecisionAutomaticallyLegalUnreasonableness : Bool
    sourceCitationAutomaticallyCreatesLegalAuthority : Bool
    statutoryContextIndexesReasonablenessInquiry : Bool
    reasonsMayBeFocalPointWithoutBeingWholeInquiry : Bool
```

Canonical values: first seven false, final two true.

- [ ] **Step 4: Add thin generic-adapter receipt**

Define one record indicating that the legal adapter consumes the situated-reasonableness indexing idea but does not identify generic reasonableness with legal reasonableness.

---

### Task 3: Focused validation

**Files:**
- Modify: `DASHI/Core/InstitutionalNormProductionEverything.agda` only if a Law import there would not violate layering; otherwise do not modify Core roll-up.
- Create: `DASHI/Law/SensibLawLegalReasonablenessEverything.agda`
- Modify workflow: `.github/workflows/institutional-norm-production-core.yml` only if keeping Law consumer in same focused workflow is clean; otherwise create a dedicated legal-reasonableness workflow.

- [ ] **Step 1: Add Law roll-up after a structural RED import regression if needed.**
- [ ] **Step 2: Add/extend focused workflow with trust-escape scan and Agda target for the legal regression.**
- [ ] **Step 3: Check exact-head workflow state and keep certification unpaid if no run exists.**

## Plan self-review

- Legal source facts are bounded to exact judgments.
- Wednesbury's dismissed appeal is explicit, avoiding the false implication that the original case found the council unreasonable.
- `Li` broadens the Australian doctrine without treating every listed administrative-law error as definitionally identical.
- `SZVFW` provides a negative application fixture and fact-dependence/merits-review boundary.
- Historical doctrinal lineage does not create moral neutrality, normative legitimacy, or universal reasonableness.
