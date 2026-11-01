# Operational Legality and Institutional Responsibility Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the next generic SensibLaw tranche separating formal prohibition from operational constraint, and cause/permission/authority from responsibility.

**Architecture:** Add two generic Law owners with finite witnesses and no historical actors. `SensibLawOperationalLegalityExact` models enforcement/non-enforcement/regularisation as coordinates distinct from formal rule. `SensibLawInstitutionalResponsibilityExact` keeps cause, permission, authority, knowledge, intent, capacity-to-refuse, role and responsibility distinct without assigning culpability.

**Tech Stack:** Agda; existing `DASHI.Core.QueryIndexedProjectionAdequacyExact`; focused regressions and workflows.

**Spec:** `docs/superpowers/specs/2026-09-13-institutional-norm-production-fragmentation-design.md`

## Global Constraints

- Formal prohibition != effective prevention.
- Non-prosecution != lawfulness.
- Tolerance/non-intervention != formal authorisation.
- Regularisation != moral/legal justification outside the specific legal system.
- Non-enforcement alone does not prove intent, conspiracy, agreement, or causal enablement.
- Distributed causation does not erase causal contribution, but contribution does not by itself settle culpability.
- No historical case or named actor is encoded in these generic owners.
- No Agda GREEN without exact-head execution.

---

### Task 1: Operational legality RED/GREEN

**Files:**
- Create first: `DASHI/Law/SensibLawOperationalLegalityRegression.agda`
- Create after RED: `DASHI/Law/SensibLawOperationalLegalityExact.agda`

**Required regression surfaces:**

```agda
formal-prohibition-does-not-pay-effective-prevention :
  Op.EffectivePreventionQueryAdequate → ⊥

non-prosecution-does-not-establish-lawfulness :
  Op.nonProsecutionAutomaticallyLawful Op.canonicalOperationalLegalityBoundary ≡ false

tolerance-does-not-establish-formal-authorisation :
  Op.toleratedConductAutomaticallyFormallyAuthorised Op.canonicalOperationalLegalityBoundary ≡ false

non-enforcement-does-not-prove-intent :
  Op.nonEnforcementAutomaticallyEstablishesIntent Op.canonicalOperationalLegalityBoundary ≡ false
```

**Finite witness:** two worlds share the same formal prohibition surface but differ on effective operational constraint: one is enforced/prevented, one is not. Use query-indexed adequacy to prove effective prevention does not factor through formal rule alone.

**Enforcement coordinates:** `Detection`, `Investigation`, `Prosecution`, `Sanction`, `NonIntervention`, `Regularisation`, `MaterialSupport`, `OperationalConstraint` represented as distinct fields/carriers.

**Boundary booleans:**

```text
formalProhibitionAutomaticallyEffectivePrevention = false
nonProsecutionAutomaticallyLawful = false
toleratedConductAutomaticallyFormallyAuthorised = false
regularisedConductAutomaticallyJustified = false
nonEnforcementAutomaticallyEstablishesIntent = false
nonEnforcementAutomaticallyEstablishesAgreement = false
materialSupportAutomaticallyFormalAuthorisation = false
formalRuleAndOperationalConstraintAreSeparate = true
```

---

### Task 2: Institutional responsibility RED/GREEN

**Files:**
- Create first: `DASHI/Law/SensibLawInstitutionalResponsibilityRegression.agda`
- Create after RED: `DASHI/Law/SensibLawInstitutionalResponsibilityExact.agda`

**Required regression surfaces:**

```agda
authorisation-does-not-pay-justification :
  Resp.authorisedAutomaticallyJustified Resp.canonicalInstitutionalResponsibilityBoundary ≡ false

small-contribution-does-not-become-zero :
  Resp.smallContributionAutomaticallyNoContribution Resp.canonicalInstitutionalResponsibilityBoundary ≡ false

role-obligation-does-not-settle-responsibility :
  Resp.roleObligationAutomaticallyCompleteResponsibilityAnswer Resp.canonicalInstitutionalResponsibilityBoundary ≡ false
```

Create typed coordinate data/records for cause, permission, authority, enforcement, justification, knowledge, intent, capacity-to-refuse, role, and responsibility. The owner must expose separation, not compute culpability.

Boundary booleans:

```text
causedAutomaticallyAuthorised = false
authorisedAutomaticallyJustified = false
lawfulAutomaticallyMorallyJustified = false
smallContributionAutomaticallyNoContribution = false
distributedCausationAutomaticallyNoCausation = false
roleObligationAutomaticallyCompleteResponsibilityAnswer = false
notPolicyArchitectAutomaticallyNoResponsibility = false
responsibilityRequiresAdditionalCoordinates = true
```

---

### Task 3: Roll-up and focused certification

Create regression-first Law roll-up `SensibLawInstitutionalOperationEverything` importing operational legality and responsibility. Add focused workflow with trust-escape scan and Agda regression targets. Keep historical Israel/settler/conscription and Nazi-bureaucracy examples out of generic owner; they are later source-bound fixtures only.

## Plan self-review

- The operational owner captures the formal-rule/enforcement gap without calling every gap tacit permission.
- The responsibility owner blocks `just doing my job` from automatically erasing causal contribution while equally blocking automatic culpability from role membership alone.
- Historical equivalence is not encoded.
- Source-specific state attribution remains deferred.
