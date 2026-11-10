module DASHI.Law.SensibLawWoogarooPriorActionAuditScope20261110Exact where

-- Separate original Commonwealth 2025 audit: EPBC 2014/7306
-- Springview Village One, Stockland Development Pty Limited.
-- National EPA audit-program summary (2025 subsection):
-- https://www.nationalepa.gov.au/epbc/compliance/audits
-- Scope conditions 1,2,3,4,5,6,7A,7B,7C,8,9;
-- seven assessed compliant; four marked not applicable.
--
-- This is NOT a site/polygon-clearing certificate, legal advice,
-- nor a finding about the distinct EPBC 2019/8575 approval.
-- Classification by individual condition is NOT supplied in this
-- summary and MUST NOT be fabricated.

open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data ActionScope : Set where
  priorSpringview20147306 : ActionScope
  currentSpringview20198575 : ActionScope

-- A receipt for one action cannot be silently promoted to the other.
-- SameAction represents exact identity of the action being audited,
-- not ecological overlap, shared developer or common land parcel.
data SameAction : ActionScope → ActionScope → Set where
  sameAction : {a : ActionScope} → SameAction a a

originalPriorAuditIsNotCurrentApprovalAudit :
  SameAction priorSpringview20147306 currentSpringview20198575 → ⊥
originalPriorAuditIsNotCurrentApprovalAudit ()

record GovernmentAuditSummary : Set where
  constructor government-audit-summary
  field
    scope : ActionScope
    assessedCompliant : Nat
    assessedNotApplicable : Nat
    assessedNoncompliant : Nat
    assessedTotal : Nat
open GovernmentAuditSummary public

original2025AuditSummary : GovernmentAuditSummary
original2025AuditSummary =
  government-audit-summary priorSpringview20147306 7 4 0 11

originalAuditCategorySum :
  assessedCompliant original2025AuditSummary +
  assessedNotApplicable original2025AuditSummary +
  assessedNoncompliant original2025AuditSummary ≡
  assessedTotal original2025AuditSummary
originalAuditCategorySum = refl

originalAuditCaseIdentity :
  scope original2025AuditSummary ≡ priorSpringview20147306
originalAuditCaseIdentity = refl

-- No equivalence between "not applicable" and "compliant" is supplied.
-- No original 7.6ha exclusion geometry, past actual-clearing polygon,
-- current July Issue F footprint join, or current decision proof is
-- constructed from this summary. Those remain external source gates.
