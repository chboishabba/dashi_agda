module DASHI.Core.EvidenceObligationAuthoritySeparationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.DisagreementFourViewBoundary as Four
import DASHI.Promotion.AuthorityGateCore as Authority

------------------------------------------------------------------------
-- Evidence polarity, proof-obligation discharge, and authority are distinct.
--
-- This module reuses AuthorityGateCore rather than introducing a second
-- authority algebra.  A supported claim may still have open obligations; even
-- a positively supported claim whose technical obligations are discharged
-- cannot bypass a closed authority gate.  External/domain authority remains a
-- separate accepted-bridge problem.
--
-- This module intentionally does NOT define per-axis completeness.  Incoming
-- PR #582 owns that theorem layer in DASHI.Core.RequiredAxisSupportSquareExact
-- (AxisEvidenceFamily, RequiredAxesResolved, MissingRequiredAxis, and the
-- non-compensation theorem).  On stack convergence, an inhabited
-- RequiredAxesResolved proof is a natural producer for obligationsDischarged.
------------------------------------------------------------------------

data ObligationStatus : Set where
  obligationsOpen : ObligationStatus
  obligationsDischarged : ObligationStatus

record GovernedClaimState : Set where
  constructor governedClaimState
  field
    evidence : Four.PolarAssessment
    obligations : ObligationStatus
    authorityGate : Authority.PromotionGate

open GovernedClaimState public

closedGovernedClaimState :
  Four.PolarAssessment →
  ObligationStatus →
  Authority.AuthorityKind →
  String →
  GovernedClaimState
closedGovernedClaimState evidence obligations kind label =
  governedClaimState evidence obligations (Authority.mkClosedGate kind label)

localPromotion : GovernedClaimState → Bool
localPromotion state = Authority.promoted (authorityGate state)

localPromotionIsFalse :
  (state : GovernedClaimState) →
  localPromotion state ≡ false
localPromotionIsFalse state = Authority.promotedIsFalse (authorityGate state)

supportOnlyOpen : GovernedClaimState
supportOnlyOpen =
  closedGovernedClaimState
    (Four.assess true false)
    obligationsOpen
    Authority.theoremAuthority
    "supported claim with open obligations"

supportOnlyDischarged : GovernedClaimState
supportOnlyDischarged =
  closedGovernedClaimState
    (Four.assess true false)
    obligationsDischarged
    Authority.theoremAuthority
    "supported claim with discharged technical obligations"

conflictDischarged : GovernedClaimState
conflictDischarged =
  closedGovernedClaimState
    (Four.assess true true)
    obligationsDischarged
    Authority.theoremAuthority
    "conflicting claim with discharged technical obligations"

supportDoesNotDischargeObligations :
  obligations supportOnlyOpen ≡ obligationsOpen
supportDoesNotDischargeObligations = refl

dischargedObligationsDoNotOpenAuthorityGate :
  localPromotion supportOnlyDischarged ≡ false
dischargedObligationsDoNotOpenAuthorityGate =
  localPromotionIsFalse supportOnlyDischarged

conflictDoesNotOpenAuthorityGate :
  localPromotion conflictDischarged ≡ false
conflictDoesNotOpenAuthorityGate =
  localPromotionIsFalse conflictDischarged

supportAndDischargeCannotBypassClosedAuthority :
  (state : GovernedClaimState) →
  evidence state ≡ Four.assess true false →
  obligations state ≡ obligationsDischarged →
  localPromotion state ≡ false
supportAndDischargeCannotBypassClosedAuthority state support discharged =
  localPromotionIsFalse state

record EvidenceObligationAuthorityBoundary : Set where
  field
    evidenceEqualsObligationDischargeClaimed : Bool
    obligationDischargeEqualsAuthorityClaimed : Bool
    authorityEqualsEvidenceClaimed : Bool
    conflictOpensAuthorityClaimed : Bool
    existingAuthorityGateCoreReused : Bool

canonicalEvidenceObligationAuthorityBoundary :
  EvidenceObligationAuthorityBoundary
canonicalEvidenceObligationAuthorityBoundary = record
  { evidenceEqualsObligationDischargeClaimed = false
  ; obligationDischargeEqualsAuthorityClaimed = false
  ; authorityEqualsEvidenceClaimed = false
  ; conflictOpensAuthorityClaimed = false
  ; existingAuthorityGateCoreReused = true
  }
