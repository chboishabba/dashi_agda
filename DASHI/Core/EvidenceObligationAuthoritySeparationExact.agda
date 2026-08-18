module DASHI.Core.EvidenceObligationAuthoritySeparationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.DisagreementFourViewBoundary as Four

------------------------------------------------------------------------
-- Evidence polarity, proof-obligation discharge, and authority are distinct.
--
-- A supported claim may still have open obligations.  A fully discharged
-- technical claim may still lack authority for a downstream action.  Authority
-- alone cannot manufacture evidence.  Promotion therefore consumes all three
-- coordinates explicitly rather than treating any one as a proxy for the rest.
------------------------------------------------------------------------

data ObligationStatus : Set where
  obligationsOpen : ObligationStatus
  obligationsDischarged : ObligationStatus

data AuthorityStatus : Set where
  authorityDenied : AuthorityStatus
  authorityGranted : AuthorityStatus

record GovernedClaimState : Set where
  constructor governedClaimState
  field
    evidence : Four.PolarAssessment
    obligations : ObligationStatus
    authority : AuthorityStatus

open GovernedClaimState public

promotionGate : GovernedClaimState → Bool
promotionGate
  (governedClaimState (Four.assess true false)
                      obligationsDischarged
                      authorityGranted) = true
promotionGate _ = false

supportOnlyOpenDenied : GovernedClaimState
supportOnlyOpenDenied =
  governedClaimState
    (Four.assess true false)
    obligationsOpen
    authorityDenied

supportOnlyDischargedDenied : GovernedClaimState
supportOnlyDischargedDenied =
  governedClaimState
    (Four.assess true false)
    obligationsDischarged
    authorityDenied

ignoranceDischargedGranted : GovernedClaimState
ignoranceDischargedGranted =
  governedClaimState
    (Four.assess false false)
    obligationsDischarged
    authorityGranted

conflictDischargedGranted : GovernedClaimState
conflictDischargedGranted =
  governedClaimState
    (Four.assess true true)
    obligationsDischarged
    authorityGranted

supportedDischargedGranted : GovernedClaimState
supportedDischargedGranted =
  governedClaimState
    (Four.assess true false)
    obligationsDischarged
    authorityGranted

supportDoesNotDischargeObligations :
  promotionGate supportOnlyOpenDenied ≡ false
supportDoesNotDischargeObligations = refl

dischargedObligationsDoNotGrantAuthority :
  promotionGate supportOnlyDischargedDenied ≡ false
dischargedObligationsDoNotGrantAuthority = refl

authorityDoesNotManufactureEvidence :
  promotionGate ignoranceDischargedGranted ≡ false
authorityDoesNotManufactureEvidence = refl

conflictDoesNotBecomeAffirmativePromotion :
  promotionGate conflictDischargedGranted ≡ false
conflictDoesNotBecomeAffirmativePromotion = refl

supportedDischargedAuthorizedPromotes :
  promotionGate supportedDischargedGranted ≡ true
supportedDischargedAuthorizedPromotes = refl

record EvidenceObligationAuthorityBoundary : Set where
  field
    evidenceEqualsObligationDischargeClaimed : Bool
    obligationDischargeEqualsAuthorityClaimed : Bool
    authorityEqualsEvidenceClaimed : Bool
    conflictPromotesAffirmativelyClaimed : Bool
    allCoordinatesRequiredForPromotion : Bool

canonicalEvidenceObligationAuthorityBoundary :
  EvidenceObligationAuthorityBoundary
canonicalEvidenceObligationAuthorityBoundary = record
  { evidenceEqualsObligationDischargeClaimed = false
  ; obligationDischargeEqualsAuthorityClaimed = false
  ; authorityEqualsEvidenceClaimed = false
  ; conflictPromotesAffirmativelyClaimed = false
  ; allCoordinatesRequiredForPromotion = true
  }
