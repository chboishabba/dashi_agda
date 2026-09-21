module DASHI.Education.DigitalESDReviewedScreeningDecisionBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

record CandidateAssessmentReference : Set where
  constructor candidate-assessment-reference
  field
    sourceIdentityReference : String
    assessmentReference : String
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

open CandidateAssessmentReference public

record ScreeningReviewPacket : Set where
  constructor screening-review-packet
  field
    sourceIdentityReference : String
    reviewPacketReference : String
    candidateAssessmentReference : String
    reviewRequired : Bool
    reviewRequiredIsTrue : reviewRequired ≡ true
    packetCreatesScreeningDecision : Bool
    packetCreatesScreeningDecisionIsFalse :
      packetCreatesScreeningDecision ≡ false

open ScreeningReviewPacket public

data ReviewedDecision : Set where
  include : ReviewedDecision
  probable : ReviewedDecision
  exclude : ReviewedDecision
  unresolved : ReviewedDecision

record ExplicitReviewedDecisionOverlay : Set where
  constructor explicit-reviewed-decision-overlay
  field
    sourceIdentityReference : String
    reviewPacketReference : String
    reviewed : Bool
    reviewedIsTrue : reviewed ≡ true
    decision : ReviewedDecision
    reasonCode : String
    reviewerOrProcessReference : String
    decisionTimestamp : String
    supersedesDecisionReference : String

open ExplicitReviewedDecisionOverlay public

record AuthoritativeLedgerUpdateReceipt : Set where
  constructor authoritative-ledger-update-receipt
  field
    inputLedgerReference : String
    inputLedgerSha256 : String
    decisionOverlayReference : String
    decisionOverlaySha256 : String
    outputLedgerReference : String
    outputLedgerSha256 : String
    inputRecordCountReference : String
    outputRecordCountReference : String
    appliedDecisionCountReference : String
    denominatorPreserved : Bool
    denominatorPreservedIsTrue : denominatorPreserved ≡ true
    candidateAssessmentAutoPromoted : Bool
    candidateAssessmentAutoPromotedIsFalse :
      candidateAssessmentAutoPromoted ≡ false
    paretoPriorityAutoPromoted : Bool
    paretoPriorityAutoPromotedIsFalse :
      paretoPriorityAutoPromoted ≡ false

open AuthoritativeLedgerUpdateReceipt public

record ReviewedScreeningDecisionBoundary : Set where
  constructor reviewed-screening-decision-boundary
  field
    candidateAssessmentIsAdvisory : Bool
    candidateAssessmentIsAdvisoryIsTrue :
      candidateAssessmentIsAdvisory ≡ true
    reviewPacketIsAdvisory : Bool
    reviewPacketIsAdvisoryIsTrue :
      reviewPacketIsAdvisory ≡ true
    explicitReviewedOverlayIsOnlyAuthorityChangingStep : Bool
    explicitReviewedOverlayIsOnlyAuthorityChangingStepIsTrue :
      explicitReviewedOverlayIsOnlyAuthorityChangingStep ≡ true
    authoritativeLedgerPreservesDenominator : Bool
    authoritativeLedgerPreservesDenominatorIsTrue :
      authoritativeLedgerPreservesDenominator ≡ true
    unmentionedRowsRemainUnchanged : Bool
    unmentionedRowsRemainUnchangedIsTrue :
      unmentionedRowsRemainUnchanged ≡ true
    candidateAssessmentMayAutoPromote : Bool
    candidateAssessmentMayAutoPromoteIsFalse :
      candidateAssessmentMayAutoPromote ≡ false
    paretoPriorityMayAutoPromote : Bool
    paretoPriorityMayAutoPromoteIsFalse :
      paretoPriorityMayAutoPromote ≡ false

open ReviewedScreeningDecisionBoundary public

canonicalReviewedScreeningDecisionBoundary :
  ReviewedScreeningDecisionBoundary
canonicalReviewedScreeningDecisionBoundary =
  reviewed-screening-decision-boundary
    true refl true refl true refl true refl true refl false refl false refl

data CandidateAssessmentChangesAuthoritativeLedger : Set where
data ReviewPacketChangesAuthoritativeLedger : Set where
data UnreviewedOverlayChangesAuthoritativeLedger : Set where
data ParetoPriorityChangesAuthoritativeLedger : Set where
data ReviewedOverlayChangesSourceTruth : Set where
data ReviewedOverlayCreatesSourceAuditAdmission : Set where

candidateAssessmentDoesNotChangeAuthoritativeLedger :
  CandidateAssessmentChangesAuthoritativeLedger → ⊥
candidateAssessmentDoesNotChangeAuthoritativeLedger ()

reviewPacketDoesNotChangeAuthoritativeLedger :
  ReviewPacketChangesAuthoritativeLedger → ⊥
reviewPacketDoesNotChangeAuthoritativeLedger ()

unreviewedOverlayDoesNotChangeAuthoritativeLedger :
  UnreviewedOverlayChangesAuthoritativeLedger → ⊥
unreviewedOverlayDoesNotChangeAuthoritativeLedger ()

paretoPriorityDoesNotChangeAuthoritativeLedger :
  ParetoPriorityChangesAuthoritativeLedger → ⊥
paretoPriorityDoesNotChangeAuthoritativeLedger ()

reviewedOverlayDoesNotChangeSourceTruth :
  ReviewedOverlayChangesSourceTruth → ⊥
reviewedOverlayDoesNotChangeSourceTruth ()

reviewedOverlayDoesNotCreateSourceAuditAdmission :
  ReviewedOverlayCreatesSourceAuditAdmission → ⊥
reviewedOverlayDoesNotCreateSourceAuditAdmission ()
