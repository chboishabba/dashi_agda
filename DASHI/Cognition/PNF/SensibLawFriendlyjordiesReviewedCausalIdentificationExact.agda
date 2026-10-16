module DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedCausalIdentificationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.HumanReviewCore as Review
import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesCausalIdentificationMaxCutExact as Causal
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceExact as Reviewed
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceWeldExact as Governance

reviewReceiptRequiredAfterIdentification : Bool
reviewReceiptRequiredAfterIdentification = true

exactReviewBindingRequired : Bool
exactReviewBindingRequired = true

reviewReceiptReplacesIdentificationGate : Bool
reviewReceiptReplacesIdentificationGate = false

identificationGateReplacesReviewReceipt : Bool
identificationGateReplacesReviewReceipt = false

reviewedIdentificationCreatesUniversalPartyRanking : Bool
reviewedIdentificationCreatesUniversalPartyRanking = false

southAustraliaNarrativeSourceStillIndependent : Bool
southAustraliaNarrativeSourceStillIndependent = true

record ReviewedIdentifiedGovernanceCausalBridge
    (case : March.MarchCase)
    (demand : Causal.GovernanceCausalEstimandDemand case) : Set₂ where
  constructor reviewed-identified-governance-causal-bridge
  field
    identifiedBridge :
      Causal.IdentifiedGovernanceCausalBridge case demand
    reviewDecision :
      Reviewed.ReviewedWorldEvidenceDecision
        case
        (Causal.GovernanceCausalEstimandDemand.observedBundle demand)

    causalPremiseMatches :
      Reviewed.ReviewedWorldEvidenceDecision.CausalPremise reviewDecision
      ≡ Causal.IdentifiedGovernanceCausalBridge.CausalPremise identifiedBridge
    sourceRefsMatch :
      Reviewed.ReviewedWorldEvidenceDecision.sourceRefs reviewDecision
      ≡ Causal.IdentifiedGovernanceCausalBridge.sourceRefs identifiedBridge
    reviewReceiptMatches :
      Review.GenericHumanReviewReceipt.reviewReceiptRef
        (Reviewed.ReviewedWorldEvidenceDecision.genericReview reviewDecision)
      ≡ Causal.IdentifiedGovernanceCausalBridge.reviewRef identifiedBridge

    reviewDoesNotReplaceIdentification : Bool
    reviewDoesNotReplaceIdentificationIsFalse :
      reviewDoesNotReplaceIdentification ≡ false
    identificationDoesNotReplaceReview : Bool
    identificationDoesNotReplaceReviewIsFalse :
      identificationDoesNotReplaceReview ≡ false
    createsUniversalPartyRanking : Bool
    createsUniversalPartyRankingIsFalse :
      createsUniversalPartyRanking ≡ false

open ReviewedIdentifiedGovernanceCausalBridge public

reviewedIdentificationRetainsAcceptedOrQualified :
  ∀ {case : March.MarchCase}
    {demand : Causal.GovernanceCausalEstimandDemand case}
    (bridge : ReviewedIdentifiedGovernanceCausalBridge case demand) →
  Review.ExactReviewItemBinding.acceptedOrQualified
    (Reviewed.ReviewedWorldEvidenceDecision.exactReviewBinding
      (reviewDecision bridge)) ≡ true
reviewedIdentificationRetainsAcceptedOrQualified bridge =
  Reviewed.reviewedDecisionRetainsAcceptedOrQualified (reviewDecision bridge)

record ReviewedIdentifiedTransitionAdmission
    (case : March.MarchCase)
    (demand : Causal.GovernanceCausalEstimandDemand case) : Set₂ where
  constructor reviewed-identified-transition-admission
  field
    reviewedBridge : ReviewedIdentifiedGovernanceCausalBridge case demand
    identifiedAdmission : Causal.IdentifiedTransitionAdmission case demand
    identifiedBridgeMatchesAdmission :
      Causal.IdentifiedTransitionAdmission.identifiedBridge identifiedAdmission
      ≡ ReviewedIdentifiedGovernanceCausalBridge.identifiedBridge reviewedBridge

open ReviewedIdentifiedTransitionAdmission public

cprsWorldTransitionEvidenceFromReviewedIdentification :
  ReviewedIdentifiedTransitionAdmission
    March.cprs2009
    Causal.cprsCausalEstimandDemand →
  Governance.WorldTransitionEvidence Governance.cprsSourcePaidCase
cprsWorldTransitionEvidenceFromReviewedIdentification admission =
  Causal.cprsWorldTransitionEvidenceFromIdentifiedAdmission
    (identifiedAdmission admission)

record SouthAustraliaReviewedIdentifiedGate : Set₂ where
  constructor south-australia-reviewed-identified-gate
  field
    sourceRecovery : Governance.SouthAustraliaTransitionPrerequisite
    reviewedAdmission :
      ReviewedIdentifiedTransitionAdmission
        March.southAustraliaRenewables
        Causal.southAustraliaCausalEstimandDemand

open SouthAustraliaReviewedIdentifiedGate public

southAustraliaReviewedIdentifiedGateCurrentlyBlocked :
  SouthAustraliaReviewedIdentifiedGate → ⊥
southAustraliaReviewedIdentifiedGateCurrentlyBlocked gate =
  Governance.southAustraliaTransitionPrerequisiteCurrentlyImpossible
    (sourceRecovery gate)

data HumanReviewReplacesIdentificationEvidence : Set where
data IdentificationEvidenceReplacesHumanReview : Set where
data ReviewedIdentificationPaysMissingNarrativeSource : Set where
data ReviewedIdentificationCreatesUniversalRanking : Set where

humanReviewDoesNotReplaceIdentificationEvidence :
  HumanReviewReplacesIdentificationEvidence → ⊥
humanReviewDoesNotReplaceIdentificationEvidence ()

identificationEvidenceDoesNotReplaceHumanReview :
  IdentificationEvidenceReplacesHumanReview → ⊥
identificationEvidenceDoesNotReplaceHumanReview ()

reviewedIdentificationDoesNotPayMissingNarrativeSource :
  ReviewedIdentificationPaysMissingNarrativeSource → ⊥
reviewedIdentificationDoesNotPayMissingNarrativeSource ()

reviewedIdentificationDoesNotCreateUniversalRanking :
  ReviewedIdentificationCreatesUniversalRanking → ⊥
reviewedIdentificationDoesNotCreateUniversalRanking ()

record FriendlyjordiesReviewedCausalIdentificationBoundary : Set where
  constructor friendlyjordies-reviewed-causal-identification-boundary
  field
    estimandStillRequired : Bool
    identificationGateStillRequired : Bool
    exactReviewBindingNowRequired : Bool
    causalPremiseSameObjectChecked : Bool
    sourceRefsSameObjectChecked : Bool
    reviewReceiptSameObjectChecked : Bool
    southAustraliaSourceStillIndependent : Bool
    universalPartyRankingCreated : Bool

canonicalFriendlyjordiesReviewedCausalIdentificationBoundary :
  FriendlyjordiesReviewedCausalIdentificationBoundary
canonicalFriendlyjordiesReviewedCausalIdentificationBoundary =
  friendlyjordies-reviewed-causal-identification-boundary
    true true true true true true true false
