module DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedCausalIdentificationExact where

------------------------------------------------------------------------
-- REVIEWED CAUSAL-IDENTIFICATION MAX-CUT
--
-- CausalIdentificationMaxCut already requires an explicit estimand and
-- identification-family evidence gate. ReviewedWorldEvidenceExact requires an
-- exact human-review receipt/binding plus a separately supplied causal premise.
-- ReviewBindingExact additionally proves that the generic review observation,
-- exact bound factor and reviewed proposition are the same proposition, and
-- that the bound source manifestation is the reviewed bundle.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesCausalIdentificationMaxCutExact as Causal
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceExact as Reviewed
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewBindingExact as Binding
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceWeldExact as Governance
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review

------------------------------------------------------------------------
-- Regression-facing status.
------------------------------------------------------------------------

reviewReceiptRequiredAfterIdentification : Bool
reviewReceiptRequiredAfterIdentification = true

exactReviewBindingRequired : Bool
exactReviewBindingRequired = true

samePropositionReviewBindingRequired : Bool
samePropositionReviewBindingRequired = true

reviewReceiptReplacesIdentificationGate : Bool
reviewReceiptReplacesIdentificationGate = false

reviewedIdentificationCreatesUniversalPartyRanking : Bool
reviewedIdentificationCreatesUniversalPartyRanking = false

southAustraliaNarrativeSourceStillIndependent : Bool
southAustraliaNarrativeSourceStillIndependent = true

------------------------------------------------------------------------
-- Same-object reviewed identification.
------------------------------------------------------------------------

record ReviewedIdentifiedGovernanceCausalBridge
    (case : March.MarchCase)
    (demand : Causal.GovernanceCausalEstimandDemand case) : Set₂ where
  constructor reviewed-identified-governance-causal-bridge
  field
    identifiedBridge :
      Causal.IdentifiedGovernanceCausalBridge case demand

    boundReview :
      Binding.SamePropositionReviewedWorldEvidenceDecision
        case
        (Causal.GovernanceCausalEstimandDemand.observedBundle demand)

    causalPremiseMatches :
      Reviewed.ReviewedWorldEvidenceDecision.CausalPremise
        (Binding.SamePropositionReviewedWorldEvidenceDecision.decision boundReview)
      ≡ Causal.IdentifiedGovernanceCausalBridge.CausalPremise identifiedBridge

    sourceRefsMatch :
      Reviewed.ReviewedWorldEvidenceDecision.sourceRefs
        (Binding.SamePropositionReviewedWorldEvidenceDecision.decision boundReview)
      ≡ Causal.IdentifiedGovernanceCausalBridge.sourceRefs identifiedBridge

    reviewReceiptMatches :
      Review.GenericHumanReviewReceipt.reviewReceiptRef
        (Reviewed.ReviewedWorldEvidenceDecision.genericReview
          (Binding.SamePropositionReviewedWorldEvidenceDecision.decision boundReview))
      ≡ Causal.IdentifiedGovernanceCausalBridge.reviewRef identifiedBridge

    reviewDoesNotReplaceIdentification : Bool
    reviewDoesNotReplaceIdentificationIsFalse :
      reviewDoesNotReplaceIdentification ≡ false

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
      (Binding.SamePropositionReviewedWorldEvidenceDecision.decision
        (boundReview bridge))) ≡ true
reviewedIdentificationRetainsAcceptedOrQualified bridge =
  Binding.acceptedOrQualifiedStillRequired (boundReview bridge)

------------------------------------------------------------------------
-- The preferred transition admission carries both the identification-paid
-- object and the exact same-proposition review wrapper for that same object.
------------------------------------------------------------------------

record ReviewedIdentifiedTransitionAdmission
    (case : March.MarchCase)
    (demand : Causal.GovernanceCausalEstimandDemand case) : Set₂ where
  constructor reviewed-identified-transition-admission
  field
    reviewedBridge :
      ReviewedIdentifiedGovernanceCausalBridge case demand

    identifiedAdmission :
      Causal.IdentifiedTransitionAdmission case demand

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

------------------------------------------------------------------------
-- South Australia remains independently source-gated even after causal
-- identification and exact human review are both paid.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Non-collapse boundaries.
------------------------------------------------------------------------

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
    estimandStillRequiredIsTrue : estimandStillRequired ≡ true
    identificationGateStillRequired : Bool
    identificationGateStillRequiredIsTrue : identificationGateStillRequired ≡ true
    exactReviewBindingNowRequired : Bool
    exactReviewBindingNowRequiredIsTrue : exactReviewBindingNowRequired ≡ true
    samePropositionReviewBindingRequired : Bool
    samePropositionReviewBindingRequiredIsTrue :
      samePropositionReviewBindingRequired ≡ true
    causalPremiseSameObjectChecked : Bool
    causalPremiseSameObjectCheckedIsTrue : causalPremiseSameObjectChecked ≡ true
    southAustraliaSourceStillIndependent : Bool
    southAustraliaSourceStillIndependentIsTrue :
      southAustraliaSourceStillIndependent ≡ true
    universalPartyRankingCreated : Bool
    universalPartyRankingCreatedIsFalse :
      universalPartyRankingCreated ≡ false

open FriendlyjordiesReviewedCausalIdentificationBoundary public

canonicalFriendlyjordiesReviewedCausalIdentificationBoundary :
  FriendlyjordiesReviewedCausalIdentificationBoundary
canonicalFriendlyjordiesReviewedCausalIdentificationBoundary =
  friendlyjordies-reviewed-causal-identification-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
