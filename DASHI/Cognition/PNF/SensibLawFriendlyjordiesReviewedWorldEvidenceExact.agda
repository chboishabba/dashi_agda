module DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.HumanReviewCore as Review
import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesWorldEvidenceExact as World
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceWeldExact as Base

genericHumanReviewReceiptReused : Bool
genericHumanReviewReceiptReused = true

exactReviewItemBindingReused : Bool
exactReviewItemBindingReused = true

reviewMetadataAloneCreatesCausalPremise : Bool
reviewMetadataAloneCreatesCausalPremise = false

reviewedBridgeCreatesUniversalPartyRanking : Bool
reviewedBridgeCreatesUniversalPartyRanking = false

worldEvidenceReviewConsumerRef : String
worldEvidenceReviewConsumerRef =
  "consumer:friendlyjordies:governance-world-evidence"

data HistoricalReviewScope : Set where
  causalAttribution : HistoricalReviewScope
  counterfactualTrajectory : HistoricalReviewScope
  operationalInterpretation : HistoricalReviewScope

scopeEstablishesPartyCause : HistoricalReviewScope → Bool
scopeEstablishesPartyCause causalAttribution = true
scopeEstablishesPartyCause counterfactualTrajectory = false
scopeEstablishesPartyCause operationalInterpretation = false

scopeEstablishesCounterfactual : HistoricalReviewScope → Bool
scopeEstablishesCounterfactual causalAttribution = false
scopeEstablishesCounterfactual counterfactualTrajectory = true
scopeEstablishesCounterfactual operationalInterpretation = false

record ReviewedWorldEvidenceDecision
    (case : March.MarchCase)
    (bundle : World.ExternalWorldFactBundle case) : Set₁ where
  constructor reviewed-world-evidence-decision
  field
    genericReview : Review.GenericHumanReviewReceipt
    exactReviewBinding : Review.ExactReviewItemBinding
    bundleRef : String
    propositionRef : String
    sourceRefs : List String
    scope : HistoricalReviewScope

    consumerBindingMatches :
      Review.ExactReviewItemBinding.consumerRef exactReviewBinding
      ≡ worldEvidenceReviewConsumerRef
    sourceManifestationMatchesBundle :
      Review.ExactReviewItemBinding.sourceManifestationRef exactReviewBinding
      ≡ bundleRef
    candidateFactorMatchesProposition :
      Review.ExactReviewItemBinding.candidateFactorRef exactReviewBinding
      ≡ propositionRef
    reviewObservationMatchesProposition :
      Review.GenericHumanReviewReceipt.observationRef genericReview
      ≡ propositionRef

    reviewItemRef : String
    reviewItemRefMatches :
      reviewItemRef
      ≡ Review.GenericHumanReviewReceipt.reviewItemRef genericReview

    CausalPremise : Set
    causalPremiseWitness : CausalPremise
    sameCase : March.MarchCase
    sameCaseMatches : sameCase ≡ case

    reviewMetadataCreatesCausalPremise : Bool
    reviewMetadataCreatesCausalPremiseIsFalse :
      reviewMetadataCreatesCausalPremise ≡ false
    decisionCreatesClaimTruth : Bool
    decisionCreatesClaimTruthIsFalse : decisionCreatesClaimTruth ≡ false
    decisionCreatesUniversalPartyRanking : Bool
    decisionCreatesUniversalPartyRankingIsFalse :
      decisionCreatesUniversalPartyRanking ≡ false

open ReviewedWorldEvidenceDecision public

reviewedDecisionRetainsAcceptedOrQualified :
  ∀ {case : March.MarchCase}
    {bundle : World.ExternalWorldFactBundle case}
    (decision : ReviewedWorldEvidenceDecision case bundle) →
  Review.ExactReviewItemBinding.acceptedOrQualified
    (exactReviewBinding decision) ≡ true
reviewedDecisionRetainsAcceptedOrQualified decision =
  Review.ExactReviewItemBinding.acceptedOrQualifiedIsTrue
    (exactReviewBinding decision)

reviewedDecisionToCausalBridge :
  ∀ {case : March.MarchCase}
    {bundle : World.ExternalWorldFactBundle case} →
  ReviewedWorldEvidenceDecision case bundle →
  World.ReviewedCausalBridge case
reviewedDecisionToCausalBridge decision =
  World.reviewed-causal-bridge
    (sourceRefs decision)
    (Review.GenericHumanReviewReceipt.reviewReceiptRef (genericReview decision))
    (CausalPremise decision)
    (causalPremiseWitness decision)
    (sameCase decision)
    (sameCaseMatches decision)
    (scopeEstablishesPartyCause (scope decision))
    (scopeEstablishesCounterfactual (scope decision))

reviewedDecisionToTransitionAdmission :
  ∀ {case : March.MarchCase}
    {bundle : World.ExternalWorldFactBundle case} →
  ReviewedWorldEvidenceDecision case bundle →
  World.TransitionAdmission case bundle
reviewedDecisionToTransitionAdmission decision =
  World.transition-admission
    (reviewedDecisionToCausalBridge decision)
    true refl
    false refl

cprsWorldTransitionEvidenceFromReviewedDecision :
  ReviewedWorldEvidenceDecision
    March.cprs2009
    World.cprsExternalWorldBundle →
  Base.WorldTransitionEvidence Base.cprsSourcePaidCase
cprsWorldTransitionEvidenceFromReviewedDecision decision =
  World.cprsWorldTransitionEvidenceFromAdmission
    (reviewedDecisionToTransitionAdmission decision)

record SouthAustraliaReviewedDualGate : Set₁ where
  constructor south-australia-reviewed-dual-gate
  field
    sourceRecovery : Base.SouthAustraliaTransitionPrerequisite
    reviewedDecision :
      ReviewedWorldEvidenceDecision
        March.southAustraliaRenewables
        World.southAustraliaExternalWorldBundle

open SouthAustraliaReviewedDualGate public

southAustraliaReviewedDualGateCurrentlyBlocked :
  SouthAustraliaReviewedDualGate → ⊥
southAustraliaReviewedDualGateCurrentlyBlocked gate =
  Base.southAustraliaTransitionPrerequisiteCurrentlyImpossible
    (sourceRecovery gate)

humanReviewCoreDoesNotCreateClaimTruth :
  Review.HumanReviewCoreBoundary.reviewCreatesClaimTruth
    Review.canonicalHumanReviewCoreBoundary ≡ false
humanReviewCoreDoesNotCreateClaimTruth = refl

humanReviewCoreDoesNotCreateCausalIdentification :
  Review.HumanReviewCoreBoundary.reviewCreatesCausalIdentification
    Review.canonicalHumanReviewCoreBoundary ≡ false
humanReviewCoreDoesNotCreateCausalIdentification = refl

data GenericReviewReceiptAloneCreatesCausalBridge : Set where
data ExactReviewBindingAloneCreatesCausalPremise : Set where
data ReviewedDecisionCreatesUniversalPartyRanking : Set where
data ReviewedDecisionPaysSouthAustraliaNarrativeSource : Set where

genericReviewReceiptAloneDoesNotCreateCausalBridge :
  GenericReviewReceiptAloneCreatesCausalBridge → ⊥
genericReviewReceiptAloneDoesNotCreateCausalBridge ()

exactReviewBindingAloneDoesNotCreateCausalPremise :
  ExactReviewBindingAloneCreatesCausalPremise → ⊥
exactReviewBindingAloneDoesNotCreateCausalPremise ()

reviewedDecisionDoesNotCreateUniversalPartyRanking :
  ReviewedDecisionCreatesUniversalPartyRanking → ⊥
reviewedDecisionDoesNotCreateUniversalPartyRanking ()

reviewedDecisionDoesNotPaySouthAustraliaNarrativeSource :
  ReviewedDecisionPaysSouthAustraliaNarrativeSource → ⊥
reviewedDecisionDoesNotPaySouthAustraliaNarrativeSource ()

record FriendlyjordiesReviewedWorldEvidenceBoundary : Set where
  constructor friendlyjordies-reviewed-world-evidence-boundary
  field
    genericReviewReceiptReused : Bool
    genericReviewReceiptReusedIsTrue : genericReviewReceiptReused ≡ true
    exactReviewBindingReused : Bool
    exactReviewBindingReusedIsTrue : exactReviewBindingReused ≡ true
    exactSourceManifestationRequired : Bool
    exactSourceManifestationRequiredIsTrue : exactSourceManifestationRequired ≡ true
    propositionIdentityRequired : Bool
    propositionIdentityRequiredIsTrue : propositionIdentityRequired ≡ true
    causalPremiseStillDomainSupplied : Bool
    causalPremiseStillDomainSuppliedIsTrue : causalPremiseStillDomainSupplied ≡ true
    southAustraliaNarrativeSourcePaidByReview : Bool
    southAustraliaNarrativeSourcePaidByReviewIsFalse :
      southAustraliaNarrativeSourcePaidByReview ≡ false
    universalPartyRankingCreated : Bool
    universalPartyRankingCreatedIsFalse : universalPartyRankingCreated ≡ false

open FriendlyjordiesReviewedWorldEvidenceBoundary public

canonicalFriendlyjordiesReviewedWorldEvidenceBoundary :
  FriendlyjordiesReviewedWorldEvidenceBoundary
canonicalFriendlyjordiesReviewedWorldEvidenceBoundary =
  friendlyjordies-reviewed-world-evidence-boundary
    true refl true refl true refl true refl true refl false refl false refl
