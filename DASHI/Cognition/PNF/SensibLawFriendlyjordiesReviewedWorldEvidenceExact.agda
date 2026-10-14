module DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceExact where

------------------------------------------------------------------------
-- FRIENDLYJORDIES REVIEWED-WORLD EVIDENCE WELD
--
-- Cross-pollinates the later REAL-MATTER review machinery into the existing
-- Friendlyjordies world-evidence max-cut.  We reuse only the generic human
-- review receipt and exact review-item binding.  The legal evidence-role /
-- normative-order decision is deliberately *not* required here: this owner is
-- about historical/governance evidence, not legal-evidence classification.
--
-- A review receipt + exact binding still does not create causation.  A domain
-- producer must additionally supply the causal/counterfactual premise itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesWorldEvidenceExact as World
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSouthAustraliaGovernanceWeldExact as Base
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as Review

------------------------------------------------------------------------
-- Regression-facing status flags.
------------------------------------------------------------------------

genericHumanReviewReceiptReused : Bool
genericHumanReviewReceiptReused = true

exactReviewItemBindingReused : Bool
exactReviewItemBindingReused = true

legalEvidenceDecisionRequiredForHistoricalReview : Bool
legalEvidenceDecisionRequiredForHistoricalReview = false

reviewMetadataAloneCreatesCausalPremise : Bool
reviewMetadataAloneCreatesCausalPremise = false

reviewedBridgeCreatesUniversalPartyRanking : Bool
reviewedBridgeCreatesUniversalPartyRanking = false

------------------------------------------------------------------------
-- Fixed consumer identity for this review surface.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Proof-relevant reviewed decision.
--
-- The exact review binding already proves accepted/qualified review status.
-- The extra equality prevents a receipt prepared for another consumer from
-- silently paying this governance-world review surface.
------------------------------------------------------------------------

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
    decisionCreatesClaimTruthIsFalse :
      decisionCreatesClaimTruth ≡ false

    decisionCreatesUniversalPartyRanking : Bool
    decisionCreatesUniversalPartyRankingIsFalse :
      decisionCreatesUniversalPartyRanking ≡ false

open ReviewedWorldEvidenceDecision public

------------------------------------------------------------------------
-- Compile a proof-relevant review decision into the existing causal bridge.
-- The premise witness is transported; it is not manufactured by the review
-- receipt or exact binding.
------------------------------------------------------------------------

reviewedDecisionToCausalBridge :
  ∀ {case : March.MarchCase}
    {bundle : World.ExternalWorldFactBundle case} →
  ReviewedWorldEvidenceDecision case bundle →
  World.ReviewedCausalBridge case
reviewedDecisionToCausalBridge decision =
  World.reviewed-causal-bridge
    (sourceRefs decision)
    (Review.GenericHumanReviewReceipt.reviewReceiptRef
      (genericReview decision))
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

------------------------------------------------------------------------
-- CPRS can now reach the existing world-transition evidence compiler through
-- the exact review spine, but only when a decision supplies a causal premise.
------------------------------------------------------------------------

cprsWorldTransitionEvidenceFromReviewedDecision :
  ReviewedWorldEvidenceDecision
    March.cprs2009
    World.cprsExternalWorldBundle →
  Base.WorldTransitionEvidence Base.cprsSourcePaidCase
cprsWorldTransitionEvidenceFromReviewedDecision decision =
  World.cprsWorldTransitionEvidenceFromAdmission
    (reviewedDecisionToTransitionAdmission decision)

------------------------------------------------------------------------
-- South Australia remains dual-gated.  Review can pay the world-evidence side,
-- but the current missing pinned Friendlyjordies M12 source unit is unaffected.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Reused review firewalls from REAL-MATTER.
------------------------------------------------------------------------

existingLegalReviewDoesNotPromoteClaimTruth :
  Review.reviewDecisionPromotesClaimTruth
    Review.canonicalRealMatterReviewBoundary ≡ false
existingLegalReviewDoesNotPromoteClaimTruth = refl

existingLegalReviewDoesNotPromoteApplicability :
  Review.reviewDecisionPromotesApplicability
    Review.canonicalRealMatterReviewBoundary ≡ false
existingLegalReviewDoesNotPromoteApplicability = refl

------------------------------------------------------------------------
-- Hard non-collapse boundaries.
------------------------------------------------------------------------

data GenericReviewReceiptAloneCreatesCausalBridge : Set where
data ExactReviewBindingAloneCreatesCausalPremise : Set where
data HistoricalReviewRequiresLegalEvidenceDecision : Set where
data ReviewedDecisionCreatesUniversalPartyRanking : Set where
data ReviewedDecisionPaysSouthAustraliaNarrativeSource : Set where

genericReviewReceiptAloneDoesNotCreateCausalBridge :
  GenericReviewReceiptAloneCreatesCausalBridge → ⊥
genericReviewReceiptAloneDoesNotCreateCausalBridge ()

exactReviewBindingAloneDoesNotCreateCausalPremise :
  ExactReviewBindingAloneCreatesCausalPremise → ⊥
exactReviewBindingAloneDoesNotCreateCausalPremise ()

historicalReviewDoesNotRequireLegalEvidenceDecision :
  HistoricalReviewRequiresLegalEvidenceDecision → ⊥
historicalReviewDoesNotRequireLegalEvidenceDecision ()

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
    legalEvidenceDecisionRequired : Bool
    legalEvidenceDecisionRequiredIsFalse :
      legalEvidenceDecisionRequired ≡ false
    causalPremiseStillDomainSupplied : Bool
    causalPremiseStillDomainSuppliedIsTrue :
      causalPremiseStillDomainSupplied ≡ true
    southAustraliaNarrativeSourcePaidByReview : Bool
    southAustraliaNarrativeSourcePaidByReviewIsFalse :
      southAustraliaNarrativeSourcePaidByReview ≡ false
    universalPartyRankingCreated : Bool
    universalPartyRankingCreatedIsFalse :
      universalPartyRankingCreated ≡ false

open FriendlyjordiesReviewedWorldEvidenceBoundary public

canonicalFriendlyjordiesReviewedWorldEvidenceBoundary :
  FriendlyjordiesReviewedWorldEvidenceBoundary
canonicalFriendlyjordiesReviewedWorldEvidenceBoundary =
  friendlyjordies-reviewed-world-evidence-boundary
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
