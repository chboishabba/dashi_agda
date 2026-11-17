module DASHI.Cognition.PNF.SensibLawFriendlyjordiesAttributionCausalMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.FriendlyjordiesGovernanceQuestionExact as March
import DASHI.Cognition.PNF.SensibLawChronologyContestationSpineExact as Contest
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesNarrativeGovernanceWeldExact as Weld
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesCompetingNarrativeExact as Competing
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesCausalIdentificationMaxCutExact as Causal
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedWorldEvidenceExact as Review
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesReviewedCausalIdentificationExact as Reviewed

------------------------------------------------------------------------
-- Attribution is a first-class coordinate all the way through causal review.
------------------------------------------------------------------------

attributionRetainedThroughCausalReview : Bool
attributionRetainedThroughCausalReview = true

reviewedCausalBridgeFlattensAttribution : Bool
reviewedCausalBridgeFlattensAttribution = false

corroborationCreatesCanonicalTruth : Bool
corroborationCreatesCanonicalTruth = false

worldFactsRewriteSourceNarrative : Bool
worldFactsRewriteSourceNarrative = false

reviewedLocalBridgeCreatesUniversalPartyRanking : Bool
reviewedLocalBridgeCreatesUniversalPartyRanking = false

record AttributionPreservingReviewedGovernanceBridge
    {root : Contest.PropositionRoot}
    (leaf : Contest.ClaimLeaf root)
    (case : March.MarchCase)
    (demand : Causal.GovernanceCausalEstimandDemand case) : Set₂ where
  constructor attribution-preserving-reviewed-governance-bridge
  field
    rootedClaim : Weld.RootedTraceClaim root leaf
    attribution : Competing.AttributionWrapper
    reviewedCausal :
      Reviewed.ReviewedIdentifiedGovernanceCausalBridge case demand

    outerSpeakerMatchesClaimSpeaker :
      Competing.AttributionWrapper.outerSpeakerRef attribution
      ≡ Contest.ClaimLeaf.speakerRef leaf
    attributedPropositionMatchesRoot :
      Competing.AttributionWrapper.propositionRef attribution
      ≡ Contest.PropositionRoot.propositionRef root
    reviewedPropositionMatchesAttribution :
      Review.ReviewedWorldEvidenceDecision.propositionRef
        (Reviewed.reviewDecision reviewedCausal)
      ≡ Competing.AttributionWrapper.propositionRef attribution
    sourceRevisionMatchesAttribution :
      Weld.RootedTraceClaim.sourceRevisionRef rootedClaim
      ≡ Competing.AttributionWrapper.sourceRevisionRef attribution

    attributionStillCandidate : Bool
    attributionStillCandidateIsTrue : attributionStillCandidate ≡ true
    attributionCreatesUnderlyingTruth : Bool
    attributionCreatesUnderlyingTruthIsFalse :
      attributionCreatesUnderlyingTruth ≡ false
    corroborationCreatesCanonicalStory : Bool
    corroborationCreatesCanonicalStoryIsFalse :
      corroborationCreatesCanonicalStory ≡ false
    reviewedBridgeRewritesNarrative : Bool
    reviewedBridgeRewritesNarrativeIsFalse :
      reviewedBridgeRewritesNarrative ≡ false
    createsUniversalPartyRanking : Bool
    createsUniversalPartyRankingIsFalse :
      createsUniversalPartyRanking ≡ false

open AttributionPreservingReviewedGovernanceBridge public

------------------------------------------------------------------------
-- Exact source attribution does not collapse to the embedded proposition.
-- Existing SensibLaw non-collapse theorem remains the authority for that edge.
------------------------------------------------------------------------

existingAttributionDoesNotCollapseToTruth :
  Competing.AttributionWrapperIsUnderlyingTruth → ⊥
existingAttributionDoesNotCollapseToTruth =
  Competing.attributionDoesNotCollapseToUnderlyingTruth

data ReviewedCausalEvidenceFlattensAttribution : Set where
data CorroborationCreatesCanonicalStory : Set where
data WorldEvidenceRewritesSourceStatement : Set where
data LocalReviewedBridgeCreatesUniversalPartyRanking : Set where

reviewedCausalEvidenceDoesNotFlattenAttribution :
  ReviewedCausalEvidenceFlattensAttribution → ⊥
reviewedCausalEvidenceDoesNotFlattenAttribution ()

corroborationDoesNotCreateCanonicalStory :
  CorroborationCreatesCanonicalStory → ⊥
corroborationDoesNotCreateCanonicalStory ()

worldEvidenceDoesNotRewriteSourceStatement :
  WorldEvidenceRewritesSourceStatement → ⊥
worldEvidenceDoesNotRewriteSourceStatement ()

localReviewedBridgeDoesNotCreateUniversalPartyRanking :
  LocalReviewedBridgeCreatesUniversalPartyRanking → ⊥
localReviewedBridgeDoesNotCreateUniversalPartyRanking ()

record FriendlyjordiesAttributionCausalBoundary : Set where
  constructor friendlyjordies-attribution-causal-boundary
  field
    sourceSpeakerRetained : Bool
    attributedAuthorityRetained : Bool
    embeddedPropositionRetained : Bool
    exactSourceRevisionRetained : Bool
    causalReviewRequiresSameProposition : Bool
    attributionPromotedToTruth : Bool
    corroborationPromotedToCanonicalTruth : Bool
    sourceNarrativeRewrittenByWorldFacts : Bool
    universalPartyRankingCreated : Bool

canonicalFriendlyjordiesAttributionCausalBoundary :
  FriendlyjordiesAttributionCausalBoundary
canonicalFriendlyjordiesAttributionCausalBoundary =
  friendlyjordies-attribution-causal-boundary
    true true true true true false false false false
