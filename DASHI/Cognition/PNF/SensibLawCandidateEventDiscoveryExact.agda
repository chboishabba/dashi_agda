module DASHI.Cognition.PNF.SensibLawCandidateEventDiscoveryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawReviewWorkstationExact as Review

------------------------------------------------------------------------
-- S28.AUTO candidate event discovery.
--
-- Automatic matching is allowed to propose a possible shared event identity.
-- It is not allowed to create that identity.  Proposals enter the ordinary
-- S29 event-assembly review lane.
------------------------------------------------------------------------

data EventJoinSignalKind : Set where
  sharedQid sharedEntity sharedTemporalBucket sharedFingerprint :
    EventJoinSignalKind
  explicitCrossReference userDeclaredSameIncident : EventJoinSignalKind

record EventJoinSignal : Set where
  constructor event-join-signal
  field
    signalKind : EventJoinSignalKind
    evidenceRef : String
    detectorRef : String

open EventJoinSignal public

record CandidateEventJoinProposal : Set where
  constructor candidate-event-join-proposal
  field
    proposalRef : String
    observationRefs : List String
    statementRefs : List String
    sourceFamilyRefs : List String
    signals : List EventJoinSignal
    policyRef : String
    independentSignalKindCount : Nat
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true
    requiresReview : Bool
    requiresReviewIsTrue : requiresReview ≡ true
    createsEventIdentity : Bool
    createsEventIdentityIsFalse : createsEventIdentity ≡ false
    createsSemanticAuthority : Bool
    createsSemanticAuthorityIsFalse : createsSemanticAuthority ≡ false
    applicabilityPromoted : Bool
    applicabilityPromotedIsFalse : applicabilityPromoted ≡ false
    claimTruthPromoted : Bool
    claimTruthPromotedIsFalse : claimTruthPromoted ≡ false

open CandidateEventJoinProposal public

record AutomaticDiscoveryBoundary : Set where
  constructor automatic-discovery-boundary
  field
    sameQidAloneCreatesProposal : Bool
    multipleIndependentSignalsMayCreateProposal : Bool
    proposalRequiresHumanReview : Bool
    proposalCreatesEventIdentity : Bool
    acceptedReviewCreatesTruth : Bool
    detectorMayWriteObservationEventLinkDirectly : Bool

canonicalAutomaticDiscoveryBoundary : AutomaticDiscoveryBoundary
canonicalAutomaticDiscoveryBoundary =
  automatic-discovery-boundary
    false true true false false false

------------------------------------------------------------------------
-- Review weld.
------------------------------------------------------------------------

record EventAssemblyReviewWeld (proposal : CandidateEventJoinProposal) : Set where
  constructor event-assembly-review-weld
  field
    reviewItem : Review.ReviewItem
    itemKindIsEventAssembly :
      Review.ReviewItem.itemKind reviewItem ≡ Review.eventAssembly
    proposalStillCandidate :
      CandidateEventJoinProposal.candidateOnly proposal ≡ true
    proposalStillDoesNotCreateIdentity :
      CandidateEventJoinProposal.createsEventIdentity proposal ≡ false

open EventAssemblyReviewWeld public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data SameQidCreatesCanonicalEvent : Set where
data SamePersonDateCreatesCanonicalEvent : Set where
data SimilarTextCreatesCanonicalEvent : Set where
data ProposalIsCanonicalEvent : Set where
data DetectorMayBypassEventAssemblyReview : Set where
data EventAssemblyReviewCreatesClaimTruth : Set where
data ProposalCreatesSemanticAuthority : Set where

sameQidDoesNotCreateCanonicalEvent :
  SameQidCreatesCanonicalEvent → ⊥
sameQidDoesNotCreateCanonicalEvent ()

samePersonDateDoesNotCreateCanonicalEvent :
  SamePersonDateCreatesCanonicalEvent → ⊥
samePersonDateDoesNotCreateCanonicalEvent ()

similarTextDoesNotCreateCanonicalEvent :
  SimilarTextCreatesCanonicalEvent → ⊥
similarTextDoesNotCreateCanonicalEvent ()

proposalIsNotCanonicalEvent : ProposalIsCanonicalEvent → ⊥
proposalIsNotCanonicalEvent ()

detectorCannotBypassEventAssemblyReview :
  DetectorMayBypassEventAssemblyReview → ⊥
detectorCannotBypassEventAssemblyReview ()

eventAssemblyReviewDoesNotCreateClaimTruth :
  EventAssemblyReviewCreatesClaimTruth → ⊥
eventAssemblyReviewDoesNotCreateClaimTruth ()

proposalDoesNotCreateSemanticAuthority :
  ProposalCreatesSemanticAuthority → ⊥
proposalDoesNotCreateSemanticAuthority ()
