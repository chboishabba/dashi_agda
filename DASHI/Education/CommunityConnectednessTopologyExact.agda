module DASHI.Education.CommunityConnectednessTopologyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor

------------------------------------------------------------------------
-- EFFECTIVE COMMUNITY CONNECTEDNESS
--
-- A formal institutional/community edge is not yet an effective connection.
-- Reachability, reciprocity, trust, contestability and activation burden remain
-- independent coordinates. The same situated coordinate may be a burden for
-- one consumer and coexist with a useful relational affordance for another.
------------------------------------------------------------------------

data ActivationCost : Set where lowCost highCost : ActivationCost

data AccessBurden : Set where lowBurden highBurden : AccessBurden

record CommunityConnectionState : Set where
  constructor communityConnectionState
  field
    formalConnection : Bool
    reachable : Bool
    reciprocal : Bool
    trusted : Bool
    contestable : Bool
    activationCost : ActivationCost
    currentAuthority : Bool
    travelBurden : AccessBurden
    dwellOpportunity : Bool
    peerExchangeRoute : Bool
    receipt : String

open CommunityConnectionState public

effectiveConnection : CommunityConnectionState → Bool
effectiveConnection state with formalConnection state | reachable state | reciprocal state | trusted state | contestable state
... | true | true | true | true | true = true
... | _ | _ | _ | _ | _ = false

formalOnly : CommunityConnectionState
formalOnly =
  communityConnectionState
    true false false false false highCost false lowBurden false false
    "formal service/community relationship exists but is not reachable, reciprocal, trusted or contestable"

effectivePeerConnection : CommunityConnectionState
effectivePeerConnection =
  communityConnectionState
    true true true true true lowCost false highBurden true true
    "effective peer/community connection; high travel burden coexists with dwell opportunity and peer exchange, without conferring authority"

effectiveAuthorityConnection : CommunityConnectionState
effectiveAuthorityConnection =
  communityConnectionState
    true true true true true lowCost true highBurden true true
    "same effective relational surface with an independently present authority coordinate"

highBurdenNoDwell : CommunityConnectionState
highBurdenNoDwell =
  communityConnectionState
    true true false true true highCost false highBurden false false
    "high travel burden without a usable dwell-time or peer-exchange affordance"

formalProjection : CommunityConnectionState → Bool
formalProjection = formalConnection

effectiveProjection : CommunityConnectionState → Bool
effectiveProjection = effectiveConnection

authorityProjection : CommunityConnectionState → Bool
authorityProjection = currentAuthority

sameFormalDifferentEffective :
  formalProjection formalOnly ≡ formalProjection effectivePeerConnection
sameFormalDifferentEffective = refl

effectiveDiffersAtSameFormal :
  effectiveProjection formalOnly ≡ effectiveProjection effectivePeerConnection → ⊥
effectiveDiffersAtSameFormal ()

formalCannotDetermineEffectiveWitness :
  NonFactor.NonFactorabilityWitness formalProjection effectiveProjection
formalCannotDetermineEffectiveWitness =
  NonFactor.nonFactorabilityWitness
    formalOnly effectivePeerConnection
    sameFormalDifferentEffective effectiveDiffersAtSameFormal

formalConnectionCannotDetermineEffectiveConnection :
  NonFactor.FactorsThrough formalProjection effectiveProjection → ⊥
formalConnectionCannotDetermineEffectiveConnection =
  NonFactor.witnessRulesOutEveryFlatFactorisation formalCannotDetermineEffectiveWitness

sameEffectiveDifferentAuthority :
  effectiveProjection effectivePeerConnection ≡ effectiveProjection effectiveAuthorityConnection
sameEffectiveDifferentAuthority = refl

authorityDiffersAtSameEffectiveConnection :
  authorityProjection effectivePeerConnection ≡ authorityProjection effectiveAuthorityConnection → ⊥
authorityDiffersAtSameEffectiveConnection ()

effectiveConnectionCannotDetermineAuthorityWitness :
  NonFactor.NonFactorabilityWitness effectiveProjection authorityProjection
effectiveConnectionCannotDetermineAuthorityWitness =
  NonFactor.nonFactorabilityWitness
    effectivePeerConnection effectiveAuthorityConnection
    sameEffectiveDifferentAuthority authorityDiffersAtSameEffectiveConnection

effectiveConnectionCannotDetermineAuthority :
  NonFactor.FactorsThrough effectiveProjection authorityProjection → ⊥
effectiveConnectionCannotDetermineAuthority =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    effectiveConnectionCannotDetermineAuthorityWitness

------------------------------------------------------------------------
-- Burden/affordance cross-axis countermodel.
------------------------------------------------------------------------

burdenProjection : CommunityConnectionState → AccessBurden
burdenProjection = travelBurden

dwellProjection : CommunityConnectionState → Bool
dwellProjection = dwellOpportunity

sameTravelBurdenDifferentDwell :
  burdenProjection highBurdenNoDwell ≡ burdenProjection effectivePeerConnection
sameTravelBurdenDifferentDwell = refl

dwellDiffersAtSameTravelBurden :
  dwellProjection highBurdenNoDwell ≡ dwellProjection effectivePeerConnection → ⊥
dwellDiffersAtSameTravelBurden ()

travelBurdenCannotDetermineRelationalAffordanceWitness :
  NonFactor.NonFactorabilityWitness burdenProjection dwellProjection
travelBurdenCannotDetermineRelationalAffordanceWitness =
  NonFactor.nonFactorabilityWitness
    highBurdenNoDwell effectivePeerConnection
    sameTravelBurdenDifferentDwell dwellDiffersAtSameTravelBurden

travelBurdenCannotDetermineDwellAffordance :
  NonFactor.FactorsThrough burdenProjection dwellProjection → ⊥
travelBurdenCannotDetermineDwellAffordance =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    travelBurdenCannotDetermineRelationalAffordanceWitness

------------------------------------------------------------------------
-- Genuine relational topology: effective edges compose into a typed path.
-- The relay node supplies a route, not direct source-target identity or
-- authority. This is the exact shape needed for a peer connector/champion-like
-- role without converting that relay into an authoritative source.
------------------------------------------------------------------------

data CommunityNode : Set where
  familyNode peerNode serviceNode : CommunityNode

record EffectiveEdge (from to : CommunityNode) : Set where
  constructor effectiveEdge
  field
    connection : CommunityConnectionState
    connectionEffective : effectiveConnection connection ≡ true
    edgeAddsAuthority : currentAuthority connection ≡ false

open EffectiveEdge public

familyToPeer : EffectiveEdge familyNode peerNode
familyToPeer = effectiveEdge effectivePeerConnection refl refl

peerToService : EffectiveEdge peerNode serviceNode
peerToService = effectiveEdge effectivePeerConnection refl refl

record TwoHopEffectivePath
    (source relay target : CommunityNode) : Set where
  constructor twoHopEffectivePath
  field
    firstEdge : EffectiveEdge source relay
    secondEdge : EffectiveEdge relay target

open TwoHopEffectivePath public

familyPeerServicePath : TwoHopEffectivePath familyNode peerNode serviceNode
familyPeerServicePath = twoHopEffectivePath familyToPeer peerToService

------------------------------------------------------------------------
-- Peer catalyst: useful relational routing without authority promotion.
------------------------------------------------------------------------

record PeerCatalyst : Set where
  constructor peerCatalyst
  field
    facilitatesConnection : Bool
    sharesSituatedExperience : Bool
    invitesIndependentInquiry : Bool
    epistemicAuthority : Bool
    decisionAuthority : Bool

open PeerCatalyst public

canonicalPeerCatalyst : PeerCatalyst
canonicalPeerCatalyst = peerCatalyst true true true false false

record PeerCatalystBoundary : Set where
  constructor peerCatalystBoundary
  field
    peerInfluenceAutomaticallyConfersEpistemicAuthority : Bool
    peerInfluenceAutomaticallyConfersDecisionAuthority : Bool
    peerCatalystMayFacilitateWithoutAuthority : Bool
    twoHopRouteCreatesDirectAuthority : Bool

open PeerCatalystBoundary public

canonicalPeerCatalystBoundary : PeerCatalystBoundary
canonicalPeerCatalystBoundary = peerCatalystBoundary false false true false

record CommunityConnectednessBoundary : Set where
  constructor communityConnectednessBoundary
  field
    formalEdgeEqualsEffectiveConnection : Bool
    effectiveConnectionDeterminesAuthority : Bool
    highTravelBurdenAlwaysDestroysRelationalAffordance : Bool
    highTravelBurdenIsThereforeGood : Bool
    connectednessIsConsumerAndContextSensitive : Bool
    effectiveEdgesCanComposeThroughRelay : Bool
    relayPathIdentifiesEndpoints : Bool

open CommunityConnectednessBoundary public

canonicalCommunityConnectednessBoundary : CommunityConnectednessBoundary
canonicalCommunityConnectednessBoundary =
  communityConnectednessBoundary false false false false true true false
