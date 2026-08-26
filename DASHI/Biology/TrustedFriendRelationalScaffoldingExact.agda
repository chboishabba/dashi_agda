module DASHI.Biology.TrustedFriendRelationalScaffoldingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.NeurodivergentSocialEcologySourceRegistryExact as Sources
import DASHI.Biology.SocialEcologicalAffordanceConeExact as Ecology
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- TRUSTED FRIEND / SAFE-PERSON RELATIONAL SCAFFOLDING
--
-- The primary positive case here is an ordinary trusted friend.  Formal
-- supporters are representable but are not the canonical relation.  A trusted
-- friend can contribute contextual information, mutual understanding,
-- co-regulation, and a stable reference point without replacing agency.
------------------------------------------------------------------------

data Situation : Set where
  benignAmbiguity hostileAmbiguity : Situation

data SelfObservation : Set where
  ambiguousSocialSignal : SelfObservation

data FriendContext : Set where
  likelyBenignContext likelyUnsafeContext : FriendContext

data RelationKind : Set where
  trustedFriend formalSupporter unfamiliarPerson absentRelation : RelationKind

data RegulationState : Set where
  regulatedState mobilisedState : RegulationState

data Decision : Set where
  remainDecision leaveDecision : Decision

selfObserver : Situation → SelfObservation
selfObserver benignAmbiguity = ambiguousSocialSignal
selfObserver hostileAmbiguity = ambiguousSocialSignal

friendObserver : Situation → FriendContext
friendObserver benignAmbiguity = likelyBenignContext
friendObserver hostileAmbiguity = likelyUnsafeContext

record JointObservation : Set where
  constructor jointObservation
  field
    selfSignal : SelfObservation
    trustedContext : FriendContext

open JointObservation public

jointObserver : Situation → JointObservation
jointObserver situation = jointObservation (selfObserver situation) (friendObserver situation)

sameSelfObservationAcrossDifferentSituations :
  selfObserver benignAmbiguity ≡ selfObserver hostileAmbiguity
sameSelfObservationAcrossDifferentSituations = refl

jointObservationDistinguishesThoseSituations :
  jointObserver benignAmbiguity ≡ jointObserver hostileAmbiguity → ⊥
jointObservationDistinguishesThoseSituations ()

trustedFriendStrictlyRefinesAmbiguousSelfObservation :
  Observer.StrictRefinement selfObserver jointObserver
trustedFriendStrictlyRefinesAmbiguousSelfObservation =
  Observer.strictRefinement
    (λ situation → refl)
    benignAmbiguity
    hostileAmbiguity
    sameSelfObservationAcrossDifferentSituations
    jointObservationDistinguishesThoseSituations

------------------------------------------------------------------------
-- Contextualization is information support, not delegated agency.
------------------------------------------------------------------------

choose : JointObservation → Decision
choose (jointObservation ambiguousSocialSignal likelyBenignContext) = remainDecision
choose (jointObservation ambiguousSocialSignal likelyUnsafeContext) = leaveDecision

data FriendContextReplacesAgencyPermission : Set where

friendContextDoesNotReplaceAgency : FriendContextReplacesAgencyPermission → ⊥
friendContextDoesNotReplaceAgency ()

------------------------------------------------------------------------
-- Relational co-regulation and ecology.
------------------------------------------------------------------------

regulateWith : RelationKind → RegulationState → RegulationState
regulateWith trustedFriend mobilisedState = regulatedState
regulateWith trustedFriend regulatedState = regulatedState
regulateWith formalSupporter mobilisedState = regulatedState
regulateWith relation state = state

trustedFriendCanChangeRegulatoryState :
  regulateWith trustedFriend mobilisedState ≡ mobilisedState → ⊥
trustedFriendCanChangeRegulatoryState ()

friendEcology : Ecology.Ecology
friendEcology =
  Ecology.ecology
    Ecology.adjustableRetreatSpace
    Ecology.lowDemandNorms
    Ecology.permissiveRegime
    Ecology.trustedFriendRelation

aloneHighDemandEcology : Ecology.Ecology
aloneHighDemandEcology = Ecology.highDemandEcology

trustedFriendEcologyOpensRemain :
  Ecology.available Ecology.canonicalAutisticPerson friendEcology Ecology.remainAction ≡ true
trustedFriendEcologyOpensRemain = refl

trustedFriendEcologyOpensRecovery :
  Ecology.available Ecology.canonicalAutisticPerson friendEcology Ecology.recoverAction ≡ true
trustedFriendEcologyOpensRecovery = refl

------------------------------------------------------------------------
-- Shared-code versus translation relation.
------------------------------------------------------------------------

data RelationalScaffoldMode : Set where
  contextualTranslation sharedCode lowTranslationNeed : RelationalScaffoldMode

data CommunicationCost : Set where
  lowCommunicationCost highCommunicationCost : CommunicationCost

communicationCost : RelationalScaffoldMode → CommunicationCost
communicationCost contextualTranslation = lowCommunicationCost
communicationCost sharedCode = lowCommunicationCost
communicationCost lowTranslationNeed = lowCommunicationCost

record FriendEcologyBoundary : Set where
  constructor friendEcologyBoundary
  field
    safePersonMeansOnlyProfessionalSupport : Bool
    safePersonMeansOnlyProfessionalSupportIsFalse : safePersonMeansOnlyProfessionalSupport ≡ false
    trustedFriendIsCanonicalPositiveRelation : Bool
    trustedFriendIsCanonicalPositiveRelationIsTrue : trustedFriendIsCanonicalPositiveRelation ≡ true
    friendCanAddContextWithoutReplacingAgency : Bool
    friendCanAddContextWithoutReplacingAgencyIsTrue : friendCanAddContextWithoutReplacingAgency ≡ true
    friendCanChangeRealizedAffordanceCone : Bool
    friendCanChangeRealizedAffordanceConeIsTrue : friendCanChangeRealizedAffordanceCone ≡ true
    everyFriendshipIsAutomaticallySafe : Bool
    everyFriendshipIsAutomaticallySafeIsFalse : everyFriendshipIsAutomaticallySafe ≡ false

canonicalFriendEcologyBoundary : FriendEcologyBoundary
canonicalFriendEcologyBoundary =
  friendEcologyBoundary false refl true refl true refl true refl false refl

friendshipSource : Sources.SourceReference
friendshipSource = Sources.friendshipTrust2025

friendshipSpectrumSource : Sources.SourceReference
friendshipSpectrumSource = Sources.friendship2024

supportTranslationSource : Sources.SourceReference
supportTranslationSource = Sources.supportTranslation2024

neurodivergentCommunitySource : Sources.SourceReference
neurodivergentCommunitySource = Sources.ndFriendship2025

doubleEmpathySource : Sources.SourceReference
doubleEmpathySource = Sources.doubleEmpathy2012
