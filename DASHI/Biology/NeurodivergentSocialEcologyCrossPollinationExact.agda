module DASHI.Biology.NeurodivergentSocialEcologyCrossPollinationExact where

open import DASHI.Core.Prelude

import DASHI.Biology.NeurotypeProcessingGeometryExact as Processing
import DASHI.Biology.SocialEcologicalAffordanceConeExact as Ecology
import DASHI.Biology.TrustedFriendRelationalScaffoldingExact as Friend
import DASHI.Biology.NeuroqueerRelationshipEcologyExact as Neuroqueer
import DASHI.Biology.PsilautNetworkResponseGeometryExact as Psilaut
import DASHI.Biology.SolisSystemSensitivityBoundaryExact as Solis
import DASHI.Core.ContrastiveInterventionResponseExact as Response

------------------------------------------------------------------------
-- CROSS-POLLINATION OWNER
--
-- This module composes the discussion surfaces without claiming that any one
-- layer is the essence of autism.  Processing geometry, relationship ecology,
-- built/social/institutional ecology, trusted-friend context and perturbational
-- network response remain distinct coordinates of one situated research state.
------------------------------------------------------------------------

record SituatedNeurodivergentState : Set where
  constructor situatedNeurodivergentState
  field
    processing : Processing.ProcessingGeometry
    ecology : Ecology.Ecology
    relation : Friend.RelationKind
    intimateEcology : Neuroqueer.IntimateEcology
    systemObserverStyle : Solis.ObserverStyle

open SituatedNeurodivergentState public

supportiveSituatedState : SituatedNeurodivergentState
supportiveSituatedState =
  situatedNeurodivergentState
    Processing.deepRuleGeometry
    Ecology.thirdPlaceEcology
    Friend.trustedFriend
    Neuroqueer.canonicalAutisticQueerEcology
    Solis.systemSensitiveObserver

hostileSituatedState : SituatedNeurodivergentState
hostileSituatedState =
  situatedNeurodivergentState
    Processing.deepRuleGeometry
    Ecology.highDemandEcology
    Friend.absentRelation
    Neuroqueer.canonicalAutisticQueerEcology
    Solis.systemSensitiveObserver

sameProcessingAcrossEcologyWitness :
  processing supportiveSituatedState ≡ processing hostileSituatedState
sameProcessingAcrossEcologyWitness = refl

sameIntimateEcologyAcrossEcologyWitness :
  intimateEcology supportiveSituatedState ≡ intimateEcology hostileSituatedState
sameIntimateEcologyAcrossEcologyWitness = refl

supportiveRemainAvailable :
  Ecology.available Ecology.canonicalAutisticPerson
    (ecology supportiveSituatedState) Ecology.remainAction ≡ true
supportiveRemainAvailable = refl

hostileRemainUnavailable :
  Ecology.available Ecology.canonicalAutisticPerson
    (ecology hostileSituatedState) Ecology.remainAction ≡ false
hostileRemainUnavailable = refl

sameProcessingDoesNotFixRealizedOptionCone :
  Ecology.available Ecology.canonicalAutisticPerson
    (ecology supportiveSituatedState) Ecology.remainAction
  ≡
  Ecology.available Ecology.canonicalAutisticPerson
    (ecology hostileSituatedState) Ecology.remainAction → ⊥
sameProcessingDoesNotFixRealizedOptionCone ()

------------------------------------------------------------------------
-- Reaction latency therefore cannot stand in for the social-ecological cone.
------------------------------------------------------------------------

sameLatencyAcrossEcologyWitness :
  Processing.latencyObserver (processing supportiveSituatedState)
  ≡ Processing.latencyObserver (processing hostileSituatedState)
sameLatencyAcrossEcologyWitness = refl

latencyDoesNotDetermineRemainAffordance :
  Ecology.available Ecology.canonicalAutisticPerson
    (ecology supportiveSituatedState) Ecology.remainAction
  ≡
  Ecology.available Ecology.canonicalAutisticPerson
    (ecology hostileSituatedState) Ecology.remainAction → ⊥
latencyDoesNotDetermineRemainAffordance = sameProcessingDoesNotFixRealizedOptionCone

------------------------------------------------------------------------
-- Trusted relation and third-place ecology are separable.
------------------------------------------------------------------------

data SafeSpaceEqualsSafeFriendPermission : Set where

safeSpaceDoesNotCollapseToSafeFriend : SafeSpaceEqualsSafeFriendPermission → ⊥
safeSpaceDoesNotCollapseToSafeFriend ()

------------------------------------------------------------------------
-- PSILAUT stays an intervention-response observer.
------------------------------------------------------------------------

psilautDMNResponseNonDescentInstalled :
  ¬ Response.ResponseDescendsThroughBaseline
      Psilaut.observeConnectivity
      Psilaut.applyDose
      Psilaut.placebo
      Psilaut.connectivityContrast
      Psilaut.fiveMg
psilautDMNResponseNonDescentInstalled =
  Psilaut.dmnFiveMgResponseCannotDescendThroughBaselineSummary

record CrossPollinationBoundary : Set where
  constructor crossPollinationBoundary
  field
    processingGeometryEqualsEcologicalReachability : Bool
    processingGeometryEqualsEcologicalReachabilityIsFalse :
      processingGeometryEqualsEcologicalReachability ≡ false
    reactionLatencyEqualsCapacity : Bool
    reactionLatencyEqualsCapacityIsFalse : reactionLatencyEqualsCapacity ≡ false
    trustedFriendEqualsFormalAuthority : Bool
    trustedFriendEqualsFormalAuthorityIsFalse : trustedFriendEqualsFormalAuthority ≡ false
    neuroqueeringEqualsSexualOrientation : Bool
    neuroqueeringEqualsSexualOrientationIsFalse : neuroqueeringEqualsSexualOrientation ≡ false
    psilautResponseIdentifiesFullMechanism : Bool
    psilautResponseIdentifiesFullMechanismIsFalse : psilautResponseIdentifiesFullMechanism ≡ false
    solisCandidateEqualsEstablishedAutismMechanism : Bool
    solisCandidateEqualsEstablishedAutismMechanismIsFalse :
      solisCandidateEqualsEstablishedAutismMechanism ≡ false
    samePersonCanHaveDifferentRealizedConeAcrossEcologies : Bool
    samePersonCanHaveDifferentRealizedConeAcrossEcologiesIsTrue :
      samePersonCanHaveDifferentRealizedConeAcrossEcologies ≡ true

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  crossPollinationBoundary false refl false refl false refl false refl false refl false refl true refl
