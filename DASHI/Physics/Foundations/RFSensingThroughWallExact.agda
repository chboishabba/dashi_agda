module DASHI.Physics.Foundations.RFSensingThroughWallExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Bounded abstraction for RF/Wi-Fi sensing in which propagation/reflection
-- changes can support human-presence, motion, pose, or activity hypotheses.
-- This module deliberately omits hardware construction, deployment geometry,
-- operational surveillance procedure, and target-identification logic.
------------------------------------------------------------------------

data RFSensingModality : Set where
  receivedSignalStrength : RFSensingModality
  channelStateInformation : RFSensingModality
  radioReflectionSensing : RFSensingModality

data RFSensingObservation : Set where
  multipathPerturbationA : RFSensingObservation
  multipathPerturbationB : RFSensingObservation

data HumanWorld : Set where
  personNearWallA : HumanWorld
  differentPersonNearWallA : HumanWorld
  noPersonB : HumanWorld

observeRF : HumanWorld → RFSensingObservation
observeRF personNearWallA = multipathPerturbationA
observeRF differentPersonNearWallA = multipathPerturbationA
observeRF noPersonB = multipathPerturbationB

personWorldsDistinct : personNearWallA ≡ differentPersonNearWallA → ⊥
personWorldsDistinct ()

RFObservationDeterminesExactHumanWorld : Set
RFObservationDeterminesExactHumanWorld =
  (x y : HumanWorld) → observeRF x ≡ observeRF y → x ≡ y

rfObservationDoesNotDetermineExactHumanWorld :
  ¬ RFObservationDeterminesExactHumanWorld
rfObservationDoesNotDetermineExactHumanWorld exact =
  personWorldsDistinct (exact personNearWallA differentPersonNearWallA refl)

------------------------------------------------------------------------
-- Observation claims and authority claims remain distinct.
------------------------------------------------------------------------

record RFSensingBoundary : Set where
  constructor rf-sensing-boundary
  field
    rfCanSupportThroughObstacleObservation : Bool
    rfCanSupportThroughObstacleObservationIsTrue :
      rfCanSupportThroughObstacleObservation ≡ true
    rfObservationDeterminesExactIdentity : Bool
    rfObservationDeterminesExactIdentityIsFalse :
      rfObservationDeterminesExactIdentity ≡ false
    rfObservationDeterminesIntent : Bool
    rfObservationDeterminesIntentIsFalse :
      rfObservationDeterminesIntent ≡ false
    rfObservationCreatesSurveillanceAuthority : Bool
    rfObservationCreatesSurveillanceAuthorityIsFalse :
      rfObservationCreatesSurveillanceAuthority ≡ false

open RFSensingBoundary public

canonicalRFSensingBoundary : RFSensingBoundary
canonicalRFSensingBoundary =
  rf-sensing-boundary true refl false refl false refl false refl

------------------------------------------------------------------------
-- Community/video/forum sources are lead generators, not theorem authority.
------------------------------------------------------------------------

record CommunityLeadAuthorityFirewall : Set where
  constructor community-lead-authority-firewall
  field
    communitySourceCanGenerateAcquisitionLead : Bool
    communitySourceCanGenerateAcquisitionLeadIsTrue :
      communitySourceCanGenerateAcquisitionLead ≡ true
    communitySourceAlonePaysTechnicalFact : Bool
    communitySourceAlonePaysTechnicalFactIsFalse :
      communitySourceAlonePaysTechnicalFact ≡ false
    primarySourceComparisonStillRequired : Bool
    primarySourceComparisonStillRequiredIsTrue :
      primarySourceComparisonStillRequired ≡ true

open CommunityLeadAuthorityFirewall public

canonicalCommunityLeadAuthorityFirewall : CommunityLeadAuthorityFirewall
canonicalCommunityLeadAuthorityFirewall =
  community-lead-authority-firewall true refl false refl true refl
