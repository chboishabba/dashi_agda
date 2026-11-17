module DASHI.Cognition.OpenCivilianSpatialDefenseRFObservationExact where

open import DASHI.Core.Prelude

import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as GEV
import DASHI.Physics.Foundations.RadioRadarGoniometerDirectionFindingExact as Goniometer
import DASHI.Physics.Foundations.PhasedArrayDirectionFindingExact as Array
import DASHI.Physics.Foundations.RFSensingThroughWallExact as RFSensing
import DASHI.Physics.Foundations.GoniometerPhasedArrayRFSensingCrossPollinationExact as RFCross

------------------------------------------------------------------------
-- OPEN CIVILIAN SPATIAL DEFENCE x PASSIVE RF OBSERVATION
--
-- This is an observation/fusion seam only.  It intentionally contains no
-- emitter-geolocation procedure, interference/jamming recipe, robot-disable
-- procedure, targeting logic, weapon employment, or autonomous engagement.
------------------------------------------------------------------------

data CivilianRFObservationKind : Set where
  boundedBearingObservation : CivilianRFObservationKind
  boundedArrayBearingObservation : CivilianRFObservationKind
  boundedSignalPresenceObservation : CivilianRFObservationKind
  boundedMultipathObservation : CivilianRFObservationKind
  externallyReportedRFObservation : CivilianRFObservationKind

record CivilianRFObservationReceipt : Set where
  constructor civilian-rf-observation-receipt
  field
    observationKind : CivilianRFObservationKind
    worldSubject : GEV.WorldObjectRef
    observationReference : String
    observedAtReference : String
    receiverGeometryReference : String
    frequencyBandReference : String
    calibrationReference : String
    uncertaintyReference : String
    sourceProvenanceReference : String
    collectionAuthorityReference : String

open CivilianRFObservationReceipt public

------------------------------------------------------------------------
-- Same-object fusion is proof-relevant.  Merely having an RF bearing that
-- overlaps a visual/spatial track does not identify the emitter, robot,
-- operator, mission, payload, or legal status.  The fusion receipt therefore
-- carries literal world-object equality in addition to review/evidence refs.
------------------------------------------------------------------------

record RFVisualSameObjectFusionReceipt : Set where
  constructor rf-visual-same-object-fusion-receipt
  field
    rfObservation : CivilianRFObservationReceipt
    visualWorldState : GEV.ResolvedWorldState
    rfSubjectIsVisualSubject :
      GEV.objectId (worldSubject rfObservation)
      ≡ GEV.objectId (GEV.resolvedSubject visualWorldState)
    temporalCompatibilityReference : String
    spatialCompatibilityReference : String
    identityEvidenceReference : String
    ambiguityReference : String
    sameObjectReviewReference : String

open RFVisualSameObjectFusionReceipt public

rfVisualFusionRequiresSameObjectReceipt : Bool
rfVisualFusionRequiresSameObjectReceipt = true

singleBearingDeterminesExactRobotWorld : Bool
singleBearingDeterminesExactRobotWorld = false

passiveRFObservationCreatesExactEmitterIdentity : Bool
passiveRFObservationCreatesExactEmitterIdentity = false

passiveRFObservationCreatesRobotIdentity : Bool
passiveRFObservationCreatesRobotIdentity = false

passiveRFObservationCreatesOperatorIdentity : Bool
passiveRFObservationCreatesOperatorIdentity = false

passiveRFObservationCreatesMissionIdentity : Bool
passiveRFObservationCreatesMissionIdentity = false

passiveRFObservationCreatesHostileAttribution : Bool
passiveRFObservationCreatesHostileAttribution = false

passiveRFObservationCreatesSurveillanceAuthority : Bool
passiveRFObservationCreatesSurveillanceAuthority = false

passiveRFObservationCreatesJammingAuthority : Bool
passiveRFObservationCreatesJammingAuthority = false

passiveRFObservationCreatesUseOfForceAuthority : Bool
passiveRFObservationCreatesUseOfForceAuthority = false

------------------------------------------------------------------------
-- Existing non-factorability and authority owners are imported literally.
------------------------------------------------------------------------

bearingNonIdentityAnchor :
  ¬ Goniometer.BearingDeterminesExactEmitterWorld
bearingNonIdentityAnchor =
  Goniometer.bearingDoesNotDetermineExactEmitterWorld

arrayBearingNonIdentityAnchor :
  ¬ Array.ArrayBearingDeterminesExactEmitterWorld
arrayBearingNonIdentityAnchor =
  Array.arrayBearingDoesNotDetermineExactEmitterWorld

rfHumanWorldNonIdentityAnchor :
  ¬ RFSensing.RFObservationDeterminesExactHumanWorld
rfHumanWorldNonIdentityAnchor =
  RFSensing.rfObservationDoesNotDetermineExactHumanWorld

rfCrossAuthorityAnchor : RFCross.CrossDomainAuthorityFirewall
rfCrossAuthorityAnchor = RFCross.canonicalCrossDomainAuthorityFirewall

------------------------------------------------------------------------
-- Defensive consumers.  These outputs are informational/protective only.
------------------------------------------------------------------------

data CivilianRFDefensiveConsumer : Set where
  anomalyAwarenessConsumer : CivilianRFDefensiveConsumer
  uncertaintyBearingMapConsumer : CivilianRFDefensiveConsumer
  civilianWarningConsumer : CivilianRFDefensiveConsumer
  avoidanceRoutingConsumer : CivilianRFDefensiveConsumer
  shelteringSupportConsumer : CivilianRFDefensiveConsumer
  evidencePreservationConsumer : CivilianRFDefensiveConsumer

record CivilianRFFusionDemand : Set where
  constructor civilian-rf-fusion-demand
  field
    consumer : CivilianRFDefensiveConsumer
    rfReceiptReference : String
    nonRFObservationReference : String
    sameObjectReceiptReference : String
    uncertaintyPropagationReference : String
    purposeReference : String
    accessAuthorityReference : String
    outputReference : String

open CivilianRFFusionDemand public

record OpenCivilianRFBoundary : Set where
  constructor open-civilian-rf-boundary
  field
    passiveObservationAllowedAsEvidence : Bool
    bearingIsExactLocation : Bool
    rfSignalIsExactRobotIdentity : Bool
    rfSignalIsHostileAttribution : Bool
    sameObjectFusionReceiptRequired : Bool
    warningAndAvoidanceConsumersAvailable : Bool
    jammingAuthorityCreated : Bool
    forceAuthorityCreated : Bool

canonicalOpenCivilianRFBoundary : OpenCivilianRFBoundary
canonicalOpenCivilianRFBoundary =
  open-civilian-rf-boundary
    true false false false true true false false
