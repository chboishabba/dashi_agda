module DASHI.Cognition.OpenCivilianSpatialDefenseMobilityEnvelopeExact where

open import DASHI.Core.Prelude

import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as GEV
import DASHI.Cognition.OpenCivilianSpatialDefenseRobotHumanRightsExact as HumanRights

------------------------------------------------------------------------
-- UNCERTAIN MOBILITY / VISIBILITY ENVELOPE
--
-- This carrier is deliberately abstract: it records that a declared model has
-- produced an uncertainty-bearing estimate of where a mobile agent may be able
-- to move or observe over a bounded horizon.  It contains no real-world robot
-- performance constants, weapon ranges, disablement guidance, route-ambush
-- optimization, or countermeasure procedure.
------------------------------------------------------------------------

record UncertainMobilityEnvelope : Set where
  constructor uncertain-mobility-envelope
  field
    subject : GEV.WorldObjectRef
    sourceWorldState : GEV.ResolvedWorldState
    horizonReference : String
    reachabilityModelReference : String
    terrainConstraintReference : String
    observedMotionReference : String
    visibilityModelReference : String
    uncertaintyReference : String
    freshnessReference : String
    provenanceReference : String
    purposeReference : String

open UncertainMobilityEnvelope public

data CivilianEnvelopeRelation : Set where
  candidateRouteOutsideEnvelope : CivilianEnvelopeRelation
  candidateRouteIntersectsEnvelope : CivilianEnvelopeRelation
  relationUnresolved : CivilianEnvelopeRelation

record CivilianEnvelopeAssessment : Set where
  constructor civilian-envelope-assessment
  field
    envelope : UncertainMobilityEnvelope
    civilianRouteOrAreaReference : String
    relation : CivilianEnvelopeRelation
    uncertaintyPropagationReference : String
    warningReference : String
    reviewReference : String

open CivilianEnvelopeAssessment public

mobilityEnvelopeSupportsWarningAndAvoidance : Bool
mobilityEnvelopeSupportsWarningAndAvoidance = true

mobilityEnvelopeDeterminesHostility : Bool
mobilityEnvelopeDeterminesHostility = false

mobilityEnvelopeDeterminesWeaponization : Bool
mobilityEnvelopeDeterminesWeaponization = false

mobilityEnvelopeDeterminesExactFutureTrajectory : Bool
mobilityEnvelopeDeterminesExactFutureTrajectory = false

routeOutsideEstimatedEnvelopeGuaranteesSafety : Bool
routeOutsideEstimatedEnvelopeGuaranteesSafety = false

routeIntersectionImpliesHostileIntent : Bool
routeIntersectionImpliesHostileIntent = false

mobilityEnvelopeCreatesPersistentIdentityTrackingAuthority : Bool
mobilityEnvelopeCreatesPersistentIdentityTrackingAuthority = false

mobilityEnvelopeCreatesInterferenceAuthority : Bool
mobilityEnvelopeCreatesInterferenceAuthority = false

mobilityEnvelopeCreatesTargetingAuthority : Bool
mobilityEnvelopeCreatesTargetingAuthority = false

mobilityEnvelopeCreatesUseOfForceAuthority : Bool
mobilityEnvelopeCreatesUseOfForceAuthority = false

humanRightsAnchor : HumanRights.OpenCivilianHumanRightsBoundary
humanRightsAnchor = HumanRights.canonicalOpenCivilianHumanRightsBoundary

record MobilityEnvelopeBoundary : Set where
  constructor mobility-envelope-boundary
  field
    defensiveWarningConsumerAvailable : Bool
    avoidanceConsumerAvailable : Bool
    envelopeIsHostilityClassification : Bool
    envelopeIsExactPrediction : Bool
    outsideEnvelopeGuaranteesSafety : Bool
    envelopeCreatesInterferenceAuthority : Bool
    envelopeCreatesForceAuthority : Bool

canonicalMobilityEnvelopeBoundary : MobilityEnvelopeBoundary
canonicalMobilityEnvelopeBoundary =
  mobility-envelope-boundary
    true true false false false false false
