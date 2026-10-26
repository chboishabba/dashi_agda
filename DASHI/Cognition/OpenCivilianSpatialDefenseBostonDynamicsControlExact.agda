module DASHI.Cognition.OpenCivilianSpatialDefenseBostonDynamicsControlExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Cognition.OpenCivilianSpatialDefenseSourceAtlasExact as Sources
import DASHI.Cognition.OpenCivilianSpatialDefenseRobotHumanRightsExact as HumanRights

------------------------------------------------------------------------
-- BOSTON DYNAMICS AS A BENIGN / GENERAL-PURPOSE ROBOT CONTROL CASE
--
-- This owner uses Boston Dynamics only as a first-party-sourced control against
-- morphology/autonomy overclaiming.  A mobile quadruped or humanoid robot may
-- be highly capable without thereby being weaponized, hostile, autonomously
-- targeting people, or legally classifiable as a weapon system.
------------------------------------------------------------------------

data RobotPlatformClass : Set where
  quadrupedMobileRobot : RobotPlatformClass
  humanoidMobileRobot : RobotPlatformClass
  otherGeneralPurposeMobileRobot : RobotPlatformClass

data RobotCapabilityCoordinate : Set where
  autonomousLocomotion : RobotCapabilityCoordinate
  obstacleAvoidance : RobotCapabilityCoordinate
  remoteInspection : RobotCapabilityCoordinate
  logisticsSupport : RobotCapabilityCoordinate
  rescueSupport : RobotCapabilityCoordinate
  persistentSensing : RobotCapabilityCoordinate
  objectClassification : RobotCapabilityCoordinate
  personTracking : RobotCapabilityCoordinate
  targetNomination : RobotCapabilityCoordinate
  forceCapablePayload : RobotCapabilityCoordinate
  autonomousApplicationOfForce : RobotCapabilityCoordinate

robotMorphologyDeterminesHostileFunction : Bool
robotMorphologyDeterminesHostileFunction = false

autonomousLocomotionDeterminesAutonomousTargeting : Bool
autonomousLocomotionDeterminesAutonomousTargeting = false

persistentSensingDeterminesWeaponization : Bool
persistentSensingDeterminesWeaponization = false

militaryUseDeterminesWeaponizedUse : Bool
militaryUseDeterminesWeaponizedUse = false

generalPurposeNonWeaponizedControlEligible : Bool
generalPurposeNonWeaponizedControlEligible = true

------------------------------------------------------------------------
-- First-party Boston Dynamics claims remain vendor-authority claims.
------------------------------------------------------------------------

bostonDynamicsStatesGeneralPurposeSpot : Bool
bostonDynamicsStatesGeneralPurposeSpot = true

bostonDynamicsStatesNonWeaponizedMilitaryUses : Bool
bostonDynamicsStatesNonWeaponizedMilitaryUses = true

bostonDynamicsStatesAntiWeaponizationPolicy : Bool
bostonDynamicsStatesAntiWeaponizationPolicy = true

vendorAntiWeaponizationPolicyCreatesUniversalLegalConstraint : Bool
vendorAntiWeaponizationPolicyCreatesUniversalLegalConstraint = false

vendorPolicyProvesEveryDownstreamDeploymentComplies : Bool
vendorPolicyProvesEveryDownstreamDeploymentComplies = false

vendorPolicyProvesThirdPartyRobotsBenign : Bool
vendorPolicyProvesThirdPartyRobotsBenign = false

vendorDescriptionCreatesIndependentSafetyValidation : Bool
vendorDescriptionCreatesIndependentSafetyValidation = false

bostonFAQSourceAnchor : Source.AttributedSource
bostonFAQSourceAnchor = Sources.bostonDynamicsFAQ

bostonOpenLetterSourceAnchor : Source.AttributedSource
bostonOpenLetterSourceAnchor = Sources.bostonDynamicsAntiWeaponizationLetter

------------------------------------------------------------------------
-- Defensive classification receipt.
------------------------------------------------------------------------

record RobotFunctionAssessment : Set where
  constructor robot-function-assessment
  field
    platformClass : RobotPlatformClass
    observedCapabilityReference : String
    payloadEvidenceReference : String
    missionEvidenceReference : String
    operatorEvidenceReference : String
    autonomyEvidenceReference : String
    uncertaintyReference : String
    provenanceReference : String
    assessmentReference : String

open RobotFunctionAssessment public

morphologyAlonePaysFunctionAssessment : Bool
morphologyAlonePaysFunctionAssessment = false

capabilityAlonePaysHostilityAssessment : Bool
capabilityAlonePaysHostilityAssessment = false

operatorIdentityAlonePaysHostilityAssessment : Bool
operatorIdentityAlonePaysHostilityAssessment = false

------------------------------------------------------------------------
-- The control case is intentionally compatible with civilian safety warning:
-- uncertain mobile agents may still be represented as movement/visibility
-- hazards without asserting hostile intent or weapon status.
------------------------------------------------------------------------

benignControlMayStillHaveMobilityEnvelope : Bool
benignControlMayStillHaveMobilityEnvelope = true

mobilityEnvelopeEqualsThreatClassification : Bool
mobilityEnvelopeEqualsThreatClassification = false

humanRightsBoundaryAnchor : HumanRights.OpenCivilianHumanRightsBoundary
humanRightsBoundaryAnchor = HumanRights.canonicalOpenCivilianHumanRightsBoundary

record BostonDynamicsControlBoundary : Set where
  constructor boston-dynamics-control-boundary
  field
    generalPurposeRobotCanBeNonWeaponized : Bool
    morphologyDeterminesMission : Bool
    locomotionAutonomyDeterminesTargetingAutonomy : Bool
    militaryUseDeterminesWeaponization : Bool
    vendorPolicyIsUniversalLaw : Bool
    vendorPolicyIsAttributedEvidence : Bool
    benignControlSupportsFalsePositiveTesting : Bool

canonicalBostonDynamicsControlBoundary : BostonDynamicsControlBoundary
canonicalBostonDynamicsControlBoundary =
  boston-dynamics-control-boundary
    true false false false false true true
