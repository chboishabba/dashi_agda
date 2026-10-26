module DASHI.Cognition.OpenCivilianSpatialDefenseCapabilityEscalationExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.OpenCivilianSpatialDefenseRobotHumanRightsExact as HumanRights

------------------------------------------------------------------------
-- CAPABILITY ESCALATION GRAPH
--
-- This is a classification/audit graph, not a development roadmap and not a
-- recipe for weaponization.  Each stage records a distinct capability claim
-- that requires its own evidence and authority analysis.  Earlier stages never
-- automatically promote into later stages.
------------------------------------------------------------------------

data RobotCapabilityStage : Set where
  mobilePlatform : RobotCapabilityStage
  autonomousNavigation : RobotCapabilityStage
  persistentSensing : RobotCapabilityStage
  personOrObjectClassification : RobotCapabilityStage
  persistentTracking : RobotCapabilityStage
  targetNomination : RobotCapabilityStage
  forceCapablePayload : RobotCapabilityStage
  machineMediatedApplicationOfForce : RobotCapabilityStage

record CapabilityStageReceipt : Set where
  constructor capability-stage-receipt
  field
    stage : RobotCapabilityStage
    systemReference : String
    evidenceReference : String
    sourceAuthorityReference : String
    temporalReference : String
    operatorReference : String
    deploymentReference : String
    uncertaintyReference : String
    reviewReference : String

open CapabilityStageReceipt public

capabilityStageAutomaticallyPromotesToNext : Bool
capabilityStageAutomaticallyPromotesToNext = false

autonomousLocomotionImpliesPersistentSensing : Bool
autonomousLocomotionImpliesPersistentSensing = false

autonomousLocomotionImpliesPersonClassification : Bool
autonomousLocomotionImpliesPersonClassification = false

autonomousLocomotionImpliesTargetNomination : Bool
autonomousLocomotionImpliesTargetNomination = false

persistentSensingImpliesPersistentTracking : Bool
persistentSensingImpliesPersistentTracking = false

classificationImpliesTargetNomination : Bool
classificationImpliesTargetNomination = false

targetNominationImpliesForceCapablePayload : Bool
targetNominationImpliesForceCapablePayload = false

forceCapablePayloadImpliesAutonomousApplicationOfForce : Bool
forceCapablePayloadImpliesAutonomousApplicationOfForce = false

samePlatformAcrossStagesImpliesSameSoftware : Bool
samePlatformAcrossStagesImpliesSameSoftware = false

samePlatformAcrossStagesImpliesSameOperator : Bool
samePlatformAcrossStagesImpliesSameOperator = false

samePlatformAcrossStagesImpliesSameAuthority : Bool
samePlatformAcrossStagesImpliesSameAuthority = false

samePlatformAcrossStagesImpliesSameDeployment : Bool
samePlatformAcrossStagesImpliesSameDeployment = false

------------------------------------------------------------------------
-- Source/authority interpretation.
------------------------------------------------------------------------

stageReceiptCreatesHostileAttribution : Bool
stageReceiptCreatesHostileAttribution = false

stageReceiptCreatesLegalWeaponStatus : Bool
stageReceiptCreatesLegalWeaponStatus = false

stageReceiptCreatesTargetingAuthority : Bool
stageReceiptCreatesTargetingAuthority = false

stageReceiptCreatesUseOfForceAuthority : Bool
stageReceiptCreatesUseOfForceAuthority = false

humanRightsAnchor : HumanRights.OpenCivilianHumanRightsBoundary
humanRightsAnchor = HumanRights.canonicalOpenCivilianHumanRightsBoundary

record CapabilityEscalationBoundary : Set where
  constructor capability-escalation-boundary
  field
    stagesRemainDistinct : Bool
    promotionRequiresStageLocalEvidence : Bool
    navigationImpliesTargetNomination : Bool
    classificationImpliesForceAuthority : Bool
    payloadImpliesAutonomousForce : Bool
    samePlatformImpliesSameAuthority : Bool
    auditGraphIsWeaponizationRoadmap : Bool

canonicalCapabilityEscalationBoundary : CapabilityEscalationBoundary
canonicalCapabilityEscalationBoundary =
  capability-escalation-boundary
    true true false false false false false
