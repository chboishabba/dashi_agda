module DASHI.Cognition.OpenCivilianSpatialDefenseTerminalMaxCutExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.OpenCivilianSpatialDefenseRFObservationExact as RF
import DASHI.Cognition.OpenCivilianSpatialDefenseRobotHumanRightsExact as Rights
import DASHI.Cognition.OpenCivilianSpatialDefenseBostonDynamicsControlExact as Boston
import DASHI.Cognition.OpenCivilianSpatialDefenseConsumerSufficiencyExact as Sufficiency
import DASHI.Cognition.OpenCivilianSpatialDefenseMobilityEnvelopeExact as Envelope
import DASHI.Cognition.OpenCivilianSpatialDefenseCapabilityEscalationExact as Escalation

------------------------------------------------------------------------
-- TERMINAL MAX-CUT LEDGER
--
-- Paid here means only that the repository now contains the named structural
-- carrier/boundary/theorem.  It does not mean that a particular deployment,
-- robot, emitter, venue, model, or civilian outcome has been empirically
-- validated.  Those empirical same-object joins remain explicit open leaves.
------------------------------------------------------------------------

structuralCivilianDefenseTranchePaid : Bool
structuralCivilianDefenseTranchePaid = true

passiveRFObservationBoundaryPaid : Bool
passiveRFObservationBoundaryPaid = true

rfVisualSameObjectFusionCarrierPaid : Bool
rfVisualSameObjectFusionCarrierPaid = true

singleBearingConsumerNonDescentPaid : Bool
singleBearingConsumerNonDescentPaid =
  Sufficiency.singleBearingExactWorldNonDescentPaid

humanRightsPurposeBoundaryPaid : Bool
humanRightsPurposeBoundaryPaid = true

meaningfulHumanControlCarrierPaid : Bool
meaningfulHumanControlCarrierPaid = true

bostonDynamicsBenignControlBoundaryPaid : Bool
bostonDynamicsBenignControlBoundaryPaid = true

uncertainMobilityEnvelopeCarrierPaid : Bool
uncertainMobilityEnvelopeCarrierPaid = true

capabilityEscalationAuditGraphPaid : Bool
capabilityEscalationAuditGraphPaid = true

------------------------------------------------------------------------
-- Open empirical / same-object leaves.
------------------------------------------------------------------------

exactRFReceiverCalibrationPaid : Bool
exactRFReceiverCalibrationPaid = false

exactDeploymentGeometryPaid : Bool
exactDeploymentGeometryPaid = false

realRobotEmitterSameObjectJoinPaid : Bool
realRobotEmitterSameObjectJoinPaid = false

realRobotVisualRFTrackJoinPaid : Bool
realRobotVisualRFTrackJoinPaid = false

realRobotOperatorMissionPayloadJoinPaid : Bool
realRobotOperatorMissionPayloadJoinPaid = false

independentBostonDeploymentComplianceValidationPaid : Bool
independentBostonDeploymentComplianceValidationPaid = false

mobilityEnvelopeHeldOutAccuracyPaid : Bool
mobilityEnvelopeHeldOutAccuracyPaid = false

civilianWarningFalsePositiveCalibrationPaid : Bool
civilianWarningFalsePositiveCalibrationPaid = false

civilianProtectionOutcomeValidationPaid : Bool
civilianProtectionOutcomeValidationPaid = false

counterfactualHarmPreventionPaid : Bool
counterfactualHarmPreventionPaid = false

exactHeadKernelReceiptPaid : Bool
exactHeadKernelReceiptPaid = false

------------------------------------------------------------------------
-- Terminal promotion boundaries.
------------------------------------------------------------------------

structuralModelImpliesFieldedSystem : Bool
structuralModelImpliesFieldedSystem = false

fieldedSensorImpliesExactRobotIdentification : Bool
fieldedSensorImpliesExactRobotIdentification = false

robotIdentificationImpliesHostileAttribution : Bool
robotIdentificationImpliesHostileAttribution = false

hostileAttributionImpliesCountermeasureAuthority : Bool
hostileAttributionImpliesCountermeasureAuthority = false

countermeasureAuthorityImpliesUseOfForceAuthority : Bool
countermeasureAuthorityImpliesUseOfForceAuthority = false

civilianWarningCapabilityImpliesProvenOutcomeEffect : Bool
civilianWarningCapabilityImpliesProvenOutcomeEffect = false

------------------------------------------------------------------------
-- Owner anchors stop this ledger from drifting into an independent ontology.
------------------------------------------------------------------------

rfBoundaryAnchor : RF.OpenCivilianRFBoundary
rfBoundaryAnchor = RF.canonicalOpenCivilianRFBoundary

rightsBoundaryAnchor : Rights.OpenCivilianHumanRightsBoundary
rightsBoundaryAnchor = Rights.canonicalOpenCivilianHumanRightsBoundary

bostonBoundaryAnchor : Boston.BostonDynamicsControlBoundary
bostonBoundaryAnchor = Boston.canonicalBostonDynamicsControlBoundary

sufficiencyBoundaryAnchor : Sufficiency.CivilianConsumerSufficiencyBoundary
sufficiencyBoundaryAnchor = Sufficiency.canonicalCivilianConsumerSufficiencyBoundary

envelopeBoundaryAnchor : Envelope.MobilityEnvelopeBoundary
envelopeBoundaryAnchor = Envelope.canonicalMobilityEnvelopeBoundary

escalationBoundaryAnchor : Escalation.CapabilityEscalationBoundary
escalationBoundaryAnchor = Escalation.canonicalCapabilityEscalationBoundary

record OpenCivilianSpatialDefenseTerminalBoundary : Set where
  constructor open-civilian-spatial-defense-terminal-boundary
  field
    structuralTranchePaid : Bool
    empiricalCalibrationPaid : Bool
    realRobotSameObjectJoinPaid : Bool
    civilianOutcomeEffectPaid : Bool
    kernelReceiptPaid : Bool
    structuralModelPromotesToFieldedSystem : Bool
    warningPromotesToForceAuthority : Bool

canonicalOpenCivilianSpatialDefenseTerminalBoundary :
  OpenCivilianSpatialDefenseTerminalBoundary
canonicalOpenCivilianSpatialDefenseTerminalBoundary =
  open-civilian-spatial-defense-terminal-boundary
    true false false false false false false
