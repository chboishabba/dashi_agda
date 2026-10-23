module DASHI.Cognition.VilyaProtectiveSpatialValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.ProtectiveSpatialIntelligenceExact as Core
import DASHI.Cognition.VilyaProtectionSourceAtlasExact as Vilya
import DASHI.Cognition.ProtectiveSpatialDualUseAntiPanopticonExact as DualUse
import DASHI.Cognition.KirkVilyaCounterfactualPreventionBoundaryExact as Kirk
import DASHI.Cognition.VilyaGodsEyeAntiPanopticonWeldExact as Weld
import DASHI.Cognition.SpatialIntelligenceAgentCrossPollinationExact as Agent
import DASHI.Cognition.OpenCivilianSpatialDefenseRFObservationExact as RFDefense
import DASHI.Cognition.OpenCivilianSpatialDefenseRobotHumanRightsExact as HumanRights
import DASHI.Cognition.OpenCivilianSpatialDefenseBostonDynamicsControlExact as Boston
import DASHI.Cognition.OpenCivilianSpatialDefenseConsumerSufficiencyExact as Sufficiency
import DASHI.Cognition.OpenCivilianSpatialDefenseMobilityEnvelopeExact as Envelope
import DASHI.Cognition.OpenCivilianSpatialDefenseCapabilityEscalationExact as Escalation
import DASHI.Cognition.OpenCivilianSpatialDefenseTerminalMaxCutExact as Terminal

gevObservationDoesNotCreateProtectiveAuthority :
  Core.observationCreatesProtectiveAuthority ≡ false
gevObservationDoesNotCreateProtectiveAuthority = refl

vilyaWorkflowKeepsFiveDistinctStages :
  Vilya.fiveStageWorkflowPaid ≡ true
vilyaWorkflowKeepsFiveDistinctStages = refl

vendorClaimsDoNotBecomeValidatedPerformance :
  Vilya.vendorDescriptionCreatesIndependentPerformanceValidation ≡ false
vendorClaimsDoNotBecomeValidatedPerformance = refl

sameSpatialPrimitiveDoesNotFixPurpose :
  DualUse.sameSpatialPrimitiveDeterminesProtectiveOrLethalPurpose ≡ false
sameSpatialPrimitiveDoesNotFixPurpose = refl

autonomousTargetSelectionDoesNotInheritProtectiveAuthority :
  DualUse.protectiveObservationCreatesAutonomousUseOfForceAuthority ≡ false
autonomousTargetSelectionDoesNotInheritProtectiveAuthority = refl

humanLifeDeathAuthorityRequired :
  DualUse.humanControlOverLifeDeathDecisionRequired ≡ true
humanLifeDeathAuthorityRequired = refl

kirkRelevantObservableOmissionPaid :
  Kirk.relevantProtectiveObservableOmissionPaid ≡ true
kirkRelevantObservableOmissionPaid = refl

vilyaWouldHavePreventedKirkNotPaid :
  Kirk.vilyaWouldHavePreventedKirkPaid ≡ false
vilyaWouldHavePreventedKirkNotPaid = refl

capabilityRelevanceDoesNotPayCausalPrevention :
  Kirk.capabilityAddressesOmittedObservableImpliesPrevention ≡ false
capabilityRelevanceDoesNotPayCausalPrevention = refl

sharedWorldStateDoesNotTransferOperationalAuthority :
  Weld.sharedSpatialStateTransfersOperationalAuthority ≡ false
sharedWorldStateDoesNotTransferOperationalAuthority = refl

privacyAndNonDominationSurviveProtectiveProjection :
  Weld.privacyAndNonDominationRemainProtected ≡ true
privacyAndNonDominationSurviveProtectiveProjection = refl

publicObservationAndProtectiveOperationsRemainDistinct :
  Weld.godsEyeViewEqualsVilyaOperationalSystem ≡ false
publicObservationAndProtectiveOperationsRemainDistinct = refl

geospatialAgentCanOrchestrateSpatialTools :
  Agent.geospatialReasoningAgentPatternPaid ≡ true
geospatialAgentCanOrchestrateSpatialTools = refl

reasoningAgentDoesNotCreateOperationalAuthority :
  Agent.reasoningAgentCreatesProtectiveAuthority ≡ false
reasoningAgentDoesNotCreateOperationalAuthority = refl

reasoningAgentDoesNotCreateUseOfForceAuthority :
  Agent.reasoningAgentCreatesUseOfForceAuthority ≡ false
reasoningAgentDoesNotCreateUseOfForceAuthority = refl

------------------------------------------------------------------------
-- Open Civilian Spatial Defence / RF / robot regression tranche.
------------------------------------------------------------------------

singleBearingDoesNotDetermineExactRobotWorld :
  RFDefense.singleBearingDeterminesExactRobotWorld ≡ false
singleBearingDoesNotDetermineExactRobotWorld = refl

rfVisualFusionRequiresSameObjectReceipt :
  RFDefense.rfVisualFusionRequiresSameObjectReceipt ≡ true
rfVisualFusionRequiresSameObjectReceipt = refl

passiveRFObservationDoesNotCreateHostileAttribution :
  RFDefense.passiveRFObservationCreatesHostileAttribution ≡ false
passiveRFObservationDoesNotCreateHostileAttribution = refl

passiveRFObservationDoesNotCreateJammingAuthority :
  RFDefense.passiveRFObservationCreatesJammingAuthority ≡ false
passiveRFObservationDoesNotCreateJammingAuthority = refl

passiveRFObservationDoesNotCreateUseOfForceAuthority :
  RFDefense.passiveRFObservationCreatesUseOfForceAuthority ≡ false
passiveRFObservationDoesNotCreateUseOfForceAuthority = refl

civilianDefenceDefaultsToWarningAvoidanceShelter :
  HumanRights.passiveCivilianSafetyResponsesDefault ≡ true
civilianDefenceDefaultsToWarningAvoidanceShelter = refl

threatScoreDoesNotDetermineCivilianCombatantStatus :
  HumanRights.threatScoreDeterminesLegalCivilianCombatantStatus ≡ false
threatScoreDoesNotDetermineCivilianCombatantStatus = refl

purposeAdmissionDoesNotTransferAcrossConsumers :
  HumanRights.observationAdmissibilityTransfersAcrossPurposes ≡ false
purposeAdmissionDoesNotTransferAcrossConsumers = refl

leastIntrusiveSufficientObservationRequired :
  HumanRights.leastIntrusiveSufficientObservationPreferred ≡ true
leastIntrusiveSufficientObservationRequired = refl

robotMorphologyDoesNotDetermineHostileFunction :
  Boston.robotMorphologyDeterminesHostileFunction ≡ false
robotMorphologyDoesNotDetermineHostileFunction = refl

BostonDynamicsVendorPolicyIsNotUniversalLaw :
  Boston.vendorAntiWeaponizationPolicyCreatesUniversalLegalConstraint ≡ false
BostonDynamicsVendorPolicyIsNotUniversalLaw = refl

BostonDynamicsGeneralPurposeRobotIsBenignControlEligible :
  Boston.generalPurposeNonWeaponizedControlEligible ≡ true
BostonDynamicsGeneralPurposeRobotIsBenignControlEligible = refl

singleBearingConsumerNonDescentIsPaid :
  Sufficiency.singleBearingExactWorldNonDescentPaid ≡ true
singleBearingConsumerNonDescentIsPaid = refl

consumerRelativeMinimalityCoreIsReused :
  Sufficiency.consumerDescentMinimalObserverCoreReused ≡ true
consumerRelativeMinimalityCoreIsReused = refl

mobilityEnvelopeSupportsWarningAvoidance :
  Envelope.mobilityEnvelopeSupportsWarningAndAvoidance ≡ true
mobilityEnvelopeSupportsWarningAvoidance = refl

mobilityEnvelopeDoesNotEstablishHostility :
  Envelope.mobilityEnvelopeDeterminesHostility ≡ false
mobilityEnvelopeDoesNotEstablishHostility = refl

mobilityEnvelopeDoesNotCreateCountermeasureAuthority :
  Envelope.mobilityEnvelopeCreatesInterferenceAuthority ≡ false
mobilityEnvelopeDoesNotCreateCountermeasureAuthority = refl

autonomousLocomotionDoesNotPromoteToTargetNomination :
  Escalation.autonomousLocomotionImpliesTargetNomination ≡ false
autonomousLocomotionDoesNotPromoteToTargetNomination = refl

capabilityGraphHasNoAutomaticEscalation :
  Escalation.capabilityStageAutomaticallyPromotesToNext ≡ false
capabilityGraphHasNoAutomaticEscalation = refl

terminalStructuralTranchePaid :
  Terminal.structuralCivilianDefenseTranchePaid ≡ true
terminalStructuralTranchePaid = refl

terminalEmpiricalRobotEmitterJoinStillOpen :
  Terminal.realRobotEmitterSameObjectJoinPaid ≡ false
terminalEmpiricalRobotEmitterJoinStillOpen = refl

terminalCivilianOutcomeValidationStillOpen :
  Terminal.civilianProtectionOutcomeValidationPaid ≡ false
terminalCivilianOutcomeValidationStillOpen = refl

terminalKernelReceiptStillOpen :
  Terminal.exactHeadKernelReceiptPaid ≡ false
terminalKernelReceiptStillOpen = refl
