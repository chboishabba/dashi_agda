module DASHI.Cognition.OpenCivilianSpatialDefenseRobotHumanRightsExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SensibLawOntologyTopology as Sensib
import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as GEV
import DASHI.Interop.GodsEyeViewWorldOntologyCrossDomainExact as GEVCross
import DASHI.Cognition.ProtectiveSpatialDualUseAntiPanopticonExact as DualUse
import DASHI.Cognition.OpenCivilianSpatialDefenseSourceAtlasExact as Sources

------------------------------------------------------------------------
-- OPEN CIVILIAN SPATIAL DEFENCE: HUMAN-RIGHTS / BAD-TIMELINE BOUNDARY
--
-- The protected aim is civilian safety without converting situational
-- awareness into population-scale identity resolution, arbitrary domination,
-- automated legal-status classification, or machine-mediated force authority.
------------------------------------------------------------------------

data CivilianDefensePurpose : Set where
  publicSafetyAwareness : CivilianDefensePurpose
  emergencyWarning : CivilianDefensePurpose
  evacuationRouting : CivilianDefensePurpose
  shelteringSupport : CivilianDefensePurpose
  humanitarianDocumentation : CivilianDefensePurpose
  protectiveOperations : CivilianDefensePurpose
  publicOrderSurveillance : CivilianDefensePurpose
  intelligenceInvestigation : CivilianDefensePurpose
  militaryTargeting : CivilianDefensePurpose
  useOfForce : CivilianDefensePurpose

data CivilianSafetyResponse : Set where
  observeAndDocument : CivilianSafetyResponse
  alertAndWarn : CivilianSafetyResponse
  rerouteOrEvacuate : CivilianSafetyResponse
  shelterOrAccessControl : CivilianSafetyResponse
  requestHumanResponder : CivilianSafetyResponse

data EscalatedCoerciveResponse : Set where
  persistentIdentityTracking : EscalatedCoerciveResponse
  movementRestriction : EscalatedCoerciveResponse
  targetNomination : EscalatedCoerciveResponse
  interferenceOrDisablement : EscalatedCoerciveResponse
  applicationOfForce : EscalatedCoerciveResponse

passiveCivilianSafetyResponsesDefault : Bool
passiveCivilianSafetyResponsesDefault = true

observationAdmissibilityTransfersAcrossPurposes : Bool
observationAdmissibilityTransfersAcrossPurposes = false

protectiveCollectionCreatesPublicOrderSurveillanceAuthority : Bool
protectiveCollectionCreatesPublicOrderSurveillanceAuthority = false

protectiveCollectionCreatesIntelligenceAuthority : Bool
protectiveCollectionCreatesIntelligenceAuthority = false

protectiveCollectionCreatesMilitaryTargetingAuthority : Bool
protectiveCollectionCreatesMilitaryTargetingAuthority = false

protectiveCollectionCreatesUseOfForceAuthority : Bool
protectiveCollectionCreatesUseOfForceAuthority = false

threatScoreDeterminesLegalCivilianCombatantStatus : Bool
threatScoreDeterminesLegalCivilianCombatantStatus = false

classifierOutputDeterminesLegalStatus : Bool
classifierOutputDeterminesLegalStatus = false

robotPresenceDeterminesHostility : Bool
robotPresenceDeterminesHostility = false

mobilityEnvelopeDeterminesHostility : Bool
mobilityEnvelopeDeterminesHostility = false

humanReviewMayBeCeremonialRubberStamp : Bool
humanReviewMayBeCeremonialRubberStamp = false

leastIntrusiveSufficientObservationPreferred : Bool
leastIntrusiveSufficientObservationPreferred = true

identityResolutionRequiredByDefault : Bool
identityResolutionRequiredByDefault = false

populationSocialGraphRequiredByDefault : Bool
populationSocialGraphRequiredByDefault = false

retentionBeyondDeclaredPurposeRequiredByDefault : Bool
retentionBeyondDeclaredPurposeRequiredByDefault = false

------------------------------------------------------------------------
-- Purpose-bearing observation admission.
------------------------------------------------------------------------

record PurposeBoundObservationAdmission : Set where
  constructor purpose-bound-observation-admission
  field
    observation : GEV.ObservationReceipt
    admittedPurpose : CivilianDefensePurpose
    necessityReference : String
    proportionalityReference : String
    leastIntrusiveAlternativeReference : String
    permittedConsumerReference : String
    retentionReference : String
    accessControlReference : String
    contestabilityReference : String
    remedyReference : String

open PurposeBoundObservationAdmission public

------------------------------------------------------------------------
-- Meaningful human control is stronger than a nominal approval click.
------------------------------------------------------------------------

record MeaningfulHumanControlReceipt : Set where
  constructor meaningful-human-control-receipt
  field
    intelligibleBasisReference : String
    uncertaintyVisibleReference : String
    sufficientDecisionTimeReference : String
    evidenceInspectionReference : String
    rejectOrOverrideCapabilityReference : String
    actualInstitutionalAuthorityReference : String
    responsibilityAndAccountabilityReference : String
    interventionOrDeactivationReference : String

open MeaningfulHumanControlReceipt public

nominalHumanInLoopAlonePaysMeaningfulControl : Bool
nominalHumanInLoopAlonePaysMeaningfulControl = false

meaningfulHumanControlRequiredBeforeForce : Bool
meaningfulHumanControlRequiredBeforeForce = true

------------------------------------------------------------------------
-- Benefit / burden / voice / control remain distinct.
------------------------------------------------------------------------

record CivilianDefenseDistributionalReceipt : Set where
  constructor civilian-defense-distributional-receipt
  field
    protectedBeneficiaryReference : String
    observedPopulationReference : String
    falsePositiveBurdenReference : String
    refusalOrOptOutReference : String
    voiceReference : String
    controllerReference : String
    contestabilityReference : String
    remedyReference : String

open CivilianDefenseDistributionalReceipt public

protectionBenefitImpliesObservationConsent : Bool
protectionBenefitImpliesObservationConsent = false

protectionBenefitImpliesSurveillanceBurdenJustified : Bool
protectionBenefitImpliesSurveillanceBurdenJustified = false

protectedPersonAndObservedPopulationMustBeSame : Bool
protectedPersonAndObservedPopulationMustBeSame = false

------------------------------------------------------------------------
-- Existing anti-panopticon and dual-use anchors.
------------------------------------------------------------------------

antiPanopticonAnchor : GEV.AntiPanopticonBoundary
antiPanopticonAnchor = GEV.canonicalAntiPanopticonBoundary

protectedInterestAnchor : List Sensib.InterestModality
protectedInterestAnchor = GEVCross.antiPanopticonProtectedInterests

dualUseAnchor : DualUse.ProtectiveUseOfForceBoundary
dualUseAnchor = DualUse.canonicalProtectiveUseOfForceBoundary

------------------------------------------------------------------------
-- Source-attribution boundaries.
------------------------------------------------------------------------

icrcPositionSourcePaid : Bool
icrcPositionSourcePaid = true

icrcPositionCreatesBindingTreatyLaw : Bool
icrcPositionCreatesBindingTreatyLaw = false

icrcNormativePositionCreatesCaseSpecificLegalityJudgment : Bool
icrcNormativePositionCreatesCaseSpecificLegalityJudgment = false

sourceAtlasAnchor : Source.AttributedSourceAtlas
sourceAtlasAnchor = Sources.openCivilianSpatialDefenseAtlas

record OpenCivilianHumanRightsBoundary : Set where
  constructor open-civilian-human-rights-boundary
  field
    civilianSafetyIsPrimaryConsumer : Bool
    observationPurposeTransfersAutomatically : Bool
    legalStatusComesFromThreatScore : Bool
    identityResolutionIsDefault : Bool
    leastIntrusiveSufficiencyPreferred : Bool
    meaningfulHumanControlRequiredForForce : Bool
    benefitAndSurveillanceBurdenCollapsed : Bool
    antiPanopticonProtectedInterestsRetained : Bool

canonicalOpenCivilianHumanRightsBoundary : OpenCivilianHumanRightsBoundary
canonicalOpenCivilianHumanRightsBoundary =
  open-civilian-human-rights-boundary
    true false false false true true false true
