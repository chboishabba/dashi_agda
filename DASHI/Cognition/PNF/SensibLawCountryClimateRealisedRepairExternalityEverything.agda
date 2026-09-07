module DASHI.Cognition.PNF.SensibLawCountryClimateRealisedRepairExternalityEverything where

------------------------------------------------------------------------
-- COUNTRY / CLIMATE / REALISED REPAIR / EXTERNALITY CAPSTONE
--
-- Preferred surface for this tranche. All external-source propositions remain
-- owned by their existing source-bounded modules. This file only composes the
-- theorem surfaces and pins no-collapse boundaries.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.TerminalRealisationValidationExact as Terminal
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Environment.LESCountryExternalityRealisationExact as LESCountry
import DASHI.Environment.LESSituatedSocioEcologicalHyperfabricExact as LES
import DASHI.Cognition.PNF.SensibLawCountryRemedyTerminalValidationCrossPollinationExact as Cross
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Country
import DASHI.Cognition.PNF.SensibLawTerraNulliusFoundationalJuridicalPersonhoodExact as Personhood
import DASHI.Cognition.PNF.SensibLawTerraNulliusTwoEyedSystemContinuityExact as Continuity
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as BillyRealised
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence

------------------------------------------------------------------------
-- Foundational legal reality: machinery was there; constitutive standing was
-- denied by the Crown-acquisition observer.
------------------------------------------------------------------------

indigenousLawWasActuallyPresent :
  Personhood.lawActuallyPresent Personhood.terraNulliusFoundationalJuridicalPersonhood
  ≡ true
indigenousLawWasActuallyPresent = refl

indigenousPolityWasActuallyPresent :
  Personhood.polityActuallyPresent Personhood.terraNulliusFoundationalJuridicalPersonhood
  ≡ true
indigenousPolityWasActuallyPresent = refl

indigenousOccupancyWasActuallyPresent :
  Personhood.occupancyActuallyPresent Personhood.terraNulliusFoundationalJuridicalPersonhood
  ≡ true
indigenousOccupancyWasActuallyPresent = refl

crownAcquisitionRelationErasedConstitutiveStanding :
  Personhood.personhoodState Personhood.terraNulliusFoundationalJuridicalPersonhood
  ≡ Personhood.juridicallyErasedActor
crownAcquisitionRelationErasedConstitutiveStanding = refl

terraNulliusClassificationIsJuridicalFunctional :
  Personhood.classificationIsLegalFunctional
    Personhood.terraNulliusRelationIndexedJuridicalNonHumanity ≡ true
terraNulliusClassificationIsJuridicalFunctional = refl

terraNulliusClassificationIsNotBiologicalTaxonomy :
  Personhood.classificationIsBiologicalTaxonomy
    Personhood.terraNulliusRelationIndexedJuridicalNonHumanity ≡ false
terraNulliusClassificationIsNotBiologicalTaxonomy = refl

------------------------------------------------------------------------
-- Doctrinal correction != transformed relation.
------------------------------------------------------------------------

doctrineRejectedButLandControlStillOpen :
  Continuity.currentCoordinateState Continuity.doctrineRejected ≡ Continuity.paid
  × Continuity.currentCoordinateState Continuity.landCountryControl ≡ Continuity.open
doctrineRejectedButLandControlStillOpen = refl , refl

communityAuthorityStillOpen :
  Continuity.currentCoordinateState Continuity.communityAuthorityBearing ≡ Continuity.open
communityAuthorityStillOpen = refl

compensationReparationStillOpen :
  Continuity.currentCoordinateState Continuity.compensationAndReparationRealised ≡ Continuity.open
compensationReparationStillOpen = refl

------------------------------------------------------------------------
-- Billy: source-backed remedy requirement remains distinct from realised state.
------------------------------------------------------------------------

committeeViolationReceiptRemainsCommitteeOwned :
  Billy.sourceKind Billy.committeeViolationFinding ≡ Billy.humanRightsCommitteeView
committeeViolationReceiptRemainsCommitteeOwned = refl

committeeFullReparationReceiptRemainsCommitteeOwned :
  Billy.sourceKind Billy.committeeFullReparationRequirement ≡ Billy.humanRightsCommitteeView
committeeFullReparationReceiptRemainsCommitteeOwned = refl

fullReparationStillResidual :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
fullReparationStillResidual = refl

consultationObserverCannotRecoverCommunityOutcome :
  INF.FactorsThrough
    BillyRealised.administrativeConsultationObserver
    BillyRealised.communityConsultationOutcome → ⊥
consultationObserverCannotRecoverCommunityOutcome =
  BillyRealised.administrativeConsultationCannotRecoverCommunityOutcome

------------------------------------------------------------------------
-- Terminal validation analogy.
------------------------------------------------------------------------

terminalBoundary : Terminal.TerminalRealisationBoundary
terminalBoundary = Terminal.canonicalTerminalRealisationBoundary

fundingIsNotTerminalRealisation :
  Terminal.fundingEqualsRealisation terminalBoundary ≡ false
fundingIsNotTerminalRealisation = refl

recognitionIsNotTerminalRealisation :
  Terminal.recognitionEqualsRealisation terminalBoundary ≡ false
recognitionIsNotTerminalRealisation = refl

consultationIsNotTerminalRealisation :
  Terminal.consultationEqualsRealisation terminalBoundary ≡ false
consultationIsNotTerminalRealisation = refl

------------------------------------------------------------------------
-- LES / Country externalities remain multi-coordinate.
------------------------------------------------------------------------

countryExternalityBoundary : LESCountry.ExternalityAccountingBoundary
countryExternalityBoundary = LESCountry.canonicalExternalityAccountingBoundary

marketRevenueDoesNotExhaustCountry :
  LESCountry.marketRevenueExhaustsCountryValue countryExternalityBoundary ≡ false
marketRevenueDoesNotExhaustCountry = refl

carbonPriceDoesNotExhaustClimateValue :
  LESCountry.carbonPriceExhaustsClimateValue countryExternalityBoundary ≡ false
carbonPriceDoesNotExhaustClimateValue = refl

carbonDoesNotExhaustCommunityAuthority :
  LESCountry.carbonMetricExhaustsCommunityAuthority countryExternalityBoundary ≡ false
carbonDoesNotExhaustCommunityAuthority = refl

unpricedEcologicalRelationDoesNotDisappear :
  LESCountry.unpricedEffectMeansEffectDoesNotExist countryExternalityBoundary ≡ false
unpricedEcologicalRelationDoesNotDisappear = refl

countryIsNotAssetByDefault :
  LESCountry.countryRelationIsAssetByDefault countryExternalityBoundary ≡ false
countryIsNotAssetByDefault = refl

communityAuthorityIsNotPropertyRightByDefault :
  LESCountry.communityAuthorityIsPropertyRightByDefault countryExternalityBoundary ≡ false
communityAuthorityIsNotPropertyRightByDefault = refl

lesCoarseObservationStillCannotRecoverPlanningSignature :
  INF.FactorsThrough LES.fullCoarseObservation LES.fullPlanningSignature → ⊥
lesCoarseObservationStillCannotRecoverPlanningSignature =
  LES.fullCoarseSummaryCannotRecoverFullPlanningSignature

------------------------------------------------------------------------
-- Duty of care: rich climate evidence still traverses separate legal gates.
------------------------------------------------------------------------

foreseeabilityIsFactualCoordinate :
  Negligence.classifyDutyIssue Climate.reasonableForeseeability
  ≡ Negligence.factualDutyFeature
foreseeabilityIsFactualCoordinate = refl

vulnerabilityIsRelationalCoordinate :
  Negligence.classifyDutyIssue Climate.vulnerability
  ≡ Negligence.relationalDutyFeature
vulnerabilityIsRelationalCoordinate = refl

corePolicyIsInstitutionalCoordinate :
  Negligence.classifyDutyIssue Climate.coreGovernmentPolicy
  ≡ Negligence.institutionalDutyConstraint
corePolicyIsInstitutionalCoordinate = refl

causationIsSeparateNegligenceElement :
  Negligence.classifyDutyIssue Climate.causation
  ≡ Negligence.downstreamNegligenceElement
causationIsSeparateNegligenceElement = refl

climateScienceDoesNotManufactureDuty :
  Climate.ClimateScienceFindingAutomaticallyCreatesDuty → ⊥
climateScienceDoesNotManufactureDuty = Climate.scienceDoesNotAutomaticallyCreatePrivateDuty

pabaiDoesNotCloseEveryReformulatedClimateDuty :
  Climate.PabaiNoDutyClosesEveryPossibleClimateDuty → ⊥
pabaiDoesNotCloseEveryReformulatedClimateDuty =
  Climate.pabaiDoesNotCloseEveryReformulatedDutyByDefinition

------------------------------------------------------------------------
-- A system is what it does: self-report is not the terminal consumer.
------------------------------------------------------------------------

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

correctionHandlingIsPartOfOperation :
  POSIWID.correctionResponseIsPartOfObservableOperation posiwidBoundary ≡ true
correctionHandlingIsPartOfOperation = refl

missionStatementCannotOverrideRepeatedOutcome :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
missionStatementCannotOverrideRepeatedOutcome = refl

------------------------------------------------------------------------
-- Current realised-justice cut.
------------------------------------------------------------------------

data RealisedJusticeTerminalCoordinate : Set where
  equalSovereignStanding : RealisedJusticeTerminalCoordinate
  landCountryControl : RealisedJusticeTerminalCoordinate
  communityAuthority : RealisedJusticeTerminalCoordinate
  compensationReparation : RealisedJusticeTerminalCoordinate
  materialSafety : RealisedJusticeTerminalCoordinate
  culturalContinuity : RealisedJusticeTerminalCoordinate
  ecologicalClimateIntegrity : RealisedJusticeTerminalCoordinate
  correctionPrevention : RealisedJusticeTerminalCoordinate


data CurrentTerminalState : Set where
  paid : CurrentTerminalState
  partial : CurrentTerminalState
  open : CurrentTerminalState
  sourceOutcomeRequired : CurrentTerminalState


currentTerminalState : RealisedJusticeTerminalCoordinate → CurrentTerminalState
currentTerminalState equalSovereignStanding = open
currentTerminalState landCountryControl = open
currentTerminalState communityAuthority = open
currentTerminalState compensationReparation = open
currentTerminalState materialSafety = sourceOutcomeRequired
currentTerminalState culturalContinuity = sourceOutcomeRequired
currentTerminalState ecologicalClimateIntegrity = sourceOutcomeRequired
currentTerminalState correctionPrevention = sourceOutcomeRequired

------------------------------------------------------------------------
-- Source-attribution constitution for this capstone.
------------------------------------------------------------------------

record CrossPollinationAttributionBoundary : Set where
  constructor cross-pollination-attribution-boundary
  field
    hrcOwnsTerminalPayerAnalogy : Bool
    hrcOwnsTerminalPayerAnalogyIsFalse : hrcOwnsTerminalPayerAnalogy ≡ false
    pabaiOwnsLESExternalityCarrier : Bool
    pabaiOwnsLESExternalityCarrierIsFalse : pabaiOwnsLESExternalityCarrier ≡ false
    kimmererOwnsNegligenceRule : Bool
    kimmererOwnsNegligenceRuleIsFalse : kimmererOwnsNegligenceRule ≡ false
    maboCourtOwnsPOSIWIDSynthesis : Bool
    maboCourtOwnsPOSIWIDSynthesisIsFalse : maboCourtOwnsPOSIWIDSynthesis ≡ false
    sharedFormalTopologyTransfersLegalAuthority : Bool
    sharedFormalTopologyTransfersLegalAuthorityIsFalse :
      sharedFormalTopologyTransfersLegalAuthority ≡ false
    exactSourcePropositionsRemainUpstreamOwned : Bool
    exactSourcePropositionsRemainUpstreamOwnedIsTrue :
      exactSourcePropositionsRemainUpstreamOwned ≡ true

open CrossPollinationAttributionBoundary public

canonicalCrossPollinationAttributionBoundary : CrossPollinationAttributionBoundary
canonicalCrossPollinationAttributionBoundary = cross-pollination-attribution-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl
