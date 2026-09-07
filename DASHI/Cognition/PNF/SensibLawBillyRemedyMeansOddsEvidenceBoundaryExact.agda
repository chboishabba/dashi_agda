module DASHI.Cognition.PNF.SensibLawBillyRemedyMeansOddsEvidenceBoundaryExact where

------------------------------------------------------------------------
-- BILLY REMEDY: MEANS != ODDS
--
-- The upstream sources identify remedy requirements, Australian implementation
-- activity and available institutional routes.  They do not provide a calibrated
-- probability distribution for full reparation.  This owner prevents the route
-- topology from being silently promoted into numeric odds.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawBillyRemedyOperationalRealisationBidiExact as Realisation
import DASHI.Cognition.PNF.SensibLawCountrySystemRealisedJusticeBidiExact as Country

------------------------------------------------------------------------
-- Evidence kinds.
------------------------------------------------------------------------

data MeansEvidenceKind : Set where
  committeeSpecifiedRemedy : MeansEvidenceKind
  stateReportedImplementation : MeansEvidenceKind
  domesticInstitutionalCapability : MeansEvidenceKind
  treatyBodyFollowUpCapability : MeansEvidenceKind
  communityNegotiationCapability : MeansEvidenceKind


data OddsEvidenceKind : Set where
  calibratedBaseRate : OddsEvidenceKind
  comparableCaseFrequency : OddsEvidenceKind
  identifiedTransitionProbability : OddsEvidenceKind
  sourceReportedProbability : OddsEvidenceKind
  noCalibratedOddsEvidence : OddsEvidenceKind


record MeansReceipt : Set where
  constructor means-receipt
  field
    kind : MeansEvidenceKind
    mechanism : Billy.ImplementationMechanism
    strength : Billy.MechanismStrength
    strengthExact : strength ≡ Billy.mechanismStrength mechanism
    canContributeToRealisation : Bool
    reference : String

open MeansReceipt public

executiveMeans : MeansReceipt
executiveMeans = means-receipt
  domesticInstitutionalCapability
  Billy.stateExecutiveImplementation
  Billy.availableDirect refl
  true
  "Executive implementation is a direct domestic route where lawful power, appropriation and implementation capacity exist."

parliamentaryMeans : MeansReceipt
parliamentaryMeans = means-receipt
  domesticInstitutionalCapability
  Billy.parliamentaryAppropriationOrLegislation
  Billy.availableDirect refl
  true
  "Parliament can legislate and appropriate where durable legal/fiscal machinery is required."

communityNegotiatedMeans : MeansReceipt
communityNegotiatedMeans = means-receipt
  communityNegotiationCapability
  Billy.communityNegotiatedAgreement
  Billy.availableDirect refl
  true
  "Negotiated implementation can directly shape a remedy but does not transfer affected-community authority to the State."

treatyFollowUpMeans : MeansReceipt
treatyFollowUpMeans = means-receipt
  treatyBodyFollowUpCapability
  Billy.treatyBodyFollowUpProcedure
  Billy.availableIndirect refl
  true
  "Human Rights Committee follow-up supplies scrutiny/pressure but is not a self-executing Australian writ."

------------------------------------------------------------------------
-- What would be needed for genuine odds.
------------------------------------------------------------------------

record OddsCalibrationRequirements : Set where
  constructor odds-calibration-requirements
  field
    outcomeDefinitionFixed : Bool
    comparablePopulationDefined : Bool
    observationWindowDefined : Bool
    transitionFrequencyObserved : Bool
    censoringAndSelectionModelled : Bool
    institutionalRegimeComparable : Bool
    communityDefinedClosureOperationalised : Bool
    numericProbabilitySourceRecovered : Bool

open OddsCalibrationRequirements public

currentOddsCalibration : OddsCalibrationRequirements
currentOddsCalibration = odds-calibration-requirements
  true false false false false false false false

record NumericOddsBoundary : Set where
  constructor numeric-odds-boundary
  field
    implementationMeansExist : Bool
    implementationMeansExistIsTrue : implementationMeansExist ≡ true
    mechanismAvailabilityDeterminesProbability : Bool
    mechanismAvailabilityDeterminesProbabilityIsFalse :
      mechanismAvailabilityDeterminesProbability ≡ false
    publicActivityDeterminesFullReparationProbability : Bool
    publicActivityDeterminesFullReparationProbabilityIsFalse :
      publicActivityDeterminesFullReparationProbability ≡ false
    currentSourcesSupportNumericProbability : Bool
    currentSourcesSupportNumericProbabilityIsFalse :
      currentSourcesSupportNumericProbability ≡ false
    qualitativeProspectLabelsAreSourceReportedOdds : Bool
    qualitativeProspectLabelsAreSourceReportedOddsIsFalse :
      qualitativeProspectLabelsAreSourceReportedOdds ≡ false
    numericOddsRequireCalibrationEvidence : Bool
    numericOddsRequireCalibrationEvidenceIsTrue :
      numericOddsRequireCalibrationEvidence ≡ true

open NumericOddsBoundary public

canonicalNumericOddsBoundary : NumericOddsBoundary
canonicalNumericOddsBoundary = numeric-odds-boundary
  true refl
  false refl
  false refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- Qualitative prospect labels are planning classifications only.
------------------------------------------------------------------------

record QualitativeProspectAttributionBoundary : Set where
  constructor qualitative-prospect-attribution-boundary
  field
    label : Billy.PracticalProspect
    coordinate : Billy.RemedyCoordinate
    labelOwnedByBillySource : Bool
    labelOwnedByBillySourceIsFalse : labelOwnedByBillySource ≡ false
    labelIsDASHIPlanningClassification : Bool
    labelIsDASHIPlanningClassificationIsTrue :
      labelIsDASHIPlanningClassification ≡ true
    labelMeansGuaranteedOutcome : Bool
    labelMeansGuaranteedOutcomeIsFalse : labelMeansGuaranteedOutcome ≡ false
    labelMeansNumericProbabilityBand : Bool
    labelMeansNumericProbabilityBandIsFalse : labelMeansNumericProbabilityBand ≡ false

open QualitativeProspectAttributionBoundary public

compensationProspectBoundary : QualitativeProspectAttributionBoundary
compensationProspectBoundary = qualitative-prospect-attribution-boundary
  (Billy.prospectFor Billy.adequateCompensation)
  Billy.adequateCompensation
  false refl
  true refl
  false refl
  false refl

consultationProspectBoundary : QualitativeProspectAttributionBoundary
consultationProspectBoundary = qualitative-prospect-attribution-boundary
  (Billy.prospectFor Billy.meaningfulConsultation)
  Billy.meaningfulConsultation
  false refl
  true refl
  false refl
  false refl

------------------------------------------------------------------------
-- Current operational state: means exist, full reparation remains open.
------------------------------------------------------------------------

fullReparationStillOpen :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
fullReparationStillOpen = refl

compensationPublicReceiptStillUnrecovered :
  Billy.publicImplementationState Billy.adequateCompensation
  ≡ Billy.publicReceiptNotRecovered
compensationPublicReceiptStillUnrecovered = refl

consultationPublicEvidenceExists :
  Billy.publicImplementationState Billy.meaningfulConsultation
  ≡ Billy.publicEvidencePresent
consultationPublicEvidenceExists = refl

landCountryControlStillOperationallyOpen :
  Country.currentOperationalJusticeState Country.landAndCountryControl
  ≡ Country.residualOpen
landCountryControlStillOperationallyOpen = refl

compensationReparationStillOperationallyOpen :
  Country.currentOperationalJusticeState Country.compensationAndReparation
  ≡ Country.residualOpen
compensationReparationStillOperationallyOpen = refl

------------------------------------------------------------------------
-- Means route to producers; odds route to missing calibration evidence.
------------------------------------------------------------------------

data RemedyQuestion : Set where
  howCouldCompensationBeImplemented : RemedyQuestion
  howCouldFullReparationBeImplemented : RemedyQuestion
  whatIsProbabilityOfFullReparation : RemedyQuestion
  whatIsProbabilityOfCompensation : RemedyQuestion


data NextWork : Set where
  inspectExecutiveAndAppropriationAuthority : NextWork
  inspectCommunityNegotiatedImplementation : NextWork
  recoverExecutionAndOutcomeReceipts : NextWork
  buildComparableCaseCalibrationDataset : NextWork
  recoverSourceReportedProbabilityIfAny : NextWork


nextWork : RemedyQuestion → NextWork
nextWork howCouldCompensationBeImplemented = inspectExecutiveAndAppropriationAuthority
nextWork howCouldFullReparationBeImplemented = recoverExecutionAndOutcomeReceipts
nextWork whatIsProbabilityOfFullReparation = buildComparableCaseCalibrationDataset
nextWork whatIsProbabilityOfCompensation = buildComparableCaseCalibrationDataset

meansQuestionRoutesToInstitutionalCapability :
  nextWork howCouldCompensationBeImplemented ≡ inspectExecutiveAndAppropriationAuthority
meansQuestionRoutesToInstitutionalCapability = refl

oddsQuestionRoutesToCalibration :
  nextWork whatIsProbabilityOfFullReparation ≡ buildComparableCaseCalibrationDataset
oddsQuestionRoutesToCalibration = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data DirectMechanismMeansHighProbability : Set where
data TreatyBodyFindingMeansDomesticExecution : Set where
data PublicConsultationMeansFullRemedy : Set where
data QualitativeProspectMeansNumericOdds : Set where
data MissingPublicReceiptMeansNoPrivateOrUnpublishedImplementation : Set where

directMechanismDoesNotDetermineHighProbability : DirectMechanismMeansHighProbability → ⊥
directMechanismDoesNotDetermineHighProbability ()

committeeFindingDoesNotSelfExecute : TreatyBodyFindingMeansDomesticExecution → ⊥
committeeFindingDoesNotSelfExecute ()

consultationDoesNotCloseFullRemedy : PublicConsultationMeansFullRemedy → ⊥
consultationDoesNotCloseFullRemedy ()

qualitativeProspectDoesNotBecomeNumericOdds : QualitativeProspectMeansNumericOdds → ⊥
qualitativeProspectDoesNotBecomeNumericOdds ()

missingPublicReceiptDoesNotProveNoUnpublishedImplementation :
  MissingPublicReceiptMeansNoPrivateOrUnpublishedImplementation → ⊥
missingPublicReceiptDoesNotProveNoPrivateOrUnpublishedImplementation ()
