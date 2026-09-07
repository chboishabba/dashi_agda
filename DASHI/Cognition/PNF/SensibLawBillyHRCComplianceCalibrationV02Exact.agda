module DASHI.Cognition.PNF.SensibLawBillyHRCComplianceCalibrationV02Exact where

------------------------------------------------------------------------
-- BILLY / HRC COMPLIANCE CALIBRATION V02
--
-- Additive update to SensibLawBillyRemedyMeansOddsEvidenceBoundaryExact.
-- The earlier owner correctly recorded that the then-admitted sources did not
-- contain a comparable numeric reference class.  Later source acquisition now
-- pays part of that evidence debt.  A reference-class rate still does not become
-- a case-specific probability for Billy et al.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawBillyRemedyMeansOddsEvidenceBoundaryExact as Historical
import DASHI.Cognition.PNF.SensibLawBillyEffectiveRemedyTwoEyedSeeingExact as Billy
import DASHI.Cognition.PNF.SensibLawCountryRealisedRepairSourceAtlasV02Exact as Sources

------------------------------------------------------------------------
-- Evidence and mechanism classes.
------------------------------------------------------------------------

data ComplianceEvidenceKind : Set where
  peerReviewedGlobalTreatyBodyDataset
  officialAustraliaQualitativeAssessment
  officialHRCFollowUpProcedure
  separateUPRComparator
  historicalSecondaryAustraliaEstimate
  : ComplianceEvidenceKind

data PopulationRelation : Set where
  sameInstitutionalMechanism
  overlappingTreatyBodyRegime
  separateUNReviewMechanism
  historicalNonCurrentComparator
  : PopulationRelation

record GlobalReferenceClassReceipt : Set where
  constructor global-reference-class-receipt
  field
    evidenceKind : ComplianceEvidenceKind
    studyAuthor : String
    studyTitle : String
    studyDOI : String
    population : String
    publicationWindow : String
    lowerReportedCompliancePercent : Nat
    upperReportedCompliancePercent : Nat
    strictFullComplianceMeanPercent : Nat
    rateDependsOnDefinitionAndMissingValueAssumptions : Bool
    rateDependsOnDefinitionAndMissingValueAssumptionsIsTrue :
      rateDependsOnDefinitionAndMissingValueAssumptions ≡ true
    billyIncludedInDataset : Bool
    billyIncludedInDatasetIsFalse : billyIncludedInDataset ≡ false
    sourceReference : String

open GlobalReferenceClassReceipt public

globalTreatyBodyReference : GlobalReferenceClassReceipt
globalTreatyBodyReference = global-reference-class-receipt
  peerReviewedGlobalTreatyBodyDataset
  "Andreas J. Ullmann; Andreas von Staden"
  "A Room Full of 'Views': Introducing a New Dataset to Explore Compliance with the Decisions of the UN Human Rights Treaty Bodies' Individual Complaints Procedures"
  "10.1177/00220027231160460"
  "Published adverse decisions in UN human-rights treaty-body individual complaints, 1979-2019"
  "1979-2019 decisions; article published 2024"
  19
  39
  23
  true refl
  false refl
  "Ullmann & von Staden, Journal of Conflict Resolution 68(2-3), 534-561 (2024)."

------------------------------------------------------------------------
-- Australia-specific official evidence is currently qualitative, not a current
-- numeric full-compliance rate.
------------------------------------------------------------------------

record AustraliaOfficialComplianceReceipt : Set where
  constructor australia-official-compliance-receipt
  field
    evidenceKind : ComplianceEvidenceKind
    stateSaysGoodFaithConsideration : Bool
    stateSaysGoodFaithConsiderationIsTrue : stateSaysGoodFaithConsideration ≡ true
    committeeReportsRepeatedFailureToImplementViews : Bool
    committeeReportsRepeatedFailureToImplementViewsIsTrue :
      committeeReportsRepeatedFailureToImplementViews ≡ true
    currentAustraliaSpecificNumericFullComplianceRateRecovered : Bool
    currentAustraliaSpecificNumericFullComplianceRateRecoveredIsFalse :
      currentAustraliaSpecificNumericFullComplianceRateRecovered ≡ false
    sourceReference : String

open AustraliaOfficialComplianceReceipt public

australia2017OfficialAssessment : AustraliaOfficialComplianceReceipt
australia2017OfficialAssessment = australia-official-compliance-receipt
  officialAustraliaQualitativeAssessment
  true refl
  true refl
  false refl
  "Human Rights Committee, Concluding observations on Australia's sixth periodic report, CCPR/C/AUS/CO/6, para 9 (2017)."

------------------------------------------------------------------------
-- Follow-up horizon / administrative suspension.
------------------------------------------------------------------------

record FollowUpHorizonReceipt : Set where
  constructor follow-up-horizon-receipt
  field
    initialBillyResponseDays : Nat
    initialResponseRequirementSource : String
    noInformationSuspensionYears : Nat
    suspensionRuleSource : String
    suspensionMeansSubstantiveFailure : Bool
    suspensionMeansSubstantiveFailureIsFalse :
      suspensionMeansSubstantiveFailure ≡ false
    suspensionMeansSubstantiveSuccess : Bool
    suspensionMeansSubstantiveSuccessIsFalse :
      suspensionMeansSubstantiveSuccess ≡ false
    treatingSuspensionAsStatisticalCensoringIsDASHIModelChoice : Bool
    treatingSuspensionAsStatisticalCensoringIsDASHIModelChoiceIsTrue :
      treatingSuspensionAsStatisticalCensoringIsDASHIModelChoice ≡ true

open FollowUpHorizonReceipt public

hrcFollowUpHorizon : FollowUpHorizonReceipt
hrcFollowUpHorizon = follow-up-horizon-receipt
  180
  "Billy and others v Australia, CCPR/C/135/D/3624/2019, para 12."
  5
  "Human Rights Committee, Guidelines on the procedure for follow-up to Views, CCPR/C/162 (2023), para 36."
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- UPR is useful triangulation but is a different procedure.
------------------------------------------------------------------------

record UPRComparatorReceipt : Set where
  constructor upr-comparator-receipt
  field
    evidenceKind : ComplianceEvidenceKind
    supportedRecommendations : Nat
    fullyImplementedPercent : Nat
    partlyImplementedPercent : Nat
    notImplementedPercent : Nat
    relationToBillyMechanism : PopulationRelation
    canBePooledAsSameHRCOptionalProtocolPopulation : Bool
    canBePooledAsSameHRCOptionalProtocolPopulationIsFalse :
      canBePooledAsSameHRCOptionalProtocolPopulation ≡ false
    sourceReference : String

open UPRComparatorReceipt public

australiaUPRComparator : UPRComparatorReceipt
australiaUPRComparator = upr-comparator-receipt
  separateUPRComparator
  177
  6
  86
  7
  separateUNReviewMechanism
  false refl
  "Australian Human Rights Commission submission to Australia's Fourth Universal Periodic Review, 2025."

------------------------------------------------------------------------
-- What the newly recovered evidence actually pays.
------------------------------------------------------------------------

record OddsCalibrationV02 : Set where
  constructor odds-calibration-v02
  field
    outcomeDefinitionFixed : Bool
    comparableGlobalPopulationDefined : Bool
    numericReferenceClassRateRecovered : Bool
    initialObservationHorizonDefined : Bool
    followUpSuspensionRuleIdentified : Bool
    selectionCensoringMechanismPartiallyModelled : Bool
    exactHRCOnlyNumericRateRecovered : Bool
    currentAustraliaSpecificNumericRateRecovered : Bool
    billySpecificProbabilityRecovered : Bool
    communityDefinedFullReparationClosureOperationalised : Bool
    oldHistoricalCalibrationRewritten : Bool

open OddsCalibrationV02 public

currentOddsCalibrationV02 : OddsCalibrationV02
currentOddsCalibrationV02 = odds-calibration-v02
  true
  true
  true
  true
  true
  true
  false
  false
  false
  false
  false

referenceClassRateNowRecovered :
  numericReferenceClassRateRecovered currentOddsCalibrationV02 ≡ true
referenceClassRateNowRecovered = refl

billySpecificProbabilityStillOpen :
  billySpecificProbabilityRecovered currentOddsCalibrationV02 ≡ false
billySpecificProbabilityStillOpen = refl

historicalOwnerWasNotRewritten :
  oldHistoricalCalibrationRewritten currentOddsCalibrationV02 ≡ false
historicalOwnerWasNotRewritten = refl

historicalT0HadNoNumericProbabilitySource :
  Historical.numericProbabilitySourceRecovered Historical.currentOddsCalibration ≡ false
historicalT0HadNoNumericProbabilitySource = refl

------------------------------------------------------------------------
-- Reference-class rate != case probability.
------------------------------------------------------------------------

data ProbabilityQuestion : Set where
  globalTreatyBodyReferenceRate
  currentAustraliaHRCFullComplianceRate
  billyFullReparationProbability
  billyAdequateCompensationProbability
  : ProbabilityQuestion

data CalibrationWork : Set where
  referenceRateAvailable
  recoverAustraliaHRCSubset
  recoverBillyCurrentFollowUpOutcome
  operationaliseCommunityDefinedClosure
  buildCaseConditionedForecast
  : CalibrationWork

nextCalibrationWork : ProbabilityQuestion → CalibrationWork
nextCalibrationWork globalTreatyBodyReferenceRate = referenceRateAvailable
nextCalibrationWork currentAustraliaHRCFullComplianceRate = recoverAustraliaHRCSubset
nextCalibrationWork billyFullReparationProbability = recoverBillyCurrentFollowUpOutcome
nextCalibrationWork billyAdequateCompensationProbability = recoverBillyCurrentFollowUpOutcome

record CaseForecastBoundary : Set where
  constructor case-forecast-boundary
  field
    globalRateIsCaseSpecificForecast : Bool
    globalRateIsCaseSpecificForecastIsFalse : globalRateIsCaseSpecificForecast ≡ false
    uprRateIsHRCOptionalProtocolRate : Bool
    uprRateIsHRCOptionalProtocolRateIsFalse : uprRateIsHRCOptionalProtocolRate ≡ false
    officialRepeatedFailureStatementIsNumericRate : Bool
    officialRepeatedFailureStatementIsNumericRateIsFalse :
      officialRepeatedFailureStatementIsNumericRate ≡ false
    referenceClassCanInformPriorOrCalibration : Bool
    referenceClassCanInformPriorOrCalibrationIsTrue :
      referenceClassCanInformPriorOrCalibration ≡ true
    caseForecastNeedsCurrentCaseAndSubsetEvidence : Bool
    caseForecastNeedsCurrentCaseAndSubsetEvidenceIsTrue :
      caseForecastNeedsCurrentCaseAndSubsetEvidence ≡ true

open CaseForecastBoundary public

canonicalCaseForecastBoundary : CaseForecastBoundary
canonicalCaseForecastBoundary = case-forecast-boundary
  false refl
  false refl
  false refl
  true refl
  true refl

------------------------------------------------------------------------
-- Public remedy state remains independently open.
------------------------------------------------------------------------

fullReparationStillOperationallyLive :
  Billy.currentPublicFullReparationStatus ≡ Billy.fullReparationResidualLive
fullReparationStillOperationallyLive = refl

compensationReceiptStillNotRecoveredInHistoricalPublicAtlas :
  Billy.publicImplementationState Billy.adequateCompensation
  ≡ Billy.publicReceiptNotRecovered
compensationReceiptStillNotRecoveredInHistoricalPublicAtlas = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data GlobalComplianceRateEqualsBillyProbability : Set where
data UPRImplementationRateEqualsHRCViewsRate : Set where
data FiveYearSuspensionMeansRemedyFailure : Set where
data RepeatedFailureStatementEqualsCurrentNumericAustraliaRate : Set where
data ReferenceClassEvidenceClosesFullReparation : Set where

globalRateDoesNotEqualBillyProbability : GlobalComplianceRateEqualsBillyProbability → ⊥
globalRateDoesNotEqualBillyProbability ()

uprDoesNotEqualHRCViewsPopulation : UPRImplementationRateEqualsHRCViewsRate → ⊥
uprDoesNotEqualHRCViewsPopulation ()

suspensionDoesNotByItselfMeanFailure : FiveYearSuspensionMeansRemedyFailure → ⊥
suspensionDoesNotByItselfMeanFailure ()

qualitativeAustraliaFindingDoesNotBecomeNumericRate :
  RepeatedFailureStatementEqualsCurrentNumericAustraliaRate → ⊥
qualitativeAustraliaFindingDoesNotBecomeNumericRate ()

referenceClassDoesNotCloseRemedy : ReferenceClassEvidenceClosesFullReparation → ⊥
referenceClassDoesNotCloseRemedy ()
