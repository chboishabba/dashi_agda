module DASHI.Cognition.PNF.SensibLawCountryRealisedRepairCalibrationV02Exact where

------------------------------------------------------------------------
-- COUNTRY / REALISED REPAIR CALIBRATION V02
--
-- Additive correction to the earlier OPEN-coordinate surface.  This file does
-- not rewrite the historical t0 status.  It attaches later source receipts to
-- particular coordinates and keeps source proposition, interpretation,
-- operational classification and causal explanation separately typed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Cognition.PNF.SensibLawTerraNulliusTwoEyedSystemContinuityExact as Continuity
import DASHI.Cognition.PNF.SensibLawCountryRealisedRepairSourceAtlasV02Exact as Sources
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as IK

------------------------------------------------------------------------
-- Source-backed state vocabulary.
------------------------------------------------------------------------

data CalibrationState : Set where
  sourceMappedPositive
  sourceMappedPartial
  sourceMappedNegativePressure
  structuralConstraintMapped
  comparatorOnly
  liveResidual
  : CalibrationState

------------------------------------------------------------------------
-- Native-title determination coverage != control != sovereignty.
------------------------------------------------------------------------

record NativeTitleCoverageReceipt : Set where
  constructor native-title-coverage-receipt
  field
    determinationCoverageTenthsPercent : Nat
    exclusiveNativeTitleTenthsPercent : Nat
    nonExclusiveNativeTitleApproxTenthsPercent : Nat
    sourceReference : String
    determinationCoverageEqualsIndigenousControl : Bool
    determinationCoverageEqualsIndigenousControlIsFalse :
      determinationCoverageEqualsIndigenousControl ≡ false
    nonExclusiveTitleConfersGeneralExclusionPower : Bool
    nonExclusiveTitleConfersGeneralExclusionPowerIsFalse :
      nonExclusiveTitleConfersGeneralExclusionPower ≡ false
    exclusiveTitleEqualsIndigenousSovereignty : Bool
    exclusiveTitleEqualsIndigenousSovereigntyIsFalse :
      exclusiveTitleEqualsIndigenousSovereignty ≡ false
    exclusiveTitleEqualsMineralOwnership : Bool
    exclusiveTitleEqualsMineralOwnershipIsFalse :
      exclusiveTitleEqualsMineralOwnership ≡ false

open NativeTitleCoverageReceipt public

nativeTitleCoverage2025 : NativeTitleCoverageReceipt
nativeTitleCoverage2025 = native-title-coverage-receipt
  554
  154
  310
  "George Driver / AAP FactCheck 2025 reporting October 2025 NNTT maps and NNTT spokesperson; 55.4% determination coverage, 15.4% exclusive native title, about 31% non-exclusive native title."
  false refl
  false refl
  false refl
  false refl

nativeTitleDeterminationCoverageMapped : CalibrationState
nativeTitleDeterminationCoverageMapped = sourceMappedPositive

landCountryControlStatusV02 : CalibrationState
landCountryControlStatusV02 = sourceMappedPartial

landCountryControlNotClosedByDeterminationCoverage :
  Continuity.currentCoordinateState Continuity.landCountryControl ≡ Continuity.open
landCountryControlNotClosedByDeterminationCoverage = refl

------------------------------------------------------------------------
-- State's own Closing-the-Gap review identifies power-sharing defects.
------------------------------------------------------------------------

record GovernmentPowerSharingReviewReceipt : Set where
  constructor government-power-sharing-review-receipt
  field
    fundamentalChangeRequired : Bool
    fundamentalChangeRequiredIsTrue : fundamentalChangeRequired ≡ true
    sharePowerRecommended : Bool
    sharePowerRecommendedIsTrue : sharePowerRecommended ≡ true
    indigenousDataSovereigntyRecommended : Bool
    indigenousDataSovereigntyRecommendedIsTrue : indigenousDataSovereigntyRecommended ≡ true
    governmentSystemsRethinkRecommended : Bool
    governmentSystemsRethinkRecommendedIsTrue : governmentSystemsRethinkRecommended ≡ true
    strongerAccountabilityRecommended : Bool
    strongerAccountabilityRecommendedIsTrue : strongerAccountabilityRecommended ≡ true
    failureToRelinquishPowerReported : Bool
    failureToRelinquishPowerReportedIsTrue : failureToRelinquishPowerReported ≡ true
    recommendationsProvePowerAlreadyShared : Bool
    recommendationsProvePowerAlreadySharedIsFalse :
      recommendationsProvePowerAlreadyShared ≡ false
    sourceReference : String

open GovernmentPowerSharingReviewReceipt public

closingGapReview2024 : GovernmentPowerSharingReviewReceipt
closingGapReview2024 = government-power-sharing-review-receipt
  true refl true refl true refl true refl true refl true refl
  false refl
  "Productivity Commission, Review of the National Agreement on Closing the Gap, 2024."

communityDefinedOutcomeAuthorityStatusV02 : CalibrationState
communityDefinedOutcomeAuthorityStatusV02 = structuralConstraintMapped

------------------------------------------------------------------------
-- PBC legal authority carrier != practical authority-bearing capacity.
------------------------------------------------------------------------

record PBCResourceCapacityReceipt : Set where
  constructor pbc-resource-capacity-receipt
  field
    surveyLackResourcesPercent : Nat
    historicalSurveyLackFundingPercent : Nat
    estimatedCoreComplianceFundingCoveragePercent : Nat
    aiatsisSourceReference : String
    caeprSourceReference : String
    legalCarrierExists : Bool
    legalCarrierExistsIsTrue : legalCarrierExists ≡ true
    fundingEstimateIsUniversalEveryPBCRatio : Bool
    fundingEstimateIsUniversalEveryPBCRatioIsFalse :
      fundingEstimateIsUniversalEveryPBCRatio ≡ false
    legalCarrierExistenceProvesOperationalCapacity : Bool
    legalCarrierExistenceProvesOperationalCapacityIsFalse :
      legalCarrierExistenceProvesOperationalCapacity ≡ false

open PBCResourceCapacityReceipt public

pbcResourceCapacity : PBCResourceCapacityReceipt
pbcResourceCapacity = pbc-resource-capacity-receipt
  67
  73
  10
  "AIATSIS, Report on the 2019 Survey of Prescribed Bodies Corporate, published 2021."
  "Woods, Markham, Smith, Taylor, Burbidge & Dinku, Toward a Perpetual Funding Model for Native Title Prescribed Bodies Corporate, 2021, DOI 10.25911/6FPY-AV98."
  true refl
  false refl
  false refl

communityAuthorityBearingStatusV02 : CalibrationState
communityAuthorityBearingStatusV02 = structuralConstraintMapped

------------------------------------------------------------------------
-- Juukan Gorge: declared legislative repair and realised correction can diverge.
------------------------------------------------------------------------

data JuukanRepairState : Set where
  strongerLegislativeRepairInForce
  strongerLegislativeRepairRepealed
  : JuukanRepairState

data JuukanDeclarationSurface : Set where
  postJuukanProtectionCommitment : JuukanDeclarationSurface

data JuukanRealisedCorrection : Set where
  strongerCorrectionCapacityInForce
  revertedProtectionArchitectureWithContinuingDestructionReports
  : JuukanRealisedCorrection

juukanDeclaration : JuukanRepairState → JuukanDeclarationSurface
juukanDeclaration _ = postJuukanProtectionCommitment

juukanRealisedCorrection : JuukanRepairState → JuukanRealisedCorrection
juukanRealisedCorrection strongerLegislativeRepairInForce = strongerCorrectionCapacityInForce
juukanRealisedCorrection strongerLegislativeRepairRepealed =
  revertedProtectionArchitectureWithContinuingDestructionReports

juukanRealisedCorrectionDiffers :
  juukanRealisedCorrection strongerLegislativeRepairInForce
  ≡ juukanRealisedCorrection strongerLegislativeRepairRepealed → ⊥
juukanRealisedCorrectionDiffers ()

juukanDeclarationCannotRecoverRealisedCorrection :
  INF.FactorsThrough juukanDeclaration juukanRealisedCorrection → ⊥
juukanDeclarationCannotRecoverRealisedCorrection =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      strongerLegislativeRepairInForce
      strongerLegislativeRepairRepealed
      refl
      juukanRealisedCorrectionDiffers)

record JuukanDurabilityReceipt : Set where
  constructor juukan-durability-receipt
  field
    strongerLawPassed : Bool
    strongerLawPassedIsTrue : strongerLawPassed ≡ true
    strongerLawCommenced : Bool
    strongerLawCommencedIsTrue : strongerLawCommenced ≡ true
    repealedAfterAboutFiveWeeks : Bool
    repealedAfterAboutFiveWeeksIsTrue : repealedAfterAboutFiveWeeks ≡ true
    original1972RegimeRestoredWithAmendments : Bool
    original1972RegimeRestoredWithAmendmentsIsTrue :
      original1972RegimeRestoredWithAmendments ≡ true
    continuingDestructionReportedIn2025 : Bool
    continuingDestructionReportedIn2025IsTrue :
      continuingDestructionReportedIn2025 ≡ true
    recurringDestructionIsCourtFinding : Bool
    recurringDestructionIsCourtFindingIsFalse : recurringDestructionIsCourtFinding ≡ false
    sourceReference : String

open JuukanDurabilityReceipt public

juukanDurability2025 : JuukanDurabilityReceipt
juukanDurability2025 = juukan-durability-receipt
  true refl true refl true refl true refl true refl
  false refl
  "Mietta Adams & Alistair Bates, ABC Pilbara, 24 May 2025. The continuing-destruction proposition is attributed reporting/quoted field evidence, not a judicial finding."

recurrencePreventionStatusV02 : CalibrationState
recurrencePreventionStatusV02 = sourceMappedNegativePressure

independentCorrectionStatusV02 : CalibrationState
independentCorrectionStatusV02 = sourceMappedPartial

------------------------------------------------------------------------
-- Wangan/Jagalingou: native-title extinguishment and later HRA review route are
-- different legal mechanisms.  The 2026 appeal reopens trial; it does not close
-- final protection merits.
------------------------------------------------------------------------

record WanganJagalingouRouteReceipt : Set where
  constructor wj-route-receipt
  field
    nativeTitleExtinguishmentReported2019 : Bool
    nativeTitleExtinguishmentReported2019IsTrue :
      nativeTitleExtinguishmentReported2019 ≡ true
    laterHumanRightsEnvironmentalReviewRouteExists : Bool
    laterHumanRightsEnvironmentalReviewRouteExistsIsTrue :
      laterHumanRightsEnvironmentalReviewRouteExists ≡ true
    courtOfAppealRestoredFullCaseForTrial : Bool
    courtOfAppealRestoredFullCaseForTrialIsTrue :
      courtOfAppealRestoredFullCaseForTrial ≡ true
    finalProtectionMeritsDetermined : Bool
    finalProtectionMeritsDeterminedIsFalse :
      finalProtectionMeritsDetermined ≡ false
    mineOrderedStoppedByAppealResult : Bool
    mineOrderedStoppedByAppealResultIsFalse :
      mineOrderedStoppedByAppealResult ≡ false
    sourceReference : String

open WanganJagalingouRouteReceipt public

wanganJagalingouRoute : WanganJagalingouRouteReceipt
wanganJagalingouRoute = wj-route-receipt
  true refl
  true refl
  true refl
  false refl
  false refl
  "2019 extinguishment: ABC reporting on Queensland extinguishment over the Carmichael mine site. 2026 review route: ABC reporting of unanimous QCA decision restoring Nagana Yarrbayn Wangan and Jagalingou Cultural Custodians' case for Supreme Court trial; final merits remain open."

externalEvidenceCanChangeDecisionStatusV02 : CalibrationState
externalEvidenceCanChangeDecisionStatusV02 = sourceMappedPartial

------------------------------------------------------------------------
-- Timber Creek: compensation is a realised datum, not systemic reparation closure.
------------------------------------------------------------------------

record TimberCreekCompensationReceipt : Set where
  constructor timber-creek-compensation-receipt
  field
    economicLossDollars : Nat
    interestDollars : Nat
    culturalLossDollars : Nat
    totalCompensationDollars : Nat
    primaryAuthorityReference : String
    numericSummaryReference : String
    oneAwardProvesSystemicReparationAdequacy : Bool
    oneAwardProvesSystemicReparationAdequacyIsFalse :
      oneAwardProvesSystemicReparationAdequacy ≡ false

open TimberCreekCompensationReceipt public

timberCreekCompensation : TimberCreekCompensationReceipt
timberCreekCompensation = timber-creek-compensation-receipt
  320250
  910100
  1300000
  2530350
  "Northern Territory v Griffiths [2019] HCA 7, High Court of Australia."
  "AIATSIS case summary of the High Court orders."
  false refl

compensationReparationStatusV02 : CalibrationState
compensationReparationStatusV02 = sourceMappedPartial

------------------------------------------------------------------------
-- Closing the Gap outcome scorecard: descriptive outcome receipt only.
------------------------------------------------------------------------

record ClosingGapOutcomeReceipt : Set where
  constructor closing-gap-outcome-receipt
  field
    targetCount : Nat
    metCount : Nat
    onTrackCount : Nat
    improvingOffTrackCount : Nat
    worseningCount : Nat
    sourceReference : String
    statisticsIdentifySingleCause : Bool
    statisticsIdentifySingleCauseIsFalse : statisticsIdentifySingleCause ≡ false
    officialOutcomeReportEqualsAffectedCommunityDefinedJustice : Bool
    officialOutcomeReportEqualsAffectedCommunityDefinedJusticeIsFalse :
      officialOutcomeReportEqualsAffectedCommunityDefinedJustice ≡ false

open ClosingGapOutcomeReceipt public

closingGap2026 : ClosingGapOutcomeReceipt
closingGap2026 = closing-gap-outcome-receipt
  19 1 3 5 4
  "Productivity Commission, Closing the Gap Annual Data Compilation Report July 2026."
  false refl
  false refl

------------------------------------------------------------------------
-- Two-Eyed / POSIWID cross-pollination.
------------------------------------------------------------------------

sharedObservationDoesNotFuseKnowledgeHistory :
  TwoEyed.sharedObservationMeansSameEpistemicHistory
    TwoEyed.canonicalKimmererTwoEyedSeeingBoundary ≡ false
sharedObservationDoesNotFuseKnowledgeHistory = refl

extractedPropositionDoesNotRecoverCommunityAuthority :
  INF.FactorsThrough IK.extractedProposition IK.authority → ⊥
extractedPropositionDoesNotRecoverCommunityAuthority =
  IK.propositionCannotRecoverAuthority

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

realisedCorrectionIsPartOfSystemOperation :
  POSIWID.correctionResponseIsPartOfObservableOperation posiwidBoundary ≡ true
realisedCorrectionIsPartOfSystemOperation = refl

declaredPurposeDoesNotOverrideRepeatedRealisedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
declaredPurposeDoesNotOverrideRepeatedRealisedEffect = refl

operationalClassificationDoesNotRequirePrivateIntent :
  POSIWID.observedOperationProvesSubjectiveIntent posiwidBoundary ≡ false
operationalClassificationDoesNotRequirePrivateIntent = refl

------------------------------------------------------------------------
-- V02 state: old OPEN coordinates are not erased; later evidence refines them.
------------------------------------------------------------------------

record CountryRepairCalibrationV02 : Set where
  constructor country-repair-calibration-v02
  field
    nativeTitleDeterminationCoverage : CalibrationState
    landCountryControl : CalibrationState
    communityAuthorityBearing : CalibrationState
    communityDefinedOutcomeAuthority : CalibrationState
    independentCorrection : CalibrationState
    externalEvidenceChangesDecision : CalibrationState
    compensationReparation : CalibrationState
    recurrencePrevention : CalibrationState
    socioEconomicOutcome : CalibrationState
    sourceAtlasReference : String
    historicalOpenStateRewritten : Bool
    historicalOpenStateRewrittenIsFalse : historicalOpenStateRewritten ≡ false

open CountryRepairCalibrationV02 public

currentCalibrationV02 : CountryRepairCalibrationV02
currentCalibrationV02 = country-repair-calibration-v02
  sourceMappedPositive
  sourceMappedPartial
  structuralConstraintMapped
  structuralConstraintMapped
  sourceMappedPartial
  sourceMappedPartial
  sourceMappedPartial
  sourceMappedNegativePressure
  sourceMappedPartial
  "SensibLawCountryRealisedRepairSourceAtlasV02Exact.atlas"
  false refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data DeterminationCoverageEqualsSovereignCountryControl : Set where
data PBCLegalExistenceMeansAdequatelyResourcedAuthority : Set where
data JuukanReformDeclarationMeansDurableRecurrencePrevention : Set where
data WJAppealMeansFinalProtectionMeritsWon : Set where
data TimberCreekAwardMeansSystemicFullReparation : Set where
data ClosingGapStatisticsProveLandBackCausalMagnitude : Set where

determinationCoverageDoesNotEqualSovereignControl :
  DeterminationCoverageEqualsSovereignCountryControl → ⊥
determinationCoverageDoesNotEqualSovereignControl ()

pbcFormDoesNotProveOperationalCapacity :
  PBCLegalExistenceMeansAdequatelyResourcedAuthority → ⊥
pbcFormDoesNotProveOperationalCapacity ()

juukanDeclarationDoesNotProveDurableCorrection :
  JuukanReformDeclarationMeansDurableRecurrencePrevention → ⊥
juukanDeclarationDoesNotProveDurableCorrection ()

wjProceduralReopeningDoesNotEqualFinalMerits : WJAppealMeansFinalProtectionMeritsWon → ⊥
wjProceduralReopeningDoesNotEqualFinalMerits ()

timberCreekDoesNotCloseSystemicReparation : TimberCreekAwardMeansSystemicFullReparation → ⊥
timberCreekDoesNotCloseSystemicReparation ()

closingGapStatisticsDoNotProveLandBackMagnitude :
  ClosingGapStatisticsProveLandBackCausalMagnitude → ⊥
closingGapStatisticsDoNotProveLandBackMagnitude ()
