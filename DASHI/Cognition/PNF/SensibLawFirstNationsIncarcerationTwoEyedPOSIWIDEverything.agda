module DASHI.Cognition.PNF.SensibLawFirstNationsIncarcerationTwoEyedPOSIWIDEverything where

------------------------------------------------------------------------
-- FIRST NATIONS INCARCERATION / TWO-EYED / POSIWID CAPSTONE
--
-- Official statistical operation is one evidence strand. Affected-community
-- outcome and authority remain independent strands. Worsening operation can
-- reopen a declared success/strategy assessment without proving private intent,
-- and community evidence does not transfer community authority to the State.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Cognition.PNF.SensibLawFirstNationsIncarcerationSourceAtlasExact as Sources
import DASHI.Cognition.PNF.SensibLawFirstNationsIncarcerationOperationalDiscrepancyExact as Incarceration
import DASHI.Cognition.PNF.SensibLawCountryCommunityAuthorityFirstCorrectionExact as Correction

------------------------------------------------------------------------
-- Source atlas and realised-operation discrepancy.
------------------------------------------------------------------------

sourceCountIsSix :
  DASHI.Core.AttributedSourceCore.sourceCount Sources.allSources ≡ 6
sourceCountIsSix = refl

declaredTargetDoesNotDetermineRealisedTrajectory :
  INF.FactorsThrough Incarceration.declaredJusticePurpose Incarceration.realisedAdultTrajectory → ⊥
declaredTargetDoesNotDetermineRealisedTrajectory =
  Incarceration.declaredTargetCannotRecoverRealisedTrajectory

latestAdultRateIsSourceReportedNotCausal :
  Incarceration.causalMechanismEstablished Incarceration.march2026AdultCustody ≡ false
latestAdultRateIsSourceReportedNotCausal = refl

closingGapAssessmentDoesNotProveIntent :
  Incarceration.subjectiveIntentEstablished Incarceration.closingGapTarget10 ≡ false
closingGapAssessmentDoesNotProveIntent = refl

------------------------------------------------------------------------
-- POSIWID: realised operation can reopen the institutional success assessment.
------------------------------------------------------------------------

observedOperationMayClassifyOperation :
  POSIWID.observedOperationMayClassifyWhatSystemDoes
    POSIWID.canonicalOperationalDescriptionBoundary ≡ true
observedOperationMayClassifyOperation = refl

operationDoesNotProveSubjectiveIntent :
  POSIWID.observedOperationProvesSubjectiveIntent
    POSIWID.canonicalOperationalDescriptionBoundary ≡ false
operationDoesNotProveSubjectiveIntent = refl

declaredPurposeCannotOverrideRepeatedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect
    POSIWID.canonicalOperationalDescriptionBoundary ≡ false
declaredPurposeCannotOverrideRepeatedEffect = refl

repeatedOperationMayReopenDeclaredSuccess :
  DASHI.Core.PluralOperationalRealisationDiscrepancyExact.repeatedOperationMayReopenDeclaredSuccess
    Correction.operationalDiscrepancyBoundary ≡ true
repeatedOperationMayReopenDeclaredSuccess = refl

------------------------------------------------------------------------
-- Two-Eyed/community-authority-first correction remains the next governance
-- surface: more State statistics do not close the community-defined outcome.
------------------------------------------------------------------------

currentCorrectionBeginsWithCommunityDefinedOutcome :
  Correction.firstStage Correction.canonicalCommunityAuthorityFirstPlan
  ≡ Correction.obtainCommunityDefinedOutcomeStage
currentCorrectionBeginsWithCommunityDefinedOutcome = refl

stateSelfReportIsNotSufficient :
  Correction.institutionalSelfReportSufficient Correction.canonicalCommunityAuthorityFirstPlan
  ≡ false
stateSelfReportIsNotSufficient = refl

communityAuthorityIsRequired :
  Correction.affectedCommunityAuthorityRequired Correction.canonicalCommunityAuthorityFirstPlan
  ≡ true
communityAuthorityIsRequired = refl

correctionMustChangeRealisedOperation :
  Correction.correctionMustChangeRealisedOperation Correction.canonicalCommunityAuthorityFirstPlan
  ≡ true
correctionMustChangeRealisedOperation = refl

preventionMustBeObserved :
  Correction.preventionMustBeObserved Correction.canonicalCommunityAuthorityFirstPlan
  ≡ true
preventionMustBeObserved = refl

statisticalSurfaceCannotRecoverCommunityMeaning :
  INF.FactorsThrough Incarceration.statisticalSurface Incarceration.communityMeaning → ⊥
statisticalSurfaceCannotRecoverCommunityMeaning =
  Incarceration.statisticalSurfaceCannotRecoverCommunityMeaning

------------------------------------------------------------------------
-- Adult/youth/sex-specific axes remain distinct.
------------------------------------------------------------------------

femaleDisparityIsSourceReportedWithoutCauseClosure :
  Incarceration.causalMechanismEstablished Incarceration.firstNationsFemaleDisparity2025 ≡ false
femaleDisparityIsSourceReportedWithoutCauseClosure = refl

youthObservationDoesNotClaimCommunityMeaning :
  Incarceration.communityDefinedMeaningEstablished Incarceration.youthDetention2024_25 ≡ false
youthObservationDoesNotClaimCommunityMeaning = refl

------------------------------------------------------------------------
-- Operational justice frontier.
------------------------------------------------------------------------

data IncarcerationOperationalResidual : Set where
  affectedCommunityOutcomeResidual
  communityAuthorityResidual
  causalMechanismResidual
  correctionResponseResidual
  materialEffectResidual
  recurrencePreventionResidual
  : IncarcerationOperationalResidual

record IncarcerationOperationalFrontier : Set where
  constructor incarceration-operational-frontier
  field
    officialRateTrajectoryMapped : Bool
    officialRateTrajectoryMappedIsTrue : officialRateTrajectoryMapped ≡ true
    officialTargetWorseningMapped : Bool
    officialTargetWorseningMappedIsTrue : officialTargetWorseningMapped ≡ true
    affectedCommunityOutcomeClosed : Bool
    affectedCommunityOutcomeClosedIsFalse : affectedCommunityOutcomeClosed ≡ false
    communityAuthorityClosed : Bool
    communityAuthorityClosedIsFalse : communityAuthorityClosed ≡ false
    causalMechanismClosed : Bool
    causalMechanismClosedIsFalse : causalMechanismClosed ≡ false
    correctionResponseClosed : Bool
    correctionResponseClosedIsFalse : correctionResponseClosed ≡ false
    recurrencePreventionClosed : Bool
    recurrencePreventionClosedIsFalse : recurrencePreventionClosed ≡ false
    firstLiveResidual : IncarcerationOperationalResidual

open IncarcerationOperationalFrontier public

currentIncarcerationOperationalFrontier : IncarcerationOperationalFrontier
currentIncarcerationOperationalFrontier = incarceration-operational-frontier
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
  false refl
  affectedCommunityOutcomeResidual

firstLiveResidualIsCommunityOutcome :
  firstLiveResidual currentIncarcerationOperationalFrontier
  ≡ affectedCommunityOutcomeResidual
firstLiveResidualIsCommunityOutcome = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data WorseningTargetEqualsCommunityDefinedFailureMeaning : Set where
data MoreGovernmentStatisticsCloseCommunityOutcome : Set where
data DisproportionateOperationProvesPrivateRacistIntent : Set where
data YouthOverrepresentationProvesAdultMechanism : Set where
data ImprisonmentHealthBurdenProvesSingleCause : Set where

targetWorseningDoesNotDefineCommunityMeaning :
  WorseningTargetEqualsCommunityDefinedFailureMeaning → ⊥
targetWorseningDoesNotDefineCommunityMeaning ()

moreGovernmentStatisticsDoNotCloseCommunityOutcome :
  MoreGovernmentStatisticsCloseCommunityOutcome → ⊥
moreGovernmentStatisticsDoNotCloseCommunityOutcome ()

disproportionateOperationDoesNotByItselfProvePrivateIntent :
  DisproportionateOperationProvesPrivateRacistIntent → ⊥
disproportionateOperationDoesNotByItselfProvePrivateIntent ()

youthAndAdultMechanismsAreNotSilentlyIdentified :
  YouthOverrepresentationProvesAdultMechanism → ⊥
youthAndAdultMechanismsAreNotSilentlyIdentified ()

healthBurdenDoesNotCreateSingleCause : ImprisonmentHealthBurdenProvesSingleCause → ⊥
healthBurdenDoesNotCreateSingleCause ()
