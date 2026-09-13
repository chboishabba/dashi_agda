module DASHI.Cognition.PNF.SensibLawFirstNationsIncarcerationOperationalDiscrepancyExact where

------------------------------------------------------------------------
-- FIRST NATIONS INCARCERATION / OPERATIONAL DISCREPANCY
--
-- Source-bounded operational analysis only.
--
-- Official statistical observations and Closing the Gap target assessments are
-- source propositions.  The declared-vs-realised discrepancy and finite
-- non-factorability fixtures are DASHI/SensibLaw constructions.  They do not
-- prove subjective institutional intent, an Indigenous criminality essence, a
-- unique causal mechanism, or community-defined meaning.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID
import DASHI.Culture.IndigenousKnowledgeStoryTwoEyedSeeingBidiExact as TwoEyed
import DASHI.Cognition.PNF.SensibLawFirstNationsIncarcerationSourceAtlasExact as Sources

------------------------------------------------------------------------
-- Source-reported observation roles.
------------------------------------------------------------------------

data ObservationRole : Set where
  officialAdministrativeStatistic
  officialTargetAssessment
  officialHealthSynthesis
  officialYouthJusticeStatistic
  : ObservationRole

record SourceReportedObservation : Set where
  constructor source-reported-observation
  field
    sourceReference : String
    observationRole : ObservationRole
    period : String
    population : String
    measure : String
    reportedValue : String
    sourceReportedMeaning : String
    causalMechanismEstablished : Bool
    causalMechanismEstablishedIsFalse : causalMechanismEstablished ≡ false
    subjectiveIntentEstablished : Bool
    subjectiveIntentEstablishedIsFalse : subjectiveIntentEstablished ≡ false
    communityDefinedMeaningEstablished : Bool
    communityDefinedMeaningEstablishedIsFalse : communityDefinedMeaningEstablished ≡ false

open SourceReportedObservation public

march2026AdultCustody : SourceReportedObservation
march2026AdultCustody = source-reported-observation
  "ABS, Corrective Services Australia, March Quarter 2026"
  officialAdministrativeStatistic
  "March quarter 2026"
  "Aboriginal and Torres Strait Islander adults"
  "average daily persons in custody / share of custody / imprisonment rate"
  "18,272 persons; 37% of custody; 2,701 per 100,000 Aboriginal and Torres Strait Islander adults"
  "official quarterly descriptive custody statistics"
  false refl false refl false refl

adultTrend2016_2025 : SourceReportedObservation
adultTrend2016_2025 = source-reported-observation
  "AIHW, Health of people in prison, updated 2026; source series ABS"
  officialHealthSynthesis
  "2016-2025"
  "First Nations and non-Indigenous adults"
  "age-standardised imprisonment rate"
  "First Nations: 1,730.2 -> 2,500.2 per 100,000 (+45%); non-Indigenous: 163.0 -> 149.1 (-8.5%); rate ratio 10.6 -> 16.8"
  "official synthesis of divergent imprisonment-rate trajectories"
  false refl false refl false refl

closingGapTarget10 : SourceReportedObservation
closingGapTarget10 = source-reported-observation
  "Productivity Commission, Closing the Gap Target 10 dashboard, update 18 March 2026"
  officialTargetAssessment
  "2019 baseline to 2025 latest annual data"
  "Aboriginal and Torres Strait Islander adults"
  "Target 10: reduce adult incarceration rate by at least 15% by 2031"
  "2019 1,925.4; 2024 2,318.4; 2025 2,500.2 per 100,000; national target assessed worsening with high confidence"
  "official target declaration plus official progress assessment"
  false refl false refl false refl

youthDetention2024_25 : SourceReportedObservation
youthDetention2024_25 = source-reported-observation
  "AIHW, Youth justice in Australia 2024-25"
  officialYouthJusticeStatistic
  "2024-25"
  "young people aged 10-17"
  "share and rate ratio in detention on an average day"
  "First Nations young people were 62% of 10-17-year-olds in detention; 25.7 per 10,000 versus 1.1 for non-Indigenous young people; rate ratio about 23.4"
  "official youth-justice descriptive statistics; adult and youth populations are not pooled"
  false refl false refl false refl

firstNationsFemaleDisparity2025 : SourceReportedObservation
firstNationsFemaleDisparity2025 = source-reported-observation
  "AIHW, The health of people in Australia's prisons 2025; source series ABS"
  officialHealthSynthesis
  "2025"
  "First Nations adult females"
  "imprisonment rate and First Nations/non-Indigenous rate ratio"
  "520 per 100,000; about 26 times the non-Indigenous female rate"
  "sex-specific official disparity statistic"
  false refl false refl false refl

------------------------------------------------------------------------
-- Declared Closing the Gap purpose versus realised measured trajectory.
------------------------------------------------------------------------

data IncarcerationSystemState : Set where
  baseline2019State latest2025State : IncarcerationSystemState

data DeclaredJusticePurpose : Set where
  reduceAdultIncarcerationByAtLeastFifteenPercent : DeclaredJusticePurpose

data RealisedAdultTrajectory : Set where
  baselineRateState worseningHigherRateState : RealisedAdultTrajectory

data CorrectionState : Set where
  targetDeclared correctionStillRequired : CorrectionState

data RealisedEffect : Set where
  baselineEffect worseningEffect : RealisedEffect

declaredJusticePurpose : IncarcerationSystemState → DeclaredJusticePurpose
declaredJusticePurpose _ = reduceAdultIncarcerationByAtLeastFifteenPercent

realisedAdultTrajectory : IncarcerationSystemState → RealisedAdultTrajectory
realisedAdultTrajectory baseline2019State = baselineRateState
realisedAdultTrajectory latest2025State = worseningHigherRateState

realisedEffect : IncarcerationSystemState → RealisedEffect
realisedEffect baseline2019State = baselineEffect
realisedEffect latest2025State = worseningEffect

correctionState : IncarcerationSystemState → CorrectionState
correctionState baseline2019State = targetDeclared
correctionState latest2025State = correctionStillRequired

closingGapOperationalSystem :
  POSIWID.OperationalSystem
    IncarcerationSystemState DeclaredJusticePurpose RealisedAdultTrajectory RealisedEffect CorrectionState
closingGapOperationalSystem = POSIWID.operational-system
  declaredJusticePurpose realisedAdultTrajectory realisedEffect correctionState

declaredPurposeSameAcrossStates :
  declaredJusticePurpose baseline2019State ≡ declaredJusticePurpose latest2025State
declaredPurposeSameAcrossStates = refl

realisedTrajectoryDiffers :
  realisedAdultTrajectory baseline2019State ≡ realisedAdultTrajectory latest2025State → ⊥
realisedTrajectoryDiffers ()

declaredTargetCannotRecoverRealisedTrajectoryWitness :
  INF.NonFactorabilityWitness declaredJusticePurpose realisedAdultTrajectory
declaredTargetCannotRecoverRealisedTrajectoryWitness =
  INF.nonFactorabilityWitness
    baseline2019State latest2025State refl realisedTrajectoryDiffers

declaredTargetCannotRecoverRealisedTrajectory :
  INF.FactorsThrough declaredJusticePurpose realisedAdultTrajectory → ⊥
declaredTargetCannotRecoverRealisedTrajectory =
  INF.witnessRulesOutEveryFlatFactorisation declaredTargetCannotRecoverRealisedTrajectoryWitness

------------------------------------------------------------------------
-- Two-Eyed / community-authority firewall.
------------------------------------------------------------------------

data StatisticalSurface : Set where sameOfficialRateSurface : StatisticalSurface
data CommunityMeaning : Set where stateMetricMeaning communitySituatedMeaning : CommunityMeaning

data MeaningCarrier : Set where stateDefinedCarrier communityDefinedCarrier : MeaningCarrier

statisticalSurface : MeaningCarrier → StatisticalSurface
statisticalSurface _ = sameOfficialRateSurface

communityMeaning : MeaningCarrier → CommunityMeaning
communityMeaning stateDefinedCarrier = stateMetricMeaning
communityMeaning communityDefinedCarrier = communitySituatedMeaning

statisticalSurfaceCannotRecoverCommunityMeaning :
  INF.FactorsThrough statisticalSurface communityMeaning → ⊥
statisticalSurfaceCannotRecoverCommunityMeaning =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness stateDefinedCarrier communityDefinedCarrier refl (λ ()))

sharedObservationDoesNotFuseKnowledgeAuthority :
  INF.FactorsThrough TwoEyed.extractedProposition TwoEyed.authority → ⊥
sharedObservationDoesNotFuseKnowledgeAuthority = TwoEyed.propositionCannotRecoverAuthority

------------------------------------------------------------------------
-- Effects/health evidence is kept distinct from causal totalisation.
------------------------------------------------------------------------

data IncarcerationEffectsBoundary : Set where
  incarceration-effects-boundary : IncarcerationEffectsBoundary

record EffectsSourceBoundary : Set where
  constructor effects-source-boundary
  field
    prisonPopulationComplexHealthBurdenReported : Bool
    prisonPopulationComplexHealthBurdenReportedIsTrue :
      prisonPopulationComplexHealthBurdenReported ≡ true
    detentionHistoryCanCreateEmploymentBarrierReported : Bool
    detentionHistoryCanCreateEmploymentBarrierReportedIsTrue :
      detentionHistoryCanCreateEmploymentBarrierReported ≡ true
    imprisonmentExacerbatesInequalityReportedByAIHW : Bool
    imprisonmentExacerbatesInequalityReportedByAIHWIsTrue :
      imprisonmentExacerbatesInequalityReportedByAIHW ≡ true
    everyObservedHealthGapCausedByImprisonment : Bool
    everyObservedHealthGapCausedByImprisonmentIsFalse :
      everyObservedHealthGapCausedByImprisonment ≡ false
    singleCausalMechanismIdentified : Bool
    singleCausalMechanismIdentifiedIsFalse : singleCausalMechanismIdentified ≡ false

open EffectsSourceBoundary public

canonicalEffectsSourceBoundary : EffectsSourceBoundary
canonicalEffectsSourceBoundary = effects-source-boundary
  true refl true refl true refl false refl false refl

------------------------------------------------------------------------
-- Intersectional result: the female disparity remains separately visible.
------------------------------------------------------------------------

record SexSpecificDisparityBoundary : Set where
  constructor sex-specific-disparity-boundary
  field
    maleAndFemaleFirstNationsRateRatiosIdentical : Bool
    maleAndFemaleFirstNationsRateRatiosIdenticalIsFalse :
      maleAndFemaleFirstNationsRateRatiosIdentical ≡ false
    femaleFirstNationsRateRatioReportedAboutTwentySix : Bool
    femaleFirstNationsRateRatioReportedAboutTwentySixIsTrue :
      femaleFirstNationsRateRatioReportedAboutTwentySix ≡ true
    maleFirstNationsRateRatioReportedAboutSixteen : Bool
    maleFirstNationsRateRatioReportedAboutSixteenIsTrue :
      maleFirstNationsRateRatioReportedAboutSixteen ≡ true
    sexSpecificDifferenceAutomaticallyExplainsMechanism : Bool
    sexSpecificDifferenceAutomaticallyExplainsMechanismIsFalse :
      sexSpecificDifferenceAutomaticallyExplainsMechanism ≡ false

open SexSpecificDisparityBoundary public

canonicalSexSpecificDisparityBoundary : SexSpecificDisparityBoundary
canonicalSexSpecificDisparityBoundary =
  sex-specific-disparity-boundary false refl true refl true refl false refl

------------------------------------------------------------------------
-- POSIWID / operational classification boundary.
------------------------------------------------------------------------

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

operationMayClassifyWhatSystemDoes :
  POSIWID.observedOperationMayClassifyWhatSystemDoes posiwidBoundary ≡ true
operationMayClassifyWhatSystemDoes = refl

operationDoesNotProveSubjectiveIntent :
  POSIWID.observedOperationProvesSubjectiveIntent posiwidBoundary ≡ false
operationDoesNotProveSubjectiveIntent = refl

declaredPurposeDoesNotOverrideRepeatedEffect :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
declaredPurposeDoesNotOverrideRepeatedEffect = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data WorseningTrajectoryMeansDeclaredTargetAbsent : Set where
data WorseningTrajectoryProvesHostileIntent : Set where
data OverrepresentationProvesIndigenousCriminalityEssence : Set where
data OfficialStatisticDefinesAffectedCommunityMeaning : Set where
data AdultRateMayBePooledWithYouthRate : Set where
data SexSpecificDisparityIdentifiesCompleteCause : Set where

data ClosingGapTargetTransfersCommunityAuthorityToState : Set where

worseningDoesNotEraseDeclaredTarget : WorseningTrajectoryMeansDeclaredTargetAbsent → ⊥
worseningDoesNotEraseDeclaredTarget ()

worseningDoesNotProveHostileIntent : WorseningTrajectoryProvesHostileIntent → ⊥
worseningDoesNotProveHostileIntent ()

overrepresentationDoesNotCreateCriminalityEssence :
  OverrepresentationProvesIndigenousCriminalityEssence → ⊥
overrepresentationDoesNotCreateCriminalityEssence ()

officialStatisticDoesNotDefineCommunityMeaning :
  OfficialStatisticDefinesAffectedCommunityMeaning → ⊥
officialStatisticDoesNotDefineCommunityMeaning ()

adultAndYouthRatesRemainSeparate : AdultRateMayBePooledWithYouthRate → ⊥
adultAndYouthRatesRemainSeparate ()

sexSpecificDifferenceDoesNotIdentifyCompleteCause :
  SexSpecificDisparityIdentifiesCompleteCause → ⊥
sexSpecificDifferenceDoesNotIdentifyCompleteCause ()

closingGapTargetDoesNotTransferCommunityAuthority :
  ClosingGapTargetTransfersCommunityAuthorityToState → ⊥
closingGapTargetDoesNotTransferCommunityAuthority ()
