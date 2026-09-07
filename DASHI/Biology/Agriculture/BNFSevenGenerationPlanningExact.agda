module DASHI.Biology.Agriculture.BNFSevenGenerationPlanningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.RequirementProducerSchedulerExact as Scheduler
import DASHI.Core.IntergenerationalPlanningHorizonExact as Intergen
import DASHI.Core.HistoryConditionedChoiceExact as History
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.AdaptiveConsumerModelLoopExact as Adaptive
import DASHI.Biology.Agriculture.BNFQualifiedInterventionModelExact as BNF
import DASHI.Biology.Agriculture.BNFClimateCountryLESCrossPollinationExact as Cross
import DASHI.Cognition.PNF.SensibLawMaboTwoLegalOrderFibreExact as TwoOrder

------------------------------------------------------------------------
-- BNF SEVEN-GENERATION PLANNING APPLICATION
--
-- The seven-generation horizon in this file is a DASHI-selected planning
-- horizon motivated by the user's planning requirement.  No historical or
-- community-specific Indigenous doctrine is attributed here.  Any later claim
-- that a named community's law requires or defines a seven-generation rule must
-- be carried by that community-specific source/authority receipt.
--
-- The Mabo/Country cross-pollination is structural only: the existing repo
-- already keeps intergenerational continuity and Country/community authority
-- independently typed.  Horizon length never manufactures that authority.
------------------------------------------------------------------------

data SevenGenerationQuestion : Set where
  sevenGenerationLandscapeDecision
  sevenGenerationCountryAffectingDecision
  : SevenGenerationQuestion

data LongHorizonCoordinate : Set where
  presentBiologicalAdequacy
  presentFarmEconomics
  generation1SoilWater
  generation2SoilWater
  generation3Biodiversity
  generation4ClimateExposure
  generation5EconomicResilience
  generation6DistributionContinuity
  generation7FutureOptionSet
  longRunReversibility
  ecologicalFutureConeAdequacy
  intergenerationalUncertainty
  countryAuthorityContinuity
  communityConsentScopeThroughTime
  : LongHorizonCoordinate

data EvidenceProducer : Set where
  fieldExperimentProducer
  farmEconomicProducer
  lesSoilHydrologyProducer
  lesBiodiversityProducer
  climateScenarioProducer
  resilienceDistributionProducer
  futureConeProducer
  reversibilityProducer
  uncertaintyProducer
  communityAuthorityProducer
  consentScopeProducer
  : EvidenceProducer

requiredFor : SevenGenerationQuestion → LongHorizonCoordinate → Bool
requiredFor sevenGenerationLandscapeDecision presentBiologicalAdequacy = true
requiredFor sevenGenerationLandscapeDecision presentFarmEconomics = true
requiredFor sevenGenerationLandscapeDecision generation1SoilWater = true
requiredFor sevenGenerationLandscapeDecision generation2SoilWater = true
requiredFor sevenGenerationLandscapeDecision generation3Biodiversity = true
requiredFor sevenGenerationLandscapeDecision generation4ClimateExposure = true
requiredFor sevenGenerationLandscapeDecision generation5EconomicResilience = true
requiredFor sevenGenerationLandscapeDecision generation6DistributionContinuity = true
requiredFor sevenGenerationLandscapeDecision generation7FutureOptionSet = true
requiredFor sevenGenerationLandscapeDecision longRunReversibility = true
requiredFor sevenGenerationLandscapeDecision ecologicalFutureConeAdequacy = true
requiredFor sevenGenerationLandscapeDecision intergenerationalUncertainty = true
requiredFor sevenGenerationLandscapeDecision _ = false

requiredFor sevenGenerationCountryAffectingDecision _ = true

producerFor : LongHorizonCoordinate → EvidenceProducer
producerFor presentBiologicalAdequacy = fieldExperimentProducer
producerFor presentFarmEconomics = farmEconomicProducer
producerFor generation1SoilWater = lesSoilHydrologyProducer
producerFor generation2SoilWater = lesSoilHydrologyProducer
producerFor generation3Biodiversity = lesBiodiversityProducer
producerFor generation4ClimateExposure = climateScenarioProducer
producerFor generation5EconomicResilience = resilienceDistributionProducer
producerFor generation6DistributionContinuity = resilienceDistributionProducer
producerFor generation7FutureOptionSet = futureConeProducer
producerFor longRunReversibility = reversibilityProducer
producerFor ecologicalFutureConeAdequacy = futureConeProducer
producerFor intergenerationalUncertainty = uncertaintyProducer
producerFor countryAuthorityContinuity = communityAuthorityProducer
producerFor communityConsentScopeThroughTime = consentScopeProducer

------------------------------------------------------------------------
-- Current closure state is deliberately conservative.  Present biological
-- evidence exists in the wider BNF tranche, but the full seven-generation
-- same-object intervention fibre has not been validated.
------------------------------------------------------------------------

closed : LongHorizonCoordinate → Bool
closed presentBiologicalAdequacy = true
closed _ = false

sevenGenerationRequirementSystem : Scheduler.RequirementSystem
sevenGenerationRequirementSystem =
  Scheduler.requirement-system
    SevenGenerationQuestion
    LongHorizonCoordinate
    EvidenceProducer
    requiredFor
    closed
    producerFor
    "BNF long-horizon consumer requirements"
    "field evidence, LES process models, climate scenarios, future-cone/reversibility analysis, and independent Country/community authority producers"

------------------------------------------------------------------------
-- Exact missing-coordinate examples.
------------------------------------------------------------------------

futureOptionSetMissing :
  Scheduler.MissingFor
    sevenGenerationRequirementSystem
    sevenGenerationLandscapeDecision
    generation7FutureOptionSet
futureOptionSetMissing = refl , refl

futureOptionProducer : EvidenceProducer
futureOptionProducer =
  Scheduler.scheduledProducer
    (Scheduler.missing-coordinate-receipt
      generation7FutureOptionSet
      futureOptionSetMissing)

futureOptionProducerIsFutureConeProducer :
  futureOptionProducer ≡ futureConeProducer
futureOptionProducerIsFutureConeProducer = refl

countryAuthorityMissing :
  Scheduler.MissingFor
    sevenGenerationRequirementSystem
    sevenGenerationCountryAffectingDecision
    countryAuthorityContinuity
countryAuthorityMissing = refl , refl

countryAuthorityProducer : EvidenceProducer
countryAuthorityProducer =
  Scheduler.scheduledProducer
    (Scheduler.missing-coordinate-receipt
      countryAuthorityContinuity
      countryAuthorityMissing)

countryAuthorityProducerIsIndependent :
  countryAuthorityProducer ≡ communityAuthorityProducer
countryAuthorityProducerIsIndependent = refl

------------------------------------------------------------------------
-- Present-value collapse counterexample.
------------------------------------------------------------------------

data LongHorizonWorld : Set where
  samePresentProfitNarrowFuture
  samePresentProfitBroadFuture
  : LongHorizonWorld

data PresentEconomicObservation : Set where
  samePresentPositiveEconomics : PresentEconomicObservation

data GenerationSevenFutureOption : Set where
  constrainedFutureOptions
  broadFutureOptions
  : GenerationSevenFutureOption

presentEconomicObserver : LongHorizonWorld → PresentEconomicObservation
presentEconomicObserver samePresentProfitNarrowFuture = samePresentPositiveEconomics
presentEconomicObserver samePresentProfitBroadFuture = samePresentPositiveEconomics

generationSevenFutureOptions : LongHorizonWorld → GenerationSevenFutureOption
generationSevenFutureOptions samePresentProfitNarrowFuture = constrainedFutureOptions
generationSevenFutureOptions samePresentProfitBroadFuture = broadFutureOptions

futureOptionsDiffer :
  generationSevenFutureOptions samePresentProfitNarrowFuture ≡
  generationSevenFutureOptions samePresentProfitBroadFuture → ⊥
futureOptionsDiffer ()

presentEconomicsCannotRecoverGenerationSevenOptionsWitness :
  INF.NonFactorabilityWitness presentEconomicObserver generationSevenFutureOptions
presentEconomicsCannotRecoverGenerationSevenOptionsWitness =
  INF.nonFactorabilityWitness
    samePresentProfitNarrowFuture
    samePresentProfitBroadFuture
    refl
    futureOptionsDiffer

presentEconomicsCannotDetermineGenerationSevenOptions :
  INF.FactorsThrough presentEconomicObserver generationSevenFutureOptions → ⊥
presentEconomicsCannotDetermineGenerationSevenOptions =
  INF.witnessRulesOutEveryFlatFactorisation
    presentEconomicsCannotRecoverGenerationSevenOptionsWitness

------------------------------------------------------------------------
-- Intermediate-generation non-collapse.
------------------------------------------------------------------------

data TerminalGenerationBenefitImpliesIntermediateSafetyPermission : Set where

data CurrentProfitImpliesLongRunReversibilityPermission : Set where

data LongHorizonSimulationImpliesCommunityConsentPermission : Set where

data SevenGenerationAnalysisImpliesCountryLawPermission : Set where

data OneDiscountRateExhaustsIntergenerationalValuePermission : Set where

terminalBenefitDoesNotAutoPromoteToIntermediateSafety :
  TerminalGenerationBenefitImpliesIntermediateSafetyPermission → ⊥
terminalBenefitDoesNotAutoPromoteToIntermediateSafety ()

currentProfitDoesNotAutoPromoteToLongRunReversibility :
  CurrentProfitImpliesLongRunReversibilityPermission → ⊥
currentProfitDoesNotAutoPromoteToLongRunReversibility ()

longHorizonSimulationDoesNotAutoPromoteToCommunityConsent :
  LongHorizonSimulationImpliesCommunityConsentPermission → ⊥
longHorizonSimulationDoesNotAutoPromoteToCommunityConsent ()

sevenGenerationAnalysisDoesNotBecomeCountryLaw :
  SevenGenerationAnalysisImpliesCountryLawPermission → ⊥
sevenGenerationAnalysisDoesNotBecomeCountryLaw ()

oneDiscountRateDoesNotExhaustIntergenerationalValue :
  OneDiscountRateExhaustsIntergenerationalValuePermission → ⊥
oneDiscountRateDoesNotExhaustIntergenerationalValue ()

------------------------------------------------------------------------
-- Existing boundaries retained.
------------------------------------------------------------------------

intergenerationalBoundary : Intergen.IntergenerationalPlanningBoundary
intergenerationalBoundary = Intergen.canonicalIntergenerationalPlanningBoundary

historyBoundary : History.HistoryConditionedChoiceBoundary
historyBoundary = History.canonicalHistoryConditionedChoiceBoundary

adaptiveBoundary : Adaptive.AdaptiveConsumerLoopBoundary
adaptiveBoundary = Adaptive.canonicalAdaptiveConsumerLoopBoundary

countryOrderContinuityRemainsIndependent :
  TwoOrder.externalRecognitionCreatesOrder TwoOrder.indigenousOrderFibre ≡ false
countryOrderContinuityRemainsIndependent = refl

countryTechnicalBundleStillDoesNotCreateQualifiedUse =
  Cross.technicalBundleDoesNotAutoPromoteToQualifiedUse

researchReplayStillDoesNotRequireAuthority :
  BNF.requiredFor BNF.replayNationalAvoidedUreaExpenditure BNF.authorityAdequacy ≡ false
researchReplayStillDoesNotRequireAuthority = refl

record SevenGenerationBNFBoundary : Set where
  constructor seven-generation-bnf-boundary
  field
    presentProfitDeterminesGenerationSevenOptions : Bool
    presentProfitDeterminesGenerationSevenOptionsIsFalse :
      presentProfitDeterminesGenerationSevenOptions ≡ false
    everyIntermediateGenerationMustBeCollapsedIntoTerminalValue : Bool
    everyIntermediateGenerationMustBeCollapsedIntoTerminalValueIsFalse :
      everyIntermediateGenerationMustBeCollapsedIntoTerminalValue ≡ false
    CountryAuthorityIsIndependentLongHorizonCoordinate : Bool
    CountryAuthorityIsIndependentLongHorizonCoordinateIsTrue :
      CountryAuthorityIsIndependentLongHorizonCoordinate ≡ true
    longHorizonProducerSchedulingIsConsumerRelative : Bool
    longHorizonProducerSchedulingIsConsumerRelativeIsTrue :
      longHorizonProducerSchedulingIsConsumerRelative ≡ true

canonicalSevenGenerationBNFBoundary : SevenGenerationBNFBoundary
canonicalSevenGenerationBNFBoundary =
  seven-generation-bnf-boundary false refl false refl true refl true refl
