module DASHI.Education.DigitalESDMaterialImpactAllocationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as Factors
import DASHI.Core.DialecticalMaterialRevisionExact as DialecticMaterial
import DASHI.Economics.AITrainingServingEconomicTimeSeriesCrossPollinationExact as TrainingServing
import DASHI.Education.DigitalESDMaterialEnvironmentalSubstrateExact as Material
import DASHI.Education.DigitalESDExternalityIncidenceAuditExact as Incidence

------------------------------------------------------------------------
-- CONSUMER-RELATIVE MATERIAL IMPACT ALLOCATION
--
-- The substrate audit already retains lifecycle stages and physical burdens.
-- This thin owner adds only the allocation question forced by shared digital
-- infrastructure: how a fixed/shared embodied, training or infrastructure
-- burden is allocated to a request, learner, task, course or other functional
-- unit. Allocation is source/model-relative accounting, not a new physical
-- measurement and not a moral distribution theorem.
------------------------------------------------------------------------

ecologitsSource : Attr.AttributedSource
ecologitsSource = Attr.mkDOISource
  "Samuel Rincé; Adrien Banse"
  "EcoLogits: Evaluating the Environmental Impacts of Generative AI"
  "Journal of Open Source Software 10(111):7471"
  "2025"
  "10.21105/joss.07471"
  "https://doi.org/10.21105/joss.07471"
  Attr.academicArticleSource
  "Primary open-source LCA methodology/tool source for generative-AI inference impact estimation. Useful for system-boundary, operational-versus-embodied and allocation-method calibration only; it does not measure a named education deployment."
  Attr.publicAttribution

wooProgrammingLCASource : Attr.AttributedSource
wooProgrammingLCASource = Attr.mkDOISource
  "Nolan H. Woo"
  "A comparative study of AI and human programming on environmental sustainability"
  "Scientific Reports 15:39182"
  "2025"
  "10.1038/s41598-025-24658-5"
  "https://doi.org/10.1038/s41598-025-24658-5"
  Attr.academicArticleSource
  "Primary comparative programming study using EcoLogits-style LCA accounting. The AI inference functional unit is one request; embodied hardware impact is amortised over hardware lifetime and allocated to a request using time-weighted resource consumption. Training and end-of-life are outside that request-level model boundary. This calibrates allocation semantics only."
  Attr.publicAttribution

allocationCalibrationSources : List Attr.AttributedSource
allocationCalibrationSources = ecologitsSource ∷ wooProgrammingLCASource ∷ []

data AllocationAuditQuestion : Set where
  whatFunctionalUnit : AllocationAuditQuestion
  whatSharedBurden : AllocationAuditQuestion
  whatAllocationBasis : AllocationAuditQuestion
  whatLifetimeOrUsageDenominator : AllocationAuditQuestion
  whatTimeUtilisationShare : AllocationAuditQuestion
  howTrainingAndServingSeparate : AllocationAuditQuestion
  whoseTaskOrConsumerDefinition : AllocationAuditQuestion
  whichBurdenFallsOutsideAllocatedUnit : AllocationAuditQuestion

allocationAuditQuestions : List AllocationAuditQuestion
allocationAuditQuestions =
  whatFunctionalUnit
  ∷ whatSharedBurden
  ∷ whatAllocationBasis
  ∷ whatLifetimeOrUsageDenominator
  ∷ whatTimeUtilisationShare
  ∷ howTrainingAndServingSeparate
  ∷ whoseTaskOrConsumerDefinition
  ∷ whichBurdenFallsOutsideAllocatedUnit
  ∷ []

allocationAuditQuestionCount : Nat
allocationAuditQuestionCount = 8

questionReading : AllocationAuditQuestion → String
questionReading whatFunctionalUnit = "what functional unit is receiving the allocated impact: request, token, successful task, learner-hour, course, device-year or another unit?"
questionReading whatSharedBurden = "which embodied, training, facility or other shared/fixed burden is being allocated?"
questionReading whatAllocationBasis = "is allocation based on elapsed resource time, utilisation, request count, token count, throughput, successful tasks or another explicit rule?"
questionReading whatLifetimeOrUsageDenominator = "what service life, total use, total task count or other denominator is assumed, observed or unresolved?"
questionReading whatTimeUtilisationShare = "what fraction of accelerator/server/device time or capacity is actually attributed to the consumer unit?"
questionReading howTrainingAndServingSeparate = "are one-off training burdens, persistent serving burdens and embodied hardware burdens kept separate before any amortisation?"
questionReading whoseTaskOrConsumerDefinition = "whose definition of a successful task, learner, request or beneficiary determines the denominator?"
questionReading whichBurdenFallsOutsideAllocatedUnit = "which lifecycle stages, affected communities or excluded externalities remain outside the chosen functional unit/system boundary?"

------------------------------------------------------------------------
-- Canonical repo donors.
------------------------------------------------------------------------

materialBoundary : Material.MaterialEnvironmentalBoundary
materialBoundary = Material.canonicalMaterialEnvironmentalBoundary

externalityBoundary : Incidence.ExternalityIncidenceBoundary
externalityBoundary = Incidence.canonicalExternalityIncidenceBoundary

dialecticalMaterialBoundary : DialecticMaterial.DialecticalMaterialRevisionBoundary
dialecticalMaterialBoundary = DialecticMaterial.canonicalDialecticalMaterialRevisionBoundary

trainingServingAmortisationType : Set₁
trainingServingAmortisationType = TrainingServing.TrainingAmortisationBoundary

trainingServingReading : String
trainingServingReading =
  "The existing AI economics owner already distinguishes training compute per model release, amortised training compute per successful task, serving compute per successful task, task throughput and utilisation. This digital-ESD owner reuses that separation for environmental allocation and does not convert economic cost coordinates into environmental quantities."

------------------------------------------------------------------------
-- Constructive collisions.
--
-- Same total shared impact can yield different per-consumer allocations when
-- usage/denominator differs. Conversely, the same consumer count can yield
-- different allocations when time/resource share differs. Therefore neither
-- total impact nor headcount alone determines per-consumer material burden.
------------------------------------------------------------------------

data AllocationWorld : Set where
  sameTotalLowUse : AllocationWorld
  sameTotalHighUse : AllocationWorld
  sameCountShortResourceTime : AllocationWorld
  sameCountLongResourceTime : AllocationWorld

data TotalImpactSurface : Set where
  sameTotalImpact : TotalImpactSurface

data ConsumerCountSurface : Set where
  sameConsumerCount : ConsumerCountSurface

totalImpactProjection : AllocationWorld → TotalImpactSurface
totalImpactProjection sameTotalLowUse = sameTotalImpact
totalImpactProjection sameTotalHighUse = sameTotalImpact
totalImpactProjection sameCountShortResourceTime = sameTotalImpact
totalImpactProjection sameCountLongResourceTime = sameTotalImpact

consumerCountProjection : AllocationWorld → ConsumerCountSurface
consumerCountProjection sameTotalLowUse = sameConsumerCount
consumerCountProjection sameTotalHighUse = sameConsumerCount
consumerCountProjection sameCountShortResourceTime = sameConsumerCount
consumerCountProjection sameCountLongResourceTime = sameConsumerCount

perConsumerImpactClass : AllocationWorld → Bool
perConsumerImpactClass sameTotalLowUse = true
perConsumerImpactClass sameTotalHighUse = false
perConsumerImpactClass sameCountShortResourceTime = false
perConsumerImpactClass sameCountLongResourceTime = true

totalImpactOutcomesDiffer :
  perConsumerImpactClass sameTotalLowUse ≡
  perConsumerImpactClass sameTotalHighUse → ⊥
totalImpactOutcomesDiffer ()

consumerCountOutcomesDiffer :
  perConsumerImpactClass sameCountShortResourceTime ≡
  perConsumerImpactClass sameCountLongResourceTime → ⊥
consumerCountOutcomesDiffer ()

totalImpactWitness :
  Factors.NonFactorabilityWitness totalImpactProjection perConsumerImpactClass
totalImpactWitness = Factors.nonFactorabilityWitness
  sameTotalLowUse sameTotalHighUse refl totalImpactOutcomesDiffer

consumerCountWitness :
  Factors.NonFactorabilityWitness consumerCountProjection perConsumerImpactClass
consumerCountWitness = Factors.nonFactorabilityWitness
  sameCountShortResourceTime sameCountLongResourceTime refl consumerCountOutcomesDiffer

totalImpactCannotDeterminePerConsumerImpact :
  Factors.FactorsThrough totalImpactProjection perConsumerImpactClass → ⊥
totalImpactCannotDeterminePerConsumerImpact =
  Factors.witnessRulesOutEveryFlatFactorisation totalImpactWitness

consumerCountCannotDeterminePerConsumerImpact :
  Factors.FactorsThrough consumerCountProjection perConsumerImpactClass → ⊥
consumerCountCannotDeterminePerConsumerImpact =
  Factors.witnessRulesOutEveryFlatFactorisation consumerCountWitness

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data ContextualAllocationCreatesEducationDeploymentFootprint : Set where
data MoreConsumersAutomaticallyCreateLowerAbsoluteBurden : Set where
data LowerAllocatedPerRequestImpactCreatesLowerAggregateImpact : Set where
data TrainingAmortisationCreatesKnownTotalUsage : Set where
data AccountingAllocationCreatesBurdenIncidenceJustice : Set where
data MaterialAllocationCreatesHistoricalMarxistInterpretation : Set where

contextualAllocationDoesNotCreateEducationDeploymentFootprint :
  ContextualAllocationCreatesEducationDeploymentFootprint → ⊥
contextualAllocationDoesNotCreateEducationDeploymentFootprint ()

moreConsumersDoNotAutomaticallyCreateLowerAbsoluteBurden :
  MoreConsumersAutomaticallyCreateLowerAbsoluteBurden → ⊥
moreConsumersDoNotAutomaticallyCreateLowerAbsoluteBurden ()

lowerPerRequestAllocationDoesNotCreateLowerAggregateImpact :
  LowerAllocatedPerRequestImpactCreatesLowerAggregateImpact → ⊥
lowerPerRequestAllocationDoesNotCreateLowerAggregateImpact ()

trainingAmortisationDoesNotCreateKnownTotalUsage :
  TrainingAmortisationCreatesKnownTotalUsage → ⊥
trainingAmortisationDoesNotCreateKnownTotalUsage ()

accountingAllocationDoesNotCreateBurdenIncidenceJustice :
  AccountingAllocationCreatesBurdenIncidenceJustice → ⊥
accountingAllocationDoesNotCreateBurdenIncidenceJustice ()

materialAllocationDoesNotCreateHistoricalMarxistInterpretation :
  MaterialAllocationCreatesHistoricalMarxistInterpretation → ⊥
materialAllocationDoesNotCreateHistoricalMarxistInterpretation ()

record MaterialImpactAllocationBoundary : Set where
  constructor material-impact-allocation-boundary
  field
    functionalUnitRetained : Bool
    functionalUnitRetainedIsTrue : functionalUnitRetained ≡ true
    allocationBasisRetained : Bool
    allocationBasisRetainedIsTrue : allocationBasisRetained ≡ true
    denominatorAndUtilisationRetained : Bool
    denominatorAndUtilisationRetainedIsTrue : denominatorAndUtilisationRetained ≡ true
    trainingServingEmbodiedSeparated : Bool
    trainingServingEmbodiedSeparatedIsTrue : trainingServingEmbodiedSeparated ≡ true
    allocationAndIncidenceRemainDistinct : Bool
    allocationAndIncidenceRemainDistinctIsTrue : allocationAndIncidenceRemainDistinct ≡ true
    perConsumerImpactDeterminedByTotalImpactAlone : Bool
    perConsumerImpactDeterminedByTotalImpactAloneIsFalse :
      perConsumerImpactDeterminedByTotalImpactAlone ≡ false
    perConsumerImpactDeterminedByConsumerCountAlone : Bool
    perConsumerImpactDeterminedByConsumerCountAloneIsFalse :
      perConsumerImpactDeterminedByConsumerCountAlone ≡ false

open MaterialImpactAllocationBoundary public

canonicalMaterialImpactAllocationBoundary : MaterialImpactAllocationBoundary
canonicalMaterialImpactAllocationBoundary = material-impact-allocation-boundary
  true refl true refl true refl true refl true refl false refl false refl

materialImpactAllocationReading : String
materialImpactAllocationReading =
  "Shared digital/AI material burdens must be allocated using an explicit functional unit and allocation rule. Primary AI-LCA methods show request-level embodied impact being allocated by resource-time/lifetime assumptions rather than by user count alone. The existing AI economics owner separately retains training compute per release, amortised training compute per successful task and serving compute per task. Digital-ESD therefore asks what denominator, utilisation, lifetime and task definition support a per-consumer figure. Lower allocated impact per request does not imply lower aggregate burden, and allocation accounting does not adjudicate who justly bears the externality."
