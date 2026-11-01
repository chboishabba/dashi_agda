module DASHI.Economics.AITrainingServingEconomicTimeSeriesCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIEconomicUsefulWorkTimeSeriesExact as Useful
import DASHI.Economics.AIScalingLawRegimeMonitorExact as Scaling
import DASHI.Economics.ChinaUSAITrainingServingComputeSeparation2026Exact as ChinaUS
import DASHI.Economics.AIEconomicUsefulWorkSourceAdmissionExact as Admission

------------------------------------------------------------------------
-- TRAINING / SERVING / USEFUL-WORK JOINT MONITOR
--
-- The infrastructure financing stack is sensitive to both finite training
-- requirements and persistent serving requirements.  Parameter count is kept
-- as a descriptive scaling coordinate, not a proxy for either cost or value.
------------------------------------------------------------------------

data TrainingServingEconomicCoordinate : Set where
  totalModelParameters : TrainingServingEconomicCoordinate
  activeModelParameters : TrainingServingEconomicCoordinate
  trainingComputePerModelRelease : TrainingServingEconomicCoordinate
  amortisedTrainingComputePerSuccessfulTask : TrainingServingEconomicCoordinate
  servingComputePerSuccessfulTask : TrainingServingEconomicCoordinate
  inferenceComputePerToken : TrainingServingEconomicCoordinate
  tokensPerSuccessfulTask : TrainingServingEconomicCoordinate
  successfulTasksPerAcceleratorTime : TrainingServingEconomicCoordinate
  revenuePerSuccessfulTask : TrainingServingEconomicCoordinate
  fullyLoadedCostPerSuccessfulTask : TrainingServingEconomicCoordinate
  grossContributionPerSuccessfulTask : TrainingServingEconomicCoordinate
  acceleratorResidualRentalValue : TrainingServingEconomicCoordinate
  acceleratorUtilisation : TrainingServingEconomicCoordinate


record TrainingServingEconomicObservation : Set₁ where
  constructor trainingServingEconomicObservation
  field
    coordinate : TrainingServingEconomicCoordinate
    Value : Set
    value : Value
    sourceReference : String
    sameTaskDefinition : Set
    sameSuccessCriterion : Set
    sameHardwareOrExplicitTransport : Set
    sameCostBoundaryOrExplicitTransport : Set
    sourceAdmission : Admission.TimeSeriesAdmissionReceipt

open TrainingServingEconomicObservation public

record TrainingServingEconomicSnapshot : Set₁ where
  constructor trainingServingEconomicSnapshot
  field
    totalParametersReceipt : TrainingServingEconomicObservation
    activeParametersReceipt : TrainingServingEconomicObservation
    trainingComputeReceipt : TrainingServingEconomicObservation
    amortisedTrainingComputeReceipt : TrainingServingEconomicObservation
    servingComputeReceipt : TrainingServingEconomicObservation
    computePerTokenReceipt : TrainingServingEconomicObservation
    tokensPerTaskReceipt : TrainingServingEconomicObservation
    taskThroughputReceipt : TrainingServingEconomicObservation
    revenuePerTaskReceipt : TrainingServingEconomicObservation
    fullyLoadedCostPerTaskReceipt : TrainingServingEconomicObservation
    contributionPerTaskReceipt : TrainingServingEconomicObservation
    residualRentalValueReceipt : TrainingServingEconomicObservation
    utilisationReceipt : TrainingServingEconomicObservation

open TrainingServingEconomicSnapshot public

------------------------------------------------------------------------
-- Economically important decompositions.
------------------------------------------------------------------------

record TrainingAmortisationBoundary : Set₁ where
  constructor trainingAmortisationBoundary
  field
    TrainingCompute SuccessfulTaskCount : Set
    trainingCompute : TrainingCompute
    successfulTaskCount : SuccessfulTaskCount
    AmortisationRule : Set
    amortisationRule : AmortisationRule
    ruleReference : String

open TrainingAmortisationBoundary public

record ServingCapacityEconomics : Set₁ where
  constructor servingCapacityEconomics
  field
    ServingCompute SuccessfulTask Revenue FullyLoadedCost : Set
    servingCompute : ServingCompute
    successfulTask : SuccessfulTask
    revenue : Revenue
    fullyLoadedCost : FullyLoadedCost
    sameTaskObject : Set

open ServingCapacityEconomics public

-- The same frontier-capability level can coexist with very different serving
-- economics.  This is the key reason national/model capability rankings cannot
-- stand in for hosted-infrastructure economics.
record CapabilityServingEconomicDivergence : Set₁ where
  constructor capabilityServingEconomicDivergence
  field
    CapabilityComparison ServingEconomicComparison : Set
    capabilityComparison : CapabilityComparison
    servingEconomicComparison : ServingEconomicComparison
    comparisonObjectsKeptSeparate : Set

open CapabilityServingEconomicDivergence public

------------------------------------------------------------------------
-- Four futures lifted onto explicit training/serving coordinates.
------------------------------------------------------------------------

data TrainingServingFutureClass : Set where
  cheaperServingDemandExpansionMarginExpansion : TrainingServingFutureClass
  cheaperServingDemandExpansionMarginCompression : TrainingServingFutureClass
  cheaperServingDemandExpansionAssetImpairment : TrainingServingFutureClass
  cheaperServingDemandDeclineOvercapacity : TrainingServingFutureClass
  trainingCheapServingScarce : TrainingServingFutureClass
  trainingExpensiveServingEfficient : TrainingServingFutureClass


record TrainingServingFutureClassification : Set₁ where
  constructor trainingServingFutureClassification
  field
    before after : TrainingServingEconomicSnapshot
    futureClass : TrainingServingFutureClass
    derivativeReceipt : Set
    sourceComparable : Set

open TrainingServingFutureClassification public

------------------------------------------------------------------------
-- Existing source-backed China/US case retained as a calibration, not a law.
------------------------------------------------------------------------

chinaUSCalibration : ChinaUS.SourceBackedTrainingServingCalibration
chinaUSCalibration = ChinaUS.canonicalSourceBackedTrainingServingCalibration

scalingBoundary : Scaling.HistoricalFitImpliesUniversalFutureLawPermission → ⊥
scalingBoundary = Scaling.historicalFitDoesNotAutoPromoteToUniversalFutureLaw

usefulWorkBoundary : Useful.UsageGrowthDeterminesFutureClassPermission → ⊥
usefulWorkBoundary = Useful.usageGrowthDoesNotDetermineFutureClass

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ParameterCountImpliesServingComputePermission : Set where

data TrainingComputeImpliesServingComputePermission : Set where

data TrainingCostDeclineImpliesHostedMarginExpansionPermission : Set where

data ServingEfficiencyImpliesResidualAssetValuePermission : Set where

data CapabilityGapImpliesServingEconomicsGapPermission : Set where

data OpenWeightsImplyZeroAggregateServingCapexPermission : Set where

parameterCountDoesNotAutoPromoteToServingCompute :
  ParameterCountImpliesServingComputePermission → ⊥
parameterCountDoesNotAutoPromoteToServingCompute ()

trainingComputeDoesNotAutoPromoteToServingCompute :
  TrainingComputeImpliesServingComputePermission → ⊥
trainingComputeDoesNotAutoPromoteToServingCompute ()

trainingCostDeclineDoesNotAutoPromoteToHostedMarginExpansion :
  TrainingCostDeclineImpliesHostedMarginExpansionPermission → ⊥
trainingCostDeclineDoesNotAutoPromoteToHostedMarginExpansion ()

servingEfficiencyDoesNotAutoPromoteToResidualAssetValue :
  ServingEfficiencyImpliesResidualAssetValuePermission → ⊥
servingEfficiencyDoesNotAutoPromoteToResidualAssetValue ()

capabilityGapDoesNotAutoPromoteToServingEconomicsGap :
  CapabilityGapImpliesServingEconomicsGapPermission → ⊥
capabilityGapDoesNotAutoPromoteToServingEconomicsGap ()

openWeightsDoNotAutoPromoteToZeroAggregateServingCapex :
  OpenWeightsImplyZeroAggregateServingCapexPermission → ⊥
openWeightsDoNotAutoPromoteToZeroAggregateServingCapex ()
