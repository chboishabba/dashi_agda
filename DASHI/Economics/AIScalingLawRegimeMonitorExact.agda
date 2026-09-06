module DASHI.Economics.AIScalingLawRegimeMonitorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.ComputeScalingUnitEconomicsExact as Scaling
import DASHI.Economics.ManufacturingScarcityTimescaleExact as Manufacturing
import DASHI.Economics.UnitEconomicsMarginExact as Unit
import DASHI.Economics.HistoryIndexedMarketMechanismOODALoopExact as OODA

------------------------------------------------------------------------
-- HISTORY-INDEXED AI SCALING REGIME MONITOR
--
-- The monitored object is not just model size.  It tracks a vector whose
-- components can move in opposing directions: active parameters, inference
-- compute/token, tokens/workload, useful work, cost/useful-work, hardware
-- economics, and aggregate demand.
------------------------------------------------------------------------

data ScalingCoordinate : Set where
  totalParameters
  activeParameters
  trainingCompute
  inferenceComputePerToken
  tokensPerWorkload
  usefulWorkPerWorkload
  costPerToken
  costPerUsefulWork
  aggregateInferenceDemand
  acceleratorResidualValue
  acceleratorUtilisation
  : ScalingCoordinate

record ScalingCoordinateReceipt : Set₁ where
  constructor scalingCoordinateReceipt
  field
    Time : Set
    time : Time
    coordinate : ScalingCoordinate
    Observation : Set
    observation : Observation
    sourceReference : String
    sameMetricDefinitionAsPrevious : Set

open ScalingCoordinateReceipt public

record ScalingRegimeSnapshot : Set₁ where
  constructor scalingRegimeSnapshot
  field
    totalParameterReceipt : ScalingCoordinateReceipt
    activeParameterReceipt : ScalingCoordinateReceipt
    inferenceComputeReceipt : ScalingCoordinateReceipt
    tokensPerWorkloadReceipt : ScalingCoordinateReceipt
    usefulWorkReceipt : ScalingCoordinateReceipt
    costPerTokenReceipt : ScalingCoordinateReceipt
    costPerUsefulWorkReceipt : ScalingCoordinateReceipt
    aggregateDemandReceipt : ScalingCoordinateReceipt
    residualValueReceipt : ScalingCoordinateReceipt
    utilisationReceipt : ScalingCoordinateReceipt

open ScalingRegimeSnapshot public

------------------------------------------------------------------------
-- Scaling-law hypotheses are explicit hypotheses fitted to a metric family.
-- A finite historical fit cannot silently become a universal future law.
------------------------------------------------------------------------

record ScalingLawHypothesis : Set₁ where
  constructor scalingLawHypothesis
  field
    InputMetric OutputMetric Parameterisation FitDomain : Set
    inputMetric : InputMetric
    outputMetric : OutputMetric
    parameterisation : Parameterisation
    fitDomain : FitDomain
    fitReceipt : Set
    sourceReference : String

open ScalingLawHypothesis public

record ScalingLawUpdate : Set₁ where
  constructor scalingLawUpdate
  field
    previousHypothesis : ScalingLawHypothesis
    newSnapshot : ScalingRegimeSnapshot
    Residual : Set
    residual : Residual
    UpdatedHypothesis : Set
    updatedHypothesis : UpdatedHypothesis
    updateReference : String

open ScalingLawUpdate public

data HistoricalFitImpliesUniversalFutureLawPermission : Set where

data ParameterScalingImpliesUsefulWorkScalingPermission : Set where

data CostPerTokenDeclineImpliesCostPerUsefulWorkDeclinePermission : Set where

data ComputeEfficiencyImpliesLowerAggregateDemandPermission : Set where

data HighUtilisationImpliesHighResidualValuePermission : Set where

historicalFitDoesNotAutoPromoteToUniversalFutureLaw :
  HistoricalFitImpliesUniversalFutureLawPermission → ⊥
historicalFitDoesNotAutoPromoteToUniversalFutureLaw ()

parameterScalingDoesNotAutoPromoteToUsefulWorkScaling :
  ParameterScalingImpliesUsefulWorkScalingPermission → ⊥
parameterScalingDoesNotAutoPromoteToUsefulWorkScaling ()

costPerTokenDeclineDoesNotAutoPromoteToCostPerUsefulWorkDecline :
  CostPerTokenDeclineImpliesCostPerUsefulWorkDeclinePermission → ⊥
costPerTokenDeclineDoesNotAutoPromoteToCostPerUsefulWorkDecline ()

computeEfficiencyDoesNotAutoPromoteToLowerAggregateDemand :
  ComputeEfficiencyImpliesLowerAggregateDemandPermission → ⊥
computeEfficiencyDoesNotAutoPromoteToLowerAggregateDemand =
  Scaling.lowerCostPerTokenDoesNotAutoPromoteToLowerTotalComputeDemand

highUtilisationDoesNotAutoPromoteToHighResidualValue :
  HighUtilisationImpliesHighResidualValuePermission → ⊥
highUtilisationDoesNotAutoPromoteToHighResidualValue ()

------------------------------------------------------------------------
-- Reusable regime patterns.  These are shapes requiring empirical receipts,
-- not claims about the current market.
------------------------------------------------------------------------

record DeflationaryScalingWithDemandRebound : Set₁ where
  field
    CostPerUsefulWorkFalling AggregateDemandRising : Set
    costPerUsefulWorkFalling : CostPerUsefulWorkFalling
    aggregateDemandRising : AggregateDemandRising

record DeflationaryScalingWithAssetImpairment : Set₁ where
  field
    CostPerUsefulWorkFalling IncumbentResidualValueFalling : Set
    costPerUsefulWorkFalling : CostPerUsefulWorkFalling
    incumbentResidualValueFalling : IncumbentResidualValueFalling

record ScalingDrivenMarginSqueeze : Set₁ where
  field
    UsageRising PricePerUsefulWorkFalling ServingCostPressure : Set
    usageRising : UsageRising
    pricePerUsefulWorkFalling : PricePerUsefulWorkFalling
    servingCostPressure : ServingCostPressure

-- Keep direct links to the existing adaptive market-control and manufacturing
-- boundaries so future source-backed monitors can feed policy/model updates.
marketMechanismBoundary : OODA.HistoryIndexedMarketMechanismBoundary
marketMechanismBoundary = OODA.canonicalHistoryIndexedMarketMechanismBoundary

manufacturingResidualValueFirewall :
  Manufacturing.PhysicalFunctionalityImpliesHighResidualValuePermission → ⊥
manufacturingResidualValueFirewall =
  Manufacturing.physicalFunctionalityDoesNotAutoPromoteToHighResidualValue

usageUnitEconomicsFirewall :
  Unit.HighUsageImpliesPositiveUnitEconomicsPermission → ⊥
usageUnitEconomicsFirewall =
  Unit.highUsageDoesNotAutoPromoteToPositiveUnitEconomics
