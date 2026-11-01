module DASHI.Economics.AIEconomicUsefulWorkTimeSeriesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- AI ECONOMIC USEFUL-WORK TIME SERIES
--
-- The primary empirical target is successful useful work, not model size or
-- raw token volume.  Compute, revenue and fully-loaded cost are all observed
-- against the same declared workload/task-success definition.
------------------------------------------------------------------------

data EconomicWorkCoordinate : Set where
  computePerSuccessfulTask : EconomicWorkCoordinate
  revenuePerSuccessfulTask : EconomicWorkCoordinate
  fullyLoadedCostPerSuccessfulTask : EconomicWorkCoordinate
  inferenceComputePerToken : EconomicWorkCoordinate
  tokensPerSuccessfulTask : EconomicWorkCoordinate
  agentStepsPerSuccessfulTask : EconomicWorkCoordinate
  acceleratorPricePerformance : EconomicWorkCoordinate
  acceleratorResidualRentalValue : EconomicWorkCoordinate
  acceleratorUtilisation : EconomicWorkCoordinate


record TimeSeriesObservation : Set₁ where
  constructor timeSeriesObservation
  field
    Time : Set
    time : Time
    coordinate : EconomicWorkCoordinate
    Value : Set
    value : Value
    sourceReference : String
    sameTaskDefinition : Set
    sameSuccessCriterion : Set
    sameCostBoundaryOrExplicitTransport : Set

open TimeSeriesObservation public

record UsefulWorkEconomicSnapshot : Set₁ where
  constructor usefulWorkEconomicSnapshot
  field
    computePerTask : TimeSeriesObservation
    revenuePerTask : TimeSeriesObservation
    fullyLoadedCostPerTask : TimeSeriesObservation
    computePerToken : TimeSeriesObservation
    tokensPerTask : TimeSeriesObservation
    agentStepsPerTask : TimeSeriesObservation
    acceleratorPricePerformanceReceipt : TimeSeriesObservation
    residualRentalValueReceipt : TimeSeriesObservation
    utilisationReceipt : TimeSeriesObservation

open UsefulWorkEconomicSnapshot public

record UsefulWorkDerivativePair : Set₁ where
  constructor usefulWorkDerivativePair
  field
    before after : UsefulWorkEconomicSnapshot
    ComputePerTaskDirection RevenuePerTaskDirection FullyLoadedCostPerTaskDirection : Set
    AcceleratorPricePerformanceDirection ResidualRentalValueDirection UtilisationDirection : Set
    computePerTaskDirection : ComputePerTaskDirection
    revenuePerTaskDirection : RevenuePerTaskDirection
    fullyLoadedCostPerTaskDirection : FullyLoadedCostPerTaskDirection
    acceleratorPricePerformanceDirection : AcceleratorPricePerformanceDirection
    residualRentalValueDirection : ResidualRentalValueDirection
    utilisationDirection : UtilisationDirection

open UsefulWorkDerivativePair public

------------------------------------------------------------------------
-- Four economically distinct futures can inhabit the same headline statement
-- that AI usage is rising.
------------------------------------------------------------------------

data UsefulWorkFutureClass : Set where
  efficiencyDemandMarginExpansion : UsefulWorkFutureClass
  efficiencyDemandMarginCompression : UsefulWorkFutureClass
  efficiencyDemandIncumbentAssetImpairment : UsefulWorkFutureClass
  efficiencyDemandDeclineWithOvercapacity : UsefulWorkFutureClass


record UsefulWorkFutureClassification : Set₁ where
  constructor usefulWorkFutureClassification
  field
    derivativePair : UsefulWorkDerivativePair
    classification : UsefulWorkFutureClass
    classificationReceipt : Set

open UsefulWorkFutureClassification public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TokenGrowthImpliesUsefulWorkGrowthPermission : Set where

data ParameterGrowthImpliesComputePerTaskGrowthPermission : Set where

data LowerCostPerTokenImpliesLowerCostPerSuccessfulTaskPermission : Set where

data HigherUtilisationImpliesPositiveCapitalReturnPermission : Set where

data UsageGrowthDeterminesFutureClassPermission : Set where

tokenGrowthDoesNotAutoPromoteToUsefulWorkGrowth :
  TokenGrowthImpliesUsefulWorkGrowthPermission → ⊥
tokenGrowthDoesNotAutoPromoteToUsefulWorkGrowth ()

parameterGrowthDoesNotAutoPromoteToComputePerTaskGrowth :
  ParameterGrowthImpliesComputePerTaskGrowthPermission → ⊥
parameterGrowthDoesNotAutoPromoteToComputePerTaskGrowth ()

lowerCostPerTokenDoesNotAutoPromoteToLowerCostPerSuccessfulTask :
  LowerCostPerTokenImpliesLowerCostPerSuccessfulTaskPermission → ⊥
lowerCostPerTokenDoesNotAutoPromoteToLowerCostPerSuccessfulTask ()

higherUtilisationDoesNotAutoPromoteToPositiveCapitalReturn :
  HigherUtilisationImpliesPositiveCapitalReturnPermission → ⊥
higherUtilisationDoesNotAutoPromoteToPositiveCapitalReturn ()

usageGrowthDoesNotDetermineFutureClass :
  UsageGrowthDeterminesFutureClassPermission → ⊥
usageGrowthDoesNotDetermineFutureClass ()
