module DASHI.Economics.ComputeScalingUnitEconomicsExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- COMPUTE SCALING / UNIT-ECONOMICS OBSERVER
--
-- Model size, active parameters, training compute, inference compute per token,
-- tokens per task and useful work are distinct coordinates.  No one coordinate
-- is allowed to stand in for the others without an explicit producer.
------------------------------------------------------------------------

record ComputeScalingSystem : Set₁ where
  field
    Model Hardware Workload Time : Set
    ParameterCount ActiveParameterCount TrainingCompute : Model → Time → Set
    InferenceComputePerToken : Model → Hardware → Workload → Time → Set
    TokensPerWorkload : Model → Workload → Time → Set
    UsefulWork : Model → Workload → Time → Set
    CostPerToken CostPerUsefulWork : Model → Hardware → Workload → Time → Set
    Capability : Model → Workload → Time → Set

open ComputeScalingSystem public

record ScalingObservation
    (sys : ComputeScalingSystem)
    (model : Model sys)
    (hardware : Hardware sys)
    (workload : Workload sys)
    (time : Time sys) : Set₁ where
  field
    parameterCount : ParameterCount sys model time
    activeParameterCount : ActiveParameterCount sys model time
    trainingCompute : TrainingCompute sys model time
    inferenceComputePerToken : InferenceComputePerToken sys model hardware workload time
    tokensPerWorkload : TokensPerWorkload sys model workload time
    usefulWork : UsefulWork sys model workload time
    costPerToken : CostPerToken sys model hardware workload time
    costPerUsefulWork : CostPerUsefulWork sys model hardware workload time
    capability : Capability sys model workload time

open ScalingObservation public

record ComputeDeflation
    (sys : ComputeScalingSystem)
    (modelBefore modelAfter : Model sys)
    (hardwareBefore hardwareAfter : Hardware sys)
    (workload : Workload sys)
    (before after : Time sys) : Set₁ where
  field
    beforeObservation : ScalingObservation sys modelBefore hardwareBefore workload before
    afterObservation  : ScalingObservation sys modelAfter hardwareAfter workload after
    costPerUsefulWorkFell : Set

record ReboundDemand
    (sys : ComputeScalingSystem)
    (modelBefore modelAfter : Model sys)
    (hardwareBefore hardwareAfter : Hardware sys)
    (workload : Workload sys)
    (before after : Time sys) : Set₁ where
  field
    deflation : ComputeDeflation sys modelBefore modelAfter hardwareBefore hardwareAfter workload before after
    tokensPerWorkloadRose : Set
    aggregateComputeDemandRose : Set

record EfficiencyGainWithCapitalPressure
    (sys : ComputeScalingSystem)
    (modelBefore modelAfter : Model sys)
    (hardwareBefore hardwareAfter : Hardware sys)
    (workload : Workload sys)
    (before after : Time sys) : Set₁ where
  field
    computeDeflation : ComputeDeflation sys modelBefore modelAfter hardwareBefore hardwareAfter workload before after
    monetisablePricePressure : Set
    incumbentAssetRevenuePressure : Set

data LargerModelImpliesMoreInferenceComputePerTokenPermission : Set where

data LowerCostPerTokenImpliesLowerTotalComputeDemandPermission : Set where

data HigherCapabilityImpliesHigherEconomicValuePermission : Set where

data LowerInferenceComputePerTokenImpliesLowerTokensPerTaskPermission : Set where

data ComputeDeflationImpliesLowerAggregateCapexPermission : Set where

largerModelDoesNotAutoPromoteToMoreInferenceComputePerToken :
  LargerModelImpliesMoreInferenceComputePerTokenPermission → ⊥
largerModelDoesNotAutoPromoteToMoreInferenceComputePerToken ()

lowerCostPerTokenDoesNotAutoPromoteToLowerTotalComputeDemand :
  LowerCostPerTokenImpliesLowerTotalComputeDemandPermission → ⊥
lowerCostPerTokenDoesNotAutoPromoteToLowerTotalComputeDemand ()

higherCapabilityDoesNotAutoPromoteToHigherEconomicValue :
  HigherCapabilityImpliesHigherEconomicValuePermission → ⊥
higherCapabilityDoesNotAutoPromoteToHigherEconomicValue ()

lowerInferenceComputePerTokenDoesNotAutoPromoteToLowerTokensPerTask :
  LowerInferenceComputePerTokenImpliesLowerTokensPerTaskPermission → ⊥
lowerInferenceComputePerTokenDoesNotAutoPromoteToLowerTokensPerTask ()

computeDeflationDoesNotAutoPromoteToLowerAggregateCapex :
  ComputeDeflationImpliesLowerAggregateCapexPermission → ⊥
computeDeflationDoesNotAutoPromoteToLowerAggregateCapex ()
