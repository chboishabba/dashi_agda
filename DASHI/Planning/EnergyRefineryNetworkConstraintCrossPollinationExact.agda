module DASHI.Planning.EnergyRefineryNetworkConstraintCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Planning.NetworkFlowCapacityCongestionExact as Network
import DASHI.Planning.PlanningAdmissibleTransitionBridgeExact as Admission
import DASHI.Chemistry.RefineryFeedstockSaltConstraintBidiExact as Refinery

------------------------------------------------------------------------
-- ENERGY / REFINERY / NETWORK PLANNING CROSS-POLLINATION
--
-- Crude supply, refinery nameplate capacity, chemistry-qualified effective
-- throughput, transport/logistics capacity and product-delivery capacity remain
-- separate planning coordinates.  A locally feasible supply increase does not
-- automatically preserve whole-network feasibility or increase delivered fuel.
------------------------------------------------------------------------

data EnergyPlanningState : Set where
  crudeAbundantRefiningConstrained
  crudeAbundantRefiningAvailable
  : EnergyPlanningState

data CrudeSupplySurface : Set where
  crudeSupplyAdequate : CrudeSupplySurface

data RefineryEffectiveCapacity : Set where
  effectiveCapacityConstrained effectiveCapacityAvailable : RefineryEffectiveCapacity

data DeliveredProductCapacity : Set where
  deliveredProductConstrained deliveredProductAvailable : DeliveredProductCapacity

data ConsumerAvailability : Set where
  consumerSupplyTight consumerSupplyLoose : ConsumerAvailability

crudeSupplySurface : EnergyPlanningState → CrudeSupplySurface
crudeSupplySurface _ = crudeSupplyAdequate

refineryEffectiveCapacity : EnergyPlanningState → RefineryEffectiveCapacity
refineryEffectiveCapacity crudeAbundantRefiningConstrained = effectiveCapacityConstrained
refineryEffectiveCapacity crudeAbundantRefiningAvailable = effectiveCapacityAvailable

deliveredProductCapacity : EnergyPlanningState → DeliveredProductCapacity
deliveredProductCapacity crudeAbundantRefiningConstrained = deliveredProductConstrained
deliveredProductCapacity crudeAbundantRefiningAvailable = deliveredProductAvailable

consumerAvailability : EnergyPlanningState → ConsumerAvailability
consumerAvailability crudeAbundantRefiningConstrained = consumerSupplyTight
consumerAvailability crudeAbundantRefiningAvailable = consumerSupplyLoose

sameCrudeSupply :
  crudeSupplySurface crudeAbundantRefiningConstrained
  ≡ crudeSupplySurface crudeAbundantRefiningAvailable
sameCrudeSupply = refl

refineryCapacityDiffers :
  refineryEffectiveCapacity crudeAbundantRefiningConstrained
  ≡ refineryEffectiveCapacity crudeAbundantRefiningAvailable → ⊥
refineryCapacityDiffers ()

consumerAvailabilityDiffers :
  consumerAvailability crudeAbundantRefiningConstrained
  ≡ consumerAvailability crudeAbundantRefiningAvailable → ⊥
consumerAvailabilityDiffers ()

crudeSupplyCannotRecoverRefineryCapacity :
  INF.FactorsThrough crudeSupplySurface refineryEffectiveCapacity → ⊥
crudeSupplyCannotRecoverRefineryCapacity =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      crudeAbundantRefiningConstrained
      crudeAbundantRefiningAvailable
      sameCrudeSupply
      refineryCapacityDiffers)

crudeSupplyCannotRecoverConsumerAvailability :
  INF.FactorsThrough crudeSupplySurface consumerAvailability → ⊥
crudeSupplyCannotRecoverConsumerAvailability =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      crudeAbundantRefiningConstrained
      crudeAbundantRefiningAvailable
      sameCrudeSupply
      consumerAvailabilityDiffers)

------------------------------------------------------------------------
-- Planning/resource graph.
------------------------------------------------------------------------

data EnergyNetworkStage : Set where
  production gathering pipelineOrShipping refinery productStorage distribution retail : EnergyNetworkStage

data ConstraintKind : Set where
  chemistryConstraint processCapacityConstraint logisticsConstraint storageConstraint demandConstraint : ConstraintKind

record EnergyNetworkConstraintReceipt : Set where
  constructor energy-network-constraint-receipt
  field
    stage : EnergyNetworkStage
    constraint : ConstraintKind
    capacityReference : String
    demandReference : String
    chemistryOrQualityReference : String
    outageMaintenanceReference : String
    transportReference : String
    validationReference : String

------------------------------------------------------------------------
-- Existing-owner welds.
------------------------------------------------------------------------

networkBoundary : Network.CoupledNetworkBoundary
networkBoundary = Network.canonicalCoupledNetworkBoundary

planningAdmissionBoundary : Admission.PlanningAdmissibleTransitionBoundary
planningAdmissionBoundary = Admission.canonicalPlanningAdmissibleTransitionBoundary

refinerySaltBoundary : Refinery.RefineryFeedstockSaltBoundary
refinerySaltBoundary = Refinery.canonicalRefineryFeedstockSaltBoundary

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record EnergyRefineryPlanningBoundary : Set where
  constructor energy-refinery-planning-boundary
  field
    crudeAbundanceImpliesDeliveredProductAbundance : Bool
    crudeAbundanceImpliesDeliveredProductAbundanceIsFalse :
      crudeAbundanceImpliesDeliveredProductAbundance ≡ false
    nameplateCapacityEqualsEffectiveCapacity : Bool
    nameplateCapacityEqualsEffectiveCapacityIsFalse :
      nameplateCapacityEqualsEffectiveCapacity ≡ false
    localSupplyFeasibilityImpliesWholeNetworkFeasibility : Bool
    localSupplyFeasibilityImpliesWholeNetworkFeasibilityIsFalse :
      localSupplyFeasibilityImpliesWholeNetworkFeasibility ≡ false
    spatialSeparationRemovesSharedLogisticsConstraint : Bool
    spatialSeparationRemovesSharedLogisticsConstraintIsFalse :
      spatialSeparationRemovesSharedLogisticsConstraint ≡ false
    chemistryQualifiedThroughputIsPlanningRelevant : Bool
    chemistryQualifiedThroughputIsPlanningRelevantIsTrue :
      chemistryQualifiedThroughputIsPlanningRelevant ≡ true

canonicalEnergyRefineryPlanningBoundary : EnergyRefineryPlanningBoundary
canonicalEnergyRefineryPlanningBoundary =
  energy-refinery-planning-boundary
    false refl
    false refl
    false refl
    false refl
    true refl
