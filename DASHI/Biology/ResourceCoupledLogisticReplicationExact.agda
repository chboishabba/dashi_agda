module DASHI.Biology.ResourceCoupledLogisticReplicationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Dynamics.LogisticAdicStageCommutingSpine as Logistic
import DASHI.Biology.Cell.OpenMetabolicNetwork as Metabolism

------------------------------------------------------------------------
-- RESOURCE-COUPLED LOGISTIC REPLICATION
--
-- This owner makes the resource/environment coordinate dynamical rather than
-- leaving it beside the population as passive residual metadata.  It reuses the
-- canonical generic logistic polynomial.  Concrete real/rational models may
-- realise normalisation as N/K(R), but division and continuum claims are not
-- invented here.
------------------------------------------------------------------------

record ResourceCoupledLogisticSystem : Set₁ where
  constructor resource-coupled-logistic-system
  field
    Population : Set
    Resource : Set
    Normalised : Set
    Capacity : Set

    algebra : Logistic.LogisticAlgebra Normalised

    growthParameter : Resource → Normalised
    carryingCapacity : Resource → Capacity

    normalise : Population → Capacity → Normalised
    realise : Normalised → Capacity → Population

    resourceStep : Population → Resource → Resource

    growthReference : String
    capacityReference : String
    resourceReference : String
    environmentReference : String

open ResourceCoupledLogisticSystem public

normalisedPopulationStep :
  (S : ResourceCoupledLogisticSystem) →
  Resource S → Population S → Normalised S
normalisedPopulationStep S resource population =
  Logistic.logisticStep
    (algebra S)
    (growthParameter S resource)
    (normalise S population (carryingCapacity S resource))

populationStep :
  (S : ResourceCoupledLogisticSystem) →
  Resource S → Population S → Population S
populationStep S resource population =
  realise S
    (normalisedPopulationStep S resource population)
    (carryingCapacity S resource)

record ResourcePopulationState (S : ResourceCoupledLogisticSystem) : Set where
  constructor resource-population-state
  field
    population : Population S
    resource : Resource S

open ResourcePopulationState public

coupledStep :
  (S : ResourceCoupledLogisticSystem) →
  ResourcePopulationState S → ResourcePopulationState S
coupledStep S state =
  resource-population-state
    (populationStep S (resource state) (population state))
    (resourceStep S (population state) (resource state))

record ResourceCoupledStepReceipt
    (S : ResourceCoupledLogisticSystem)
    (before after : ResourcePopulationState S) : Set where
  constructor resource-coupled-step-receipt
  field
    populationUpdate :
      population after
      ≡ populationStep S (resource before) (population before)
    resourceUpdate :
      resource after
      ≡ resourceStep S (population before) (resource before)

open ResourceCoupledStepReceipt public

canonicalResourceCoupledStepReceipt :
  (S : ResourceCoupledLogisticSystem) →
  (before : ResourcePopulationState S) →
  ResourceCoupledStepReceipt S before (coupledStep S before)
canonicalResourceCoupledStepReceipt S before =
  resource-coupled-step-receipt refl refl

------------------------------------------------------------------------
-- Optional metabolic realization.
--
-- A resource carrier may be interpreted inside an OpenMetabolicNetwork only
-- when an explicit realization is supplied.  Resource depletion or resource-
-- dependent growth alone does not construct fluxes, gradients, cycles,
-- boundedness, or restoration.
------------------------------------------------------------------------

record MetabolicResourceRealisation
    (S : ResourceCoupledLogisticSystem)
    (M : Metabolism.OpenMetabolicNetwork) : Set₁ where
  constructor metabolic-resource-realisation
  field
    resourceToNetworkState :
      Resource S → Metabolism.OpenMetabolicNetwork.NetworkState M
    resourceToEnvironment :
      Resource S → Metabolism.OpenMetabolicNetwork.Environment M
    populationToNetworkState :
      Population S → Metabolism.OpenMetabolicNetwork.NetworkState M

    resourceRealisationReference : String
    populationRealisationReference : String

open MetabolicResourceRealisation public

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data ResourceCoupledGrowthMeansMetabolismPermission : Set where

data ResourceCoupledGrowthMeansAgencyPermission : Set where

data ResourceCoupledGrowthMeansAbiogenesisPermission : Set where

data ResourceModulationMeansCarryingCapacityMeasuredPermission : Set where

resourceCoupledGrowthDoesNotByItselfProveMetabolism :
  ResourceCoupledGrowthMeansMetabolismPermission → ⊥
resourceCoupledGrowthDoesNotByItselfProveMetabolism ()

resourceCoupledGrowthDoesNotByItselfProveAgency :
  ResourceCoupledGrowthMeansAgencyPermission → ⊥
resourceCoupledGrowthDoesNotByItselfProveAgency ()

resourceCoupledGrowthDoesNotByItselfProveAbiogenesis :
  ResourceCoupledGrowthMeansAbiogenesisPermission → ⊥
resourceCoupledGrowthDoesNotByItselfProveAbiogenesis ()

resourceModulationDoesNotClaimEmpiricalCapacityMeasurement :
  ResourceModulationMeansCarryingCapacityMeasuredPermission → ⊥
resourceModulationDoesNotClaimEmpiricalCapacityMeasurement ()

record ResourceCoupledLogisticBoundary : Set where
  constructor resource-coupled-logistic-boundary
  field
    resourceMayModulateGrowthParameter : Bool
    resourceMayModulateCarryingCapacity : Bool
    populationMayFeedBackIntoResource : Bool
    populationAndResourceUpdateRemainSeparate : Bool
    resourceCoupledGrowthDefinitionallyIsMetabolism : Bool
    resourceCoupledGrowthDefinitionallyIsAgency : Bool
    resourceCoupledGrowthProvesAbiogenesis : Bool
    empiricalParameterCalibrationStillRequired : Bool

canonicalResourceCoupledLogisticBoundary : ResourceCoupledLogisticBoundary
canonicalResourceCoupledLogisticBoundary =
  resource-coupled-logistic-boundary
    true true true true false false false true
