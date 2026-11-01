module DASHI.Biology.ResourceCoupledLogisticEvolutionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Biology.ResourceCoupledLogisticReplicationExact as Resource
import DASHI.Biology.Evolution.EvolutionaryPopulationDynamics as Evolution
import DASHI.Biology.Cell.OpenMetabolicNetwork as Metabolism
import DASHI.Biology.AgenticMaterialsControlCore as Agentic

------------------------------------------------------------------------
-- RESOURCE-COUPLED LOGISTIC / EVOLUTIONARY-SYSTEM REALISATION
--
-- EvolutionaryPopulationDynamics already owns the generic environment-indexed
-- reproduction and population-to-environment ecological-feedback interfaces.
-- This module states the exact commuting receipts needed for a resource-coupled
-- logistic system to realise that pair of interfaces.  It does not derive the
-- remaining evolutionary coordinates: heredity, mutation, recombination,
-- selection, drift, phenotype, or historical trajectory.
------------------------------------------------------------------------

record ResourceCoupledEvolutionRealisation
    (S : Resource.ResourceCoupledLogisticSystem)
    (E : Evolution.EvolutionarySystem) : Set₁ where
  constructor resource-coupled-evolution-realisation
  field
    populationMap :
      Resource.Population S → Evolution.EvolutionarySystem.Population E
    environmentMap :
      Resource.Resource S → Evolution.EvolutionarySystem.Environment E

    reproductionCommutes :
      (resource : Resource.Resource S) →
      (population : Resource.Population S) →
      populationMap (Resource.populationStep S resource population)
      ≡
      Evolution.EvolutionarySystem.reproduce E
        (environmentMap resource)
        (populationMap population)

    ecologicalFeedbackCommutes :
      (population : Resource.Population S) →
      (resource : Resource.Resource S) →
      environmentMap (Resource.resourceStep S population resource)
      ≡
      Evolution.EvolutionarySystem.ecologicalFeedback E
        (populationMap population)
        (environmentMap resource)

    reproductionReference : String
    ecologicalFeedbackReference : String
    realisationReference : String

open ResourceCoupledEvolutionRealisation public

------------------------------------------------------------------------
-- Product-state commuting square.
------------------------------------------------------------------------

record EvolutionPopulationEnvironmentState
    (E : Evolution.EvolutionarySystem) : Set where
  constructor evolution-population-environment-state
  field
    population : Evolution.EvolutionarySystem.Population E
    environment : Evolution.EvolutionarySystem.Environment E

open EvolutionPopulationEnvironmentState public

evolutionCoupledStep :
  (E : Evolution.EvolutionarySystem) →
  EvolutionPopulationEnvironmentState E →
  EvolutionPopulationEnvironmentState E
evolutionCoupledStep E state =
  evolution-population-environment-state
    (Evolution.EvolutionarySystem.reproduce E
      (environment state) (population state))
    (Evolution.EvolutionarySystem.ecologicalFeedback E
      (population state) (environment state))

mapCoupledState :
  ∀ {S E} →
  ResourceCoupledEvolutionRealisation S E →
  Resource.ResourcePopulationState S →
  EvolutionPopulationEnvironmentState E
mapCoupledState R state =
  evolution-population-environment-state
    (populationMap R (Resource.population state))
    (environmentMap R (Resource.resource state))

coupledStepCommutes :
  ∀ {S E} →
  (R : ResourceCoupledEvolutionRealisation S E) →
  (state : Resource.ResourcePopulationState S) →
  mapCoupledState R (Resource.coupledStep S state)
  ≡
  evolutionCoupledStep E (mapCoupledState R state)
coupledStepCommutes R state =
  cong₂ evolution-population-environment-state
    (reproductionCommutes R
      (Resource.resource state)
      (Resource.population state))
    (ecologicalFeedbackCommutes R
      (Resource.population state)
      (Resource.resource state))

------------------------------------------------------------------------
-- Metabolism and agency remain stricter downstream coordinates.
------------------------------------------------------------------------

record EvolutionMetabolismJoinBoundary
    (S : Resource.ResourceCoupledLogisticSystem)
    (E : Evolution.EvolutionarySystem) : Set₁ where
  constructor evolution-metabolism-join-boundary
  field
    realisation : ResourceCoupledEvolutionRealisation S E

    MetabolicNetwork : Set
    metabolicNetworkWitness : MetabolicNetwork → Set

    AgenticSystem : Set
    agenticSystemWitness : AgenticSystem → Set

    metabolismReference : String
    agencyReference : String

open EvolutionMetabolismJoinBoundary public

data EvolutionRealisationMeansMetabolismPermission : Set where

data EvolutionRealisationMeansAgencyPermission : Set where

data EvolutionRealisationMeansHistoricalProofPermission : Set where

data LogisticReproductionMeansSelectionPermission : Set where

data LogisticReproductionMeansHeredityPermission : Set where

resourceEvolutionRealisationDoesNotProveMetabolism :
  EvolutionRealisationMeansMetabolismPermission → ⊥
resourceEvolutionRealisationDoesNotProveMetabolism ()

resourceEvolutionRealisationDoesNotProveAgency :
  EvolutionRealisationMeansAgencyPermission → ⊥
resourceEvolutionRealisationDoesNotProveAgency ()

resourceEvolutionRealisationDoesNotProveHistoricalPath :
  EvolutionRealisationMeansHistoricalProofPermission → ⊥
resourceEvolutionRealisationDoesNotProveHistoricalPath ()

logisticReproductionDoesNotByItselfSupplySelection :
  LogisticReproductionMeansSelectionPermission → ⊥
logisticReproductionDoesNotByItselfSupplySelection ()

logisticReproductionDoesNotByItselfSupplyHeredity :
  LogisticReproductionMeansHeredityPermission → ⊥
logisticReproductionDoesNotByItselfSupplyHeredity ()

record ResourceCoupledEvolutionBoundary : Set where
  constructor resource-coupled-evolution-boundary
  field
    resourceSystemCanRealiseEnvironmentIndexedReproduction : Bool
    populationFeedbackCanRealiseEcologicalFeedback : Bool
    coupledProductSquareCanCommute : Bool
    reproductionAloneSuppliesSelection : Bool
    reproductionAloneSuppliesHeredity : Bool
    resourceEvolutionRealisationIsMetabolism : Bool
    resourceEvolutionRealisationIsAgency : Bool
    resourceEvolutionRealisationProvesHistory : Bool

canonicalResourceCoupledEvolutionBoundary : ResourceCoupledEvolutionBoundary
canonicalResourceCoupledEvolutionBoundary =
  resource-coupled-evolution-boundary
    true true true false false false false false
