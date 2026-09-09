module DASHI.Environment.NitrogenPathwayLESCausalTransitionBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.NitrogenPathwayEnergeticMaterialComparisonExact as Nitrogen
import DASHI.Environment.SoilPlantAtmosphereContinuumExact as SPAC
import DASHI.Environment.SustainableManagementCausalEstimandExperimentBridgeExact as Causal
import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Environment.LESSituatedObservationInteractionExact as LES

------------------------------------------------------------------------
-- NITROGEN DELIVERY -> ROOT-ZONE -> UPTAKE -> ALLOCATION -> OUTCOME
--
-- Each arrow is an explicit receipt; plant-available N in the delivery packet
-- is not silently promoted to root uptake, biomass, fruit, yield or soil return.
------------------------------------------------------------------------

data NitrogenTransitionCoordinate : Set where
  deliveredPlantAvailableNitrogen
  rootZoneAvailableNitrogen
  plantNitrogenUptake
  plantNitrogenAllocation
  vegetativeBiomassOutcome
  reproductiveOrFruitOutcome
  soilReturnNitrogen : NitrogenTransitionCoordinate

record NitrogenSPACTransitionWeld : Set₁ where
  constructor nitrogen-spac-transition-weld
  field
    packet : Nitrogen.NitrogenDeliveryPacket
    spacDomain : SPAC.SPACDomainRealization
    deliveredNToRootZoneReference : String
    rootZoneAvailabilityReference : String
    rootUptakeMeasurementOrModelReference : String
    uptakeToAllocationReference : String
    allocationToBiomassReference : String
    allocationToFruitOrReproductionReference : String
    plantToSoilReturnReference : String
    sameSpatialBoundaryReference : String
    sameTemporalBoundaryReference : String
    crossDomainConservationReference : String
    uncertaintyReference : String

open NitrogenSPACTransitionWeld public

record NitrogenLESStateTransition
    (weld : NitrogenSPACTransitionWeld) : Set₁ where
  constructor nitrogen-les-state-transition
  field
    before : LES.SituatedObservation
    after : LES.SituatedObservation
    interventionIdentity : Causal.SituatedInterventionIdentity
    packetMatchesInterventionReference : String
    beforeStateReference : String
    afterStateReference : String
    transitionModelReference : String
    observedOutcomeReference : String

open NitrogenLESStateTransition public

record NitrogenCausalTransitionBinding
    {weld : NitrogenSPACTransitionWeld}
    (transition : NitrogenLESStateTransition weld) : Set₂ where
  constructor nitrogen-causal-transition-binding
  field
    estimand : Estimand.CausalEffectEstimand
    interventionMatchesEstimandReference : String
    comparatorReference : String
    populationReference : String
    outcomeReference : String
    horizonReference : String
    assignmentOrIdentificationReference : String
    sourceDataProvenanceReference : String
    sameSystemBoundaryReference : String

open NitrogenCausalTransitionBinding public

------------------------------------------------------------------------
-- WrongType barriers.
------------------------------------------------------------------------

data PlantAvailableMeansRootZoneAvailablePermission : Set where
data RootZoneAvailableMeansUptakePermission : Set where
data UptakeMeansAllocationPermission : Set where
data AllocationMeansYieldPermission : Set where
data BiomassMeansFruitInvestmentPermission : Set where
data PlantNitrogenMeansSoilReturnPermission : Set where
data ObservedTransitionMeansCausalEffectPermission : Set where
data SameDeliveredNMeansSameTrajectoryPermission : Set where

plantAvailableDoesNotDefinitionallyMeanRootZoneAvailable : PlantAvailableMeansRootZoneAvailablePermission → ⊥
plantAvailableDoesNotDefinitionallyMeanRootZoneAvailable ()
rootZoneAvailabilityDoesNotProveUptake : RootZoneAvailableMeansUptakePermission → ⊥
rootZoneAvailabilityDoesNotProveUptake ()
uptakeDoesNotDetermineAllocation : UptakeMeansAllocationPermission → ⊥
uptakeDoesNotDetermineAllocation ()
allocationDoesNotDefinitionallyMeanYield : AllocationMeansYieldPermission → ⊥
allocationDoesNotDefinitionallyMeanYield ()
biomassDoesNotDetermineFruitInvestment : BiomassMeansFruitInvestmentPermission → ⊥
biomassDoesNotDetermineFruitInvestment ()
plantNitrogenDoesNotDetermineSoilReturn : PlantNitrogenMeansSoilReturnPermission → ⊥
plantNitrogenDoesNotDetermineSoilReturn ()
observedTransitionDoesNotIdentifyCausalEffect : ObservedTransitionMeansCausalEffectPermission → ⊥
observedTransitionDoesNotIdentifyCausalEffect ()
sameDeliveredNitrogenDoesNotFixTrajectory : SameDeliveredNMeansSameTrajectoryPermission → ⊥
sameDeliveredNitrogenDoesNotFixTrajectory ()

record NitrogenLESTransitionBoundary : Set where
  constructor nitrogen-les-transition-boundary
  field
    packetUptakeAllocationAndOutcomeRemainDistinct : Bool
    spacHydrologyBiogeochemistryRemainAuthoritative : Bool
    situatedHistoryAndBoundaryRemainFirstClass : Bool
    observedTransitionAndCausalEstimandRemainDistinct : Bool
    sameDeliveredNitrogenAutomaticallyMeansSamePlantTrajectory : Bool

canonicalNitrogenLESTransitionBoundary : NitrogenLESTransitionBoundary
canonicalNitrogenLESTransitionBoundary =
  nitrogen-les-transition-boundary true true true true false
