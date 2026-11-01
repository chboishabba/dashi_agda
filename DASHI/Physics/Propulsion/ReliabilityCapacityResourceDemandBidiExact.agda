{-# OPTIONS --safe #-}
module DASHI.Physics.Propulsion.ReliabilityCapacityResourceDemandBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Planning.CorkySoftOperationalPatternAtlasExact as Corky
import DASHI.Physics.Propulsion.QualifiedHotSectionManufacturingBidiExact as Qual
import DASHI.Physics.Propulsion.CorkySoftManufacturingMissionOperationsBidiExact as Ops
import DASHI.Physics.Propulsion.JetEngineCanonicalMissionEnergyBidiExact as Mission
import DASHI.Physics.Propulsion.JetEngineIndustrialEnergyBidiExact as Industrial
import DASHI.Economics.ManufacturingScarcityTimescaleExact as Scarcity
import DASHI.Economics.TSMCHBMManufacturingDemandPolicy2026Exact as TSMC

------------------------------------------------------------------------
-- RELIABILITY -> QUALIFIED AVAILABLE CAPACITY -> SERVICE/RESOURCE DEMAND
--
-- This owner composes the operational grammar learned from CorkySoft with the
-- existing jet/TSMC/AI carriers.  The canonical seam is not "defect implies
-- shortage".  A defect/reliability observation first changes the population of
-- qualified, physically available units.  Capacity, allocation, realised
-- service, and resource demand remain separately paid coordinates.
------------------------------------------------------------------------

data CapacityDomain : Set where
  aviationFleet : CapacityDomain
  semiconductorSupply : CapacityDomain
  aiDatacentreFleet : CapacityDomain

record PopulationIdentity : Set where
  constructor population-identity
  field
    domain : CapacityDomain
    populationReference : String
    revisionOrTimeWindow : String
    evidenceReference : String

open PopulationIdentity public

data CapacityLossCause : Set where
  manufacturingDefect : CapacityLossCause
  inspectionReject : CapacityLossCause
  maintenanceRemoval : CapacityLossCause
  quarantine : CapacityLossCause
  supplyShortage : CapacityLossCause
  installationUnavailable : CapacityLossCause
  infrastructureConstraint : CapacityLossCause
  otherLoss : CapacityLossCause

record ReliabilityObservation : Set where
  constructor reliability-observation
  field
    population : PopulationIdentity
    cause : CapacityLossCause
    observedUnitsCode : Nat
    affectedUnitsCode : Nat
    observationSource : String
    samePopulation : Bool
    samePopulationIsTrue : samePopulation ≡ true

open ReliabilityObservation public

------------------------------------------------------------------------
-- Canonical capacity carrier.
-- Gross produced/owned units are not the same as qualified available units.
------------------------------------------------------------------------

record QualifiedAvailableCapacity : Set where
  constructor qualified-available-capacity
  field
    population : PopulationIdentity
    grossUnitsCode : Nat
    qualifiedUnitsCode : Nat
    physicallyAvailableUnitsCode : Nat
    allocatedUnitsCode : Nat
    serviceableUnitsCode : Nat
    qualificationReference : String
    custodyAvailabilityReference : String
    samePopulationAcrossCounts : Bool
    samePopulationAcrossCountsIsTrue : samePopulationAcrossCounts ≡ true

open QualifiedAvailableCapacity public

record ReliabilityCapacityWeld : Set where
  constructor reliability-capacity-weld
  field
    observation : ReliabilityObservation
    capacity : QualifiedAvailableCapacity
    observationAffectsSamePopulation : Bool
    observationAffectsSamePopulationIsTrue :
      observationAffectsSamePopulation ≡ true
    effectRuleReference : String

open ReliabilityCapacityWeld public

------------------------------------------------------------------------
-- Demand/capacity comparison is a second payment.  A reliability event can
-- reduce availability without proving that demand exceeds the remaining
-- capacity.
------------------------------------------------------------------------

record DemandCapacityState : Set where
  constructor demand-capacity-state
  field
    capacity : QualifiedAvailableCapacity
    demandCode : Nat
    committedServiceCode : Nat
    shortageCode : Nat
    demandSource : String
    sameScenario : Bool
    sameScenarioIsTrue : sameScenario ≡ true

open DemandCapacityState public

data CapacityResponse : Set where
  noOperationalChange : CapacityResponse
  deferService : CapacityResponse
  approvedSubstitution : CapacityResponse
  useSpareCapacity : CapacityResponse
  subcontractOrExternalSupply : CapacityResponse
  replanNetwork : CapacityResponse
  reduceCommittedService : CapacityResponse

record GovernedCapacityResponse : Set where
  constructor governed-capacity-response
  field
    state : DemandCapacityState
    response : CapacityResponse
    decisionAuthority : String
    decisionEvidence : String
    substitutionOrReplanGoverned : Bool
    substitutionOrReplanGovernedIsTrue :
      substitutionOrReplanGoverned ≡ true

open GovernedCapacityResponse public

------------------------------------------------------------------------
-- Resource consequence comes only after realised execution.  This lets the
-- same grammar carry aviation fuel, semiconductor deployment, and datacentre
-- electricity/water without identifying those resources.
------------------------------------------------------------------------

data ResourceCoordinate : Set where
  aviationFuel : ResourceCoordinate
  aviationMaintenanceMaterial : ResourceCoordinate
  semiconductorQualifiedOutput : ResourceCoordinate
  semiconductorProcessEnergy : ResourceCoordinate
  datacentreElectricity : ResourceCoordinate
  datacentreWater : ResourceCoordinate
  datacentreInstalledCompute : ResourceCoordinate

record RealisedResourceDemand : Set where
  constructor realised-resource-demand
  field
    state : DemandCapacityState
    response : GovernedCapacityResponse
    coordinate : ResourceCoordinate
    realisedServiceCode : Nat
    realisedResourceCode : Nat
    executionReference : String
    sameScenarioExecution : Bool
    sameScenarioExecutionIsTrue : sameScenarioExecution ≡ true

open RealisedResourceDemand public

------------------------------------------------------------------------
-- Cross-domain structural bridge.
------------------------------------------------------------------------

data SharedCapacityCoordinate : Set where
  grossPopulation : SharedCapacityCoordinate
  qualifiedPopulation : SharedCapacityCoordinate
  physicallyAvailablePopulation : SharedCapacityCoordinate
  allocatedPopulation : SharedCapacityCoordinate
  serviceablePopulation : SharedCapacityCoordinate
  demandAgainstCapacity : SharedCapacityCoordinate
  governedSubstitutionOrReplan : SharedCapacityCoordinate
  realisedResourceUse : SharedCapacityCoordinate

record CrossDomainCapacityBridge : Set where
  constructor cross-domain-capacity-bridge
  field
    left : CapacityDomain
    right : CapacityDomain
    shared : List SharedCapacityCoordinate
    systemIdentityClaimed : Bool
    systemIdentityClaimedIsFalse : systemIdentityClaimed ≡ false

open CrossDomainCapacityBridge public

aviationSemiconductorCapacityBridge : CrossDomainCapacityBridge
aviationSemiconductorCapacityBridge =
  cross-domain-capacity-bridge aviationFleet semiconductorSupply
    (grossPopulation ∷ qualifiedPopulation ∷ physicallyAvailablePopulation ∷
     allocatedPopulation ∷ serviceablePopulation ∷ demandAgainstCapacity ∷
     governedSubstitutionOrReplan ∷ realisedResourceUse ∷ [])
    false refl

semiconductorDatacentreCapacityBridge : CrossDomainCapacityBridge
semiconductorDatacentreCapacityBridge =
  cross-domain-capacity-bridge semiconductorSupply aiDatacentreFleet
    (grossPopulation ∷ qualifiedPopulation ∷ physicallyAvailablePopulation ∷
     allocatedPopulation ∷ serviceablePopulation ∷ demandAgainstCapacity ∷
     governedSubstitutionOrReplan ∷ realisedResourceUse ∷ [])
    false refl

------------------------------------------------------------------------
-- Existing-owner anchors.
------------------------------------------------------------------------

corkySoftExecutionBoundary : Corky.CorkySoftOperationalPatternBoundary
corkySoftExecutionBoundary = Corky.canonicalCorkySoftOperationalPatternBoundary

operationsBoundary : Ops.CorkySoftManufacturingMissionOperationsBoundary
operationsBoundary = Ops.canonicalCorkySoftManufacturingMissionOperationsBoundary

qualificationBoundary : Qual.CanonicalQualificationBoundary
qualificationBoundary = Qual.canonicalQualificationBoundary

manufacturingFoundryStage : Scarcity.ManufacturingStage
manufacturingFoundryStage = Scarcity.foundry

advancedPackagingStage : Scarcity.ManufacturingStage
advancedPackagingStage = Scarcity.advancedPackaging

tsmcCapacityPlanningSource : TSMC.SourceReceipt
tsmcCapacityPlanningSource = TSMC.tsmcCapacityPlanning

aviationIndustrialDomain : Industrial.IndustrialDomain
aviationIndustrialDomain = Industrial.aviationJetEngine

aiIndustrialDomain : Industrial.IndustrialDomain
aiIndustrialDomain = Industrial.aiDatacentre

semiconductorIndustrialDomain : Industrial.IndustrialDomain
semiconductorIndustrialDomain = Industrial.semiconductorManufacturing

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data DefectObservationImpliesCapacityShortagePermission : Set where

data GrossUnitsImpliesQualifiedCapacityPermission : Set where

data QualifiedCapacityImpliesPhysicalAvailabilityPermission : Set where

data PhysicalAvailabilityImpliesAllocationPermission : Set where

data CapacityReductionImpliesDemandReductionPermission : Set where

data CapacityShortageImpliesPriceIncreasePermission : Set where

data SemiconductorShortageImpliesDatacentreResourceDemandPermission : Set where

data MissionRemovalImpliesFleetFuelReductionPermission : Set where

data OneLotYieldImpliesFabThroughputPermission : Set where

data LocalCapacityImpliesNetworkCapacityPermission : Set where

defectObservationDoesNotProveShortage :
  DefectObservationImpliesCapacityShortagePermission → ⊥
defectObservationDoesNotProveShortage ()

grossUnitsDoNotProveQualifiedCapacity :
  GrossUnitsImpliesQualifiedCapacityPermission → ⊥
grossUnitsDoNotProveQualifiedCapacity ()

qualificationDoesNotCreatePhysicalAvailability :
  QualifiedCapacityImpliesPhysicalAvailabilityPermission → ⊥
qualificationDoesNotCreatePhysicalAvailability ()

physicalAvailabilityDoesNotCreateAllocation :
  PhysicalAvailabilityImpliesAllocationPermission → ⊥
physicalAvailabilityDoesNotCreateAllocation ()

capacityReductionDoesNotCreateDemandReduction :
  CapacityReductionImpliesDemandReductionPermission → ⊥
capacityReductionDoesNotCreateDemandReduction ()

shortageDoesNotByItselfProvePriceIncrease :
  CapacityShortageImpliesPriceIncreasePermission → ⊥
shortageDoesNotByItselfProvePriceIncrease ()

semiconductorShortageDoesNotCreateDatacentreResourceDemand :
  SemiconductorShortageImpliesDatacentreResourceDemandPermission → ⊥
semiconductorShortageDoesNotCreateDatacentreResourceDemand ()

missionRemovalDoesNotByItselfProveFleetFuelReduction :
  MissionRemovalImpliesFleetFuelReductionPermission → ⊥
missionRemovalDoesNotByItselfProveFleetFuelReduction ()

oneLotYieldDoesNotProveFabThroughput :
  OneLotYieldImpliesFabThroughputPermission → ⊥
oneLotYieldDoesNotProveFabThroughput ()

localCapacityDoesNotProveNetworkCapacity :
  LocalCapacityImpliesNetworkCapacityPermission → ⊥
localCapacityDoesNotProveNetworkCapacity ()

------------------------------------------------------------------------
-- Reverse acquisition frontier.
------------------------------------------------------------------------

data ReliabilityCapacityReverseTarget : Set where
  acquirePopulationIdentity : ReliabilityCapacityReverseTarget
  acquireDefectRejectRemovalCounts : ReliabilityCapacityReverseTarget
  acquireQualifiedYieldOrServiceability : ReliabilityCapacityReverseTarget
  acquirePhysicalAvailabilityAndCustody : ReliabilityCapacityReverseTarget
  acquireAllocationState : ReliabilityCapacityReverseTarget
  acquireDemandSameWindow : ReliabilityCapacityReverseTarget
  acquireShortageOrSpareCapacity : ReliabilityCapacityReverseTarget
  acquireSubstitutionReplanDecision : ReliabilityCapacityReverseTarget
  acquireRealisedService : ReliabilityCapacityReverseTarget
  acquireRealisedResourceUse : ReliabilityCapacityReverseTarget
  acquireFleetMissionFuelResponse : ReliabilityCapacityReverseTarget
  acquireFabQualifiedOutput : ReliabilityCapacityReverseTarget
  acquireDatacentreDeploymentAndMetering : ReliabilityCapacityReverseTarget

record ReliabilityCapacityReverseObligation : Set where
  constructor reliability-capacity-reverse-obligation
  field
    target : ReliabilityCapacityReverseTarget
    preferredEvidence : String
    promotes : String
    cannotPromote : String

open ReliabilityCapacityReverseObligation public

record ReliabilityCapacityResourceBoundary : Set where
  constructor reliability-capacity-resource-boundary
  field
    defectDistinctFromShortage : Bool
    defectDistinctFromShortageIsTrue : defectDistinctFromShortage ≡ true
    qualificationDistinctFromAvailability : Bool
    qualificationDistinctFromAvailabilityIsTrue :
      qualificationDistinctFromAvailability ≡ true
    availabilityDistinctFromAllocation : Bool
    availabilityDistinctFromAllocationIsTrue :
      availabilityDistinctFromAllocation ≡ true
    capacityDistinctFromDemand : Bool
    capacityDistinctFromDemandIsTrue : capacityDistinctFromDemand ≡ true
    resourceDemandRequiresRealisedExecution : Bool
    resourceDemandRequiresRealisedExecutionIsTrue :
      resourceDemandRequiresRealisedExecution ≡ true

canonicalReliabilityCapacityResourceBoundary :
  ReliabilityCapacityResourceBoundary
canonicalReliabilityCapacityResourceBoundary =
  reliability-capacity-resource-boundary
    true refl true refl true refl true refl true refl
