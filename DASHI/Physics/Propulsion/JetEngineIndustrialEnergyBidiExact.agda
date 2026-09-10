module DASHI.Physics.Propulsion.JetEngineIndustrialEnergyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Propulsion.JetEngineFlowArchitectureExact as Jet
import DASHI.Physics.Nuclear.LeBlancFissionSurfacePowerICBidiExact as FSP
import DASHI.Planning.DataCentreUrbanResourceConflictExact as DataCentre
import DASHI.Economics.TSMCHBMManufacturingDemandPolicy2026Exact as TSMC
import DASHI.Biology.DeepTimeCarbonBiosphereFossilFuelBidiExact as Fossil

------------------------------------------------------------------------
-- INDUSTRIAL-ENERGY BIDI BRIDGE
--
-- The point is not to identify jet engines, AI datacentres, semiconductor fabs
-- and nuclear surface-power systems.  They remain distinct systems.  The bridge
-- exposes shared dependency coordinates so demand, manufacturing, energy,
-- operation and climate claims can be routed to the exact producer that owns
-- them.
------------------------------------------------------------------------

data IndustrialDomain : Set where
  aviationJetEngine : IndustrialDomain
  aiDatacentre : IndustrialDomain
  semiconductorManufacturing : IndustrialDomain
  fissionSurfacePower : IndustrialDomain

data IndustrialCoordinate : Set where
  serviceDemand : IndustrialCoordinate
  installedCapital : IndustrialCoordinate
  materialInput : IndustrialCoordinate
  manufacturingCapacity : IndustrialCoordinate
  electricityInput : IndustrialCoordinate
  fuelInput : IndustrialCoordinate
  waterInput : IndustrialCoordinate
  thermalWaste : IndustrialCoordinate
  usefulOutput : IndustrialCoordinate
  directEmissions : IndustrialCoordinate
  upstreamEmissions : IndustrialCoordinate
  atmosphericForcing : IndustrialCoordinate
  policyConstraint : IndustrialCoordinate

record IndustrialSystemObservation : Set where
  constructor industrial-system-observation
  field
    domain : IndustrialDomain
    coordinate : IndustrialCoordinate
    sourceObject : String
    sameObjectBound : Bool
    empirical : Bool

open IndustrialSystemObservation public

------------------------------------------------------------------------
-- Existing-repo anchors.
------------------------------------------------------------------------

fspRotatingMachineRegion : FSP.FSPSystemRegion
fspRotatingMachineRegion = FSP.turbineCompressor

dataCentreProject : DataCentre.Project
dataCentreProject = DataCentre.aiDataCentre

dataCentreElectricityDemand :
  DataCentre.Demand DataCentre.aiDataCentre DataCentre.electricity
dataCentreElectricityDemand = tt

dataCentreWaterDemand :
  DataCentre.Demand DataCentre.aiDataCentre DataCentre.water
dataCentreWaterDemand = tt

tsmcManufacturingSource : TSMC.SourceReceipt
tsmcManufacturingSource = TSMC.tsmcCapacityPlanning

fossilCarbonBoundary : Fossil.DeepTimeCarbonBiosphereFossilFuelBoundary
fossilCarbonBoundary = Fossil.canonicalDeepTimeCarbonBiosphereFossilFuelBoundary

------------------------------------------------------------------------
-- Shared rotating-machinery seam.
--
-- FSP already owns a turbine/compressor region and sensor axes for pressure,
-- temperature, mass flow, speed and vibration.  A jet engine can reuse the
-- observation/qualification pattern, but not the nuclear heat-source claim.
------------------------------------------------------------------------

record RotatingMachineObservationBridge : Set where
  constructor rotating-machine-observation-bridge
  field
    jetComponent : Jet.EngineComponent
    fspRegion : FSP.FSPSystemRegion
    pressureObservableShared : Bool
    temperatureObservableShared : Bool
    massFlowObservableShared : Bool
    speedObservableShared : Bool
    vibrationObservableShared : Bool
    heatSourceIdentityClaimed : Bool

open RotatingMachineObservationBridge public

canonicalRotatingMachineBridge : RotatingMachineObservationBridge
canonicalRotatingMachineBridge =
  rotating-machine-observation-bridge
    Jet.compressor
    FSP.turbineCompressor
    true true true true true false

------------------------------------------------------------------------
-- Aviation fuel / fossil-carbon boundary.
------------------------------------------------------------------------

data FuelPathway : Set where
  petroleumDerivedFuel : FuelPathway
  syntheticHydrocarbonFuel : FuelPathway
  bioDerivedDropInFuel : FuelPathway
  hydrogenFuel : FuelPathway

record AviationFuelLifecycleReceipt : Set where
  constructor aviation-fuel-lifecycle-receipt
  field
    pathway : FuelPathway
    extractionOrFeedstockCode : Nat
    processingCode : Nat
    transportCode : Nat
    combustionCode : Nat
    upstreamCarbonCode : Nat
    combustionCarbonCode : Nat
    lifecycleBoundaryChecked : Bool

record AviationClimateVector : Set where
  constructor aviation-climate-vector
  field
    carbonDioxideCode : Nat
    nitrogenOxidesCode : Nat
    waterVapourCode : Nat
    contrailCirrusCode : Nat
    aerosolCode : Nat
    altitudeBandCode : Nat
    timeHorizonCode : Nat

------------------------------------------------------------------------
-- Common demand -> capital -> resources -> operation -> impact carrier.
------------------------------------------------------------------------

record IndustrialDemandChain : Set where
  constructor industrial-demand-chain
  field
    domain : IndustrialDomain
    demandCode : Nat
    installedCapacityCode : Nat
    materialRequirementCode : Nat
    energyRequirementCode : Nat
    waterRequirementCode : Nat
    usefulServiceCode : Nat
    emissionsCode : Nat
    climateForcingCode : Nat
    sameScenario : Bool

open IndustrialDemandChain public

------------------------------------------------------------------------
-- WrongType firewalls shared by aviation and AI infrastructure.
------------------------------------------------------------------------

data ComponentEfficiencyImpliesAbsoluteResourceDeclinePermission : Set where

data LowerOperatingEnergyImpliesLowerLifecycleImpactPermission : Set where

data TailpipeCarbonImpliesLifecycleClimateImpactPermission : Set where

data EmissionsInventoryImpliesClimateForcingPermission : Set where

data ManufacturingDemandImpliesPermanentChokepointPermission : Set where

data SharedResourceCoordinateImpliesSystemIdentityPermission : Set where

data TurbineCompressorRegionImpliesSameHeatSourcePermission : Set where

componentEfficiencyDoesNotProveAbsoluteResourceDecline :
  ComponentEfficiencyImpliesAbsoluteResourceDeclinePermission → ⊥
componentEfficiencyDoesNotProveAbsoluteResourceDecline ()

lowerOperatingEnergyDoesNotProveLowerLifecycleImpact :
  LowerOperatingEnergyImpliesLowerLifecycleImpactPermission → ⊥
lowerOperatingEnergyDoesNotProveLowerLifecycleImpact ()

tailpipeCarbonDoesNotEqualLifecycleClimateImpact :
  TailpipeCarbonImpliesLifecycleClimateImpactPermission → ⊥
tailpipeCarbonDoesNotEqualLifecycleClimateImpact ()

emissionsInventoryDoesNotAutoPromoteToClimateForcing :
  EmissionsInventoryImpliesClimateForcingPermission → ⊥
emissionsInventoryDoesNotAutoPromoteToClimateForcing ()

manufacturingDemandDoesNotAutoPromoteToPermanentChokepoint :
  ManufacturingDemandImpliesPermanentChokepointPermission → ⊥
manufacturingDemandDoesNotAutoPromoteToPermanentChokepoint ()

sharedResourceCoordinatesDoNotIdentifySystems :
  SharedResourceCoordinateImpliesSystemIdentityPermission → ⊥
sharedResourceCoordinatesDoNotIdentifySystems ()

sharedTurbomachineryDoesNotIdentifyHeatSource :
  TurbineCompressorRegionImpliesSameHeatSourcePermission → ⊥
sharedTurbomachineryDoesNotIdentifyHeatSource ()

------------------------------------------------------------------------
-- Reverse acquisition targets for the cross-domain claims.
------------------------------------------------------------------------

data IndustrialReverseTarget : Set where
  acquireEngineStationData : IndustrialReverseTarget
  acquireMissionFuelBurn : IndustrialReverseTarget
  acquireFuelLifecycleInventory : IndustrialReverseTarget
  acquireAviationNonCO2ForcingModel : IndustrialReverseTarget
  acquireDatacentreElectricityUse : IndustrialReverseTarget
  acquireDatacentreWaterUse : IndustrialReverseTarget
  acquireGridGenerationMix : IndustrialReverseTarget
  acquireFabCapacityReceipt : IndustrialReverseTarget
  acquireSemiconductorProcessEnergy : IndustrialReverseTarget
  acquireCapitalDeploymentReceipt : IndustrialReverseTarget
  acquireDemandScenario : IndustrialReverseTarget
  acquireClimateForcingModel : IndustrialReverseTarget

record IndustrialReverseObligation : Set where
  constructor industrial-reverse-obligation
  field
    target : IndustrialReverseTarget
    preferredEvidence : String
    promotes : String
    cannotPromote : String

open IndustrialReverseObligation public

jetFuelBurnObligation : IndustrialReverseObligation
jetFuelBurnObligation =
  industrial-reverse-obligation
    acquireMissionFuelBurn
    "same-aircraft mission profile plus engine/aircraft fuel-burn observation or validated performance model"
    "mission-bounded aviation fuel demand"
    "rated engine efficiency alone"

dataCentreEnergyObligation : IndustrialReverseObligation
dataCentreEnergyObligation =
  industrial-reverse-obligation
    acquireDatacentreElectricityUse
    "metered or source-bound facility electricity demand for the same site/time window"
    "datacentre operational electricity demand"
    "GPU nameplate power or chip shipment count alone"

tsmcProcessEnergyObligation : IndustrialReverseObligation
tsmcProcessEnergyObligation =
  industrial-reverse-obligation
    acquireSemiconductorProcessEnergy
    "fab/process-specific energy inventory bound to the manufacturing stage under analysis"
    "semiconductor manufacturing energy demand"
    "TSMC capacity-planning statements alone"

climateForcingObligation : IndustrialReverseObligation
climateForcingObligation =
  industrial-reverse-obligation
    acquireClimateForcingModel
    "source-bound atmospheric/climate model matched to the emitted species, altitude, geography and time horizon"
    "climate-forcing claim"
    "emissions inventory alone"
