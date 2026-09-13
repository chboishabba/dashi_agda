module DASHI.Environment.HolzerPassiveStorageEnergyServiceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ScientificWorkAttributionExact as Attribution
import DASHI.Environment.HolzerKrameterhofSourceAttributionExact as HolzerSources
import DASHI.Environment.HolzerKrameterhofIntegratedLandscapeBridgeExact as Holzer
import DASHI.Environment.HolzerKrameterhofAdjacentSOTASourceRegistryExact as SOTA
import DASHI.Environment.PermacultureEmbodiedEnergyLandscapeBridgeExact as PermacultureEnergy
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- PASSIVE EARTH-CELLAR STORAGE <-> POWERED REFRIGERATION
--
-- The supplied Krameterhof tour provides a practitioner report of an
-- underground-air / earth-coupled storage arrangement.  Adjacent engineering
-- literature supplies mechanism analogues.  DASHI owns the matched-service and
-- lifecycle comparison below.  Neither source class supplies a Krameterhof
-- energy-saving theorem.
------------------------------------------------------------------------

data StorageArchitecture : Set where
  earthCoupledPassiveCellar
  mechanicallyRefrigeratedStore
  hybridPassiveMechanicalStore : StorageArchitecture

data StorageServiceCoordinate : Set where
  productTemperature
  relativeHumidity
  airExchange
  condensationControl
  mouldControl
  productMassRetained
  storageDuration
  productQuality : StorageServiceCoordinate

record StorageServiceDemand : Set where
  constructor storage-service-demand
  field
    commodityReference : String
    initialProductStateReference : String
    targetTemperatureBandReference : String
    targetHumidityBandReference : String
    minimumVentilationReference : String
    storageDurationReference : String
    acceptableMassLossReference : String
    acceptableQualityLossReference : String
    safetyReference : String

open StorageServiceDemand public

record StorageSystemIdentity : Set where
  constructor storage-system-identity
  field
    architecture : StorageArchitecture
    siteClimateReference : String
    constructionReference : String
    groundCouplingReference : String
    ventilationReference : String
    moistureControlReference : String
    controlsReference : String
    maintenanceReference : String

open StorageSystemIdentity public

record StorageEnergyLedger
    (system : StorageSystemIdentity)
    (demand : StorageServiceDemand) : Set where
  constructor storage-energy-ledger
  field
    embodiedConstructionEnergy : SI.Quantity SI.Energy SI.unitScale
    operatingElectricalEnergy : SI.Quantity SI.Energy SI.unitScale
    maintenanceEnergyReference : String
    replacementEnergyReference : String
    constructionLifetimeReference : String
    allocationAcrossServiceLifeReference : String
    productLossEnergyOrResourceReference : String
    measurementOrModelReference : String
    uncertaintyReference : String

open StorageEnergyLedger public

record StorageServicePerformance
    (system : StorageSystemIdentity)
    (demand : StorageServiceDemand) : Set where
  constructor storage-service-performance
  field
    temperaturePerformanceReference : String
    humidityPerformanceReference : String
    ventilationPerformanceReference : String
    condensationPerformanceReference : String
    mouldSafetyReference : String
    productMassRetentionReference : String
    productQualityReference : String
    serviceDemandMetReference : String

open StorageServicePerformance public

record MatchedStorageEnergyComparison : Set where
  constructor matched-storage-energy-comparison
  field
    demand : StorageServiceDemand
    passiveSystem : StorageSystemIdentity
    poweredSystem : StorageSystemIdentity
    passiveEnergy : StorageEnergyLedger passiveSystem demand
    poweredEnergy : StorageEnergyLedger poweredSystem demand
    passivePerformance : StorageServicePerformance passiveSystem demand
    poweredPerformance : StorageServicePerformance poweredSystem demand
    sameCommodityReference : String
    sameClimateOrNormalisationReference : String
    sameServiceBoundaryReference : String
    sameLifetimeOrAnnualisationReference : String
    embodiedEnergyAccountingReference : String
    operatingEnergyAccountingReference : String
    productLossAccountingReference : String
    comparisonResultReference : String
    dashiInferenceOwner : Attribution.ClaimOwner
    comparisonOwnedByDashi :
      dashiInferenceOwner ≡ Attribution.dashiInferenceOwner

open MatchedStorageEnergyComparison public

------------------------------------------------------------------------
-- Krameterhof source admission.
------------------------------------------------------------------------

record KrameterhofPassiveStorageAdmission : Set where
  constructor krameterhof-passive-storage-admission
  field
    practice : Holzer.SituatedKrameterhofPractice
    practitionerSource : HolzerSources.KrameterhofSource
    practiceIsPassiveEarthCellarReference : String
    reportedUndergroundAirIntakeReference : String
    reportedCoolingReference : String
    reportedCondensationReference : String
    directEnergyMeasurementAvailable : Bool
    directProductSafetyMeasurementAvailable : Bool

open KrameterhofPassiveStorageAdmission public

record PassiveStorageAdjacentEvidenceAdmission : Set where
  constructor passive-storage-adjacent-evidence-admission
  field
    source : SOTA.AdjacentSOTASource
    sharedGroundThermalMechanismReference : String
    sharedVentilationMechanismReference : String
    commodityMatchReference : String
    climateMatchReference : String
    geometryMatchReference : String
    directKrameterhofMeasurement : Bool
    sourceOwner : Attribution.ClaimOwner
    sourceRemainsExternallyOwned :
      sourceOwner ≡ Attribution.externalSourceOwner

open PassiveStorageAdjacentEvidenceAdmission public

------------------------------------------------------------------------
-- Permaculture embodied-energy cross-pollination.
------------------------------------------------------------------------

record PassiveStoragePermacultureEnergyWeld : Set where
  constructor passive-storage-permaculture-energy-weld
  field
    landscapeCapacity : PermacultureEnergy.LandscapeStoredCapacity
    storageSystem : StorageSystemIdentity
    physicalEnergyCoordinateReference : String
    embodiedConstructionReference : String
    retainedFoodResourceReference : String
    waterMoistureReference : String
    samePhysicalEnergyIsNotSameNaturalCapital : Bool

open PassiveStoragePermacultureEnergyWeld public

------------------------------------------------------------------------
-- WrongType / attribution barriers.
------------------------------------------------------------------------

data PassiveMeansZeroEnergyPermission : Set where
data NoCompressorMeansLowerLifecycleEnergyPermission : Set where
data LowerOperatingEnergyMeansLowerTotalCostPermission : Set where
data EarthCouplingMeansSafeHumidityPermission : Set where
data LowerTemperatureMeansLowerFoodLossPermission : Set where
data AdjacentEngineeringStudyMeansKrameterhofPerformancePermission : Set where
data PractitionerDescriptionMeansMeasuredEnergySavingPermission : Set where
data SameTemperatureMeansSameStorageServicePermission : Set where

passiveDoesNotMeanZeroEnergy : PassiveMeansZeroEnergyPermission → ⊥
passiveDoesNotMeanZeroEnergy ()

noCompressorDoesNotProveLowerLifecycleEnergy :
  NoCompressorMeansLowerLifecycleEnergyPermission → ⊥
noCompressorDoesNotProveLowerLifecycleEnergy ()

lowerOperatingEnergyDoesNotProveLowerTotalCost :
  LowerOperatingEnergyMeansLowerTotalCostPermission → ⊥
lowerOperatingEnergyDoesNotProveLowerTotalCost ()

earthCouplingDoesNotProveSafeHumidity : EarthCouplingMeansSafeHumidityPermission → ⊥
earthCouplingDoesNotProveSafeHumidity ()

lowerTemperatureDoesNotProveLowerFoodLoss : LowerTemperatureMeansLowerFoodLossPermission → ⊥
lowerTemperatureDoesNotProveLowerFoodLoss ()

adjacentStudyDoesNotPayKrameterhofPerformance :
  AdjacentEngineeringStudyMeansKrameterhofPerformancePermission → ⊥
adjacentStudyDoesNotPayKrameterhofPerformance ()

practitionerDescriptionDoesNotPayEnergySaving :
  PractitionerDescriptionMeansMeasuredEnergySavingPermission → ⊥
practitionerDescriptionDoesNotPayEnergySaving ()

sameTemperatureDoesNotIdentifySameStorageService :
  SameTemperatureMeansSameStorageServicePermission → ⊥
sameTemperatureDoesNotIdentifySameStorageService ()

record PassiveStorageBoundary : Set where
  constructor passive-storage-boundary
  field
    embodiedAndOperatingEnergyRemainDistinct : Bool
    temperatureHumidityVentilationAndFoodLossRemainDistinct : Bool
    matchedServiceRequiredForEnergyComparison : Bool
    practitionerReportAndEnergyMeasurementRemainDistinct : Bool
    adjacentEngineeringEvidenceAndSitePerformanceRemainDistinct : Bool
    dashiLifecycleComparisonRemainsDashiOwned : Bool
    passiveAutomaticallyMeansLowerLifecycleEnergy : Bool

canonicalPassiveStorageBoundary : PassiveStorageBoundary
canonicalPassiveStorageBoundary =
  passive-storage-boundary true true true true true true false
