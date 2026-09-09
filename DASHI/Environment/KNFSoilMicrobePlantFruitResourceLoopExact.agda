module DASHI.Environment.KNFSoilMicrobePlantFruitResourceLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.KoreanNaturalFarmingExact as KNF
import DASHI.Environment.SoilBiogeochemistryProcessNetworkExact as Soil
import DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact as Root
import DASHI.Biology.FruitEmbodiedEnergyHistoryFibreExact as FruitEnergy
import DASHI.Biology.FruitBoundaryResourcePaidRepairExact as FruitRepair

------------------------------------------------------------------------
-- KNF -> SOIL -> ROOT -> PLANT -> FRUIT RESOURCE LOOP
--
-- This owner closes only the structural chain. Each arrow remains an explicit
-- application-supplied receipt. In particular, KNF application does not by
-- itself prove soil-process change; soil-process change does not by itself
-- prove plant uptake; and uptake does not by itself prove greater fruit energy,
-- repair capacity, yield or fitness.
------------------------------------------------------------------------

data SoilMicrobialResponse : Set where
  microbialResponseUnresolved
  microbialCommunityChanged
  microbialCommunityUnchanged : SoilMicrobialResponse

data SoilNutrientResponse : Set where
  nutrientResponseUnresolved
  nutrientAvailabilityChanged
  nutrientAvailabilityUnchanged : SoilNutrientResponse

data PlantAcquisitionResponse : Set where
  acquisitionUnresolved
  rootAcquisitionChanged
  rootAcquisitionUnchanged : PlantAcquisitionResponse

data PlantAllocationResponse : Set where
  allocationUnresolved
  fruitAllocationChanged
  fruitAllocationUnchanged : PlantAllocationResponse

data FruitResourceResponse : Set where
  fruitResourceUnresolved
  fruitInvestmentChanged
  fruitRepairPoolChanged
  fruitResourceUnchanged : FruitResourceResponse

------------------------------------------------------------------------
-- Practice-to-soil adapter.
------------------------------------------------------------------------

record KNFSoilProcessPerturbation
    (soil : Soil.SoilCNProcessNetwork) : Set₁ where
  constructor knf-soil-process-perturbation
  field
    application : KNF.KNFApplication
    applicationTargetsSoilOrRootZone : Bool
    soilNetwork : Soil.SoilCNProcessNetwork
    sameSoilNetwork : soilNetwork ≡ soil
    microbialResponse : SoilMicrobialResponse
    nutrientResponse : SoilNutrientResponse
    applicationToMicrobialStateReference : String
    applicationToCNProcessReference : String
    moistureTemperatureContextReference : String
    evidenceReference : String

open KNFSoilProcessPerturbation public

------------------------------------------------------------------------
-- Soil-to-root bridge reuses the existing root/fungal physiology owner.
------------------------------------------------------------------------

record SoilToPlantAcquisitionBridge
    {soil : Soil.SoilCNProcessNetwork}
    (perturbation : KNFSoilProcessPerturbation soil) : Set₁ where
  constructor soil-to-plant-acquisition-bridge
  field
    biogeochemistryWeld : Soil.SoilPlantFungalBiogeochemistryWeld soil
    rootMechanism : Root.RootSoilIonWaterMechanism
    sameRootMechanism :
      Soil.rootSoilMechanism biogeochemistryWeld ≡ rootMechanism
    acquisitionResponse : PlantAcquisitionResponse
    nutrientSpeciesIdentificationReference : String
    waterStateSynchronizationReference : String
    rootDemandReference : String
    uptakeEvidenceReference : String

open SoilToPlantAcquisitionBridge public

------------------------------------------------------------------------
-- Root acquisition to plant allocation remains a separate physiological seam.
------------------------------------------------------------------------

record PlantResourceAllocationBridge
    {soil : Soil.SoilCNProcessNetwork}
    {perturbation : KNFSoilProcessPerturbation soil}
    (acquisition : SoilToPlantAcquisitionBridge perturbation) : Set where
  constructor plant-resource-allocation-bridge
  field
    allocationResponse : PlantAllocationResponse
    sourceSinkAllocationReference : String
    photosynthateCarbonReference : String
    mineralNutrientAllocationReference : String
    waterStatusAllocationReference : String
    developmentalStageReference : String
    allocationEvidenceReference : String

open PlantResourceAllocationBridge public

------------------------------------------------------------------------
-- Plant allocation to fruit embodied investment / repair pool.
------------------------------------------------------------------------

record PlantToFruitResourceBridge
    {soil : Soil.SoilCNProcessNetwork}
    {perturbation : KNFSoilProcessPerturbation soil}
    {acquisition : SoilToPlantAcquisitionBridge perturbation}
    (allocation : PlantResourceAllocationBridge acquisition) : Set where
  constructor plant-to-fruit-resource-bridge
  field
    fruitHistory : FruitEnergy.PlantPartHistory
    fruitEmbodiedEnergy : FruitEnergy.EmbodiedEnergy
    sameFruitEnergy :
      FruitEnergy.embodiedEnergy fruitHistory ≡ fruitEmbodiedEnergy
    fruitResourceResponse : FruitResourceResponse
    fruitConstructionReference : String
    fruitMaintenanceReference : String
    repairPoolReference : String
    fruitEvidenceReference : String

open PlantToFruitResourceBridge public

------------------------------------------------------------------------
-- Full resource loop receipt.
------------------------------------------------------------------------

record KNFSoilPlantFruitLoopReceipt : Set₁ where
  constructor knf-soil-plant-fruit-loop-receipt
  field
    soil : Soil.SoilCNProcessNetwork
    knfPerturbation : KNFSoilProcessPerturbation soil
    acquisition : SoilToPlantAcquisitionBridge knfPerturbation
    allocation : PlantResourceAllocationBridge acquisition
    fruitBridge : PlantToFruitResourceBridge allocation

    resourcePaidRepair : FruitRepair.ResourcePaidSkinRepair
    fruitBridgeToRepairReference : String

    applicationContextMatched : Bool
    soilResponseMeasured : Bool
    uptakeResponseMeasured : Bool
    allocationResponseMeasured : Bool
    fruitResponseMeasured : Bool

open KNFSoilPlantFruitLoopReceipt public

------------------------------------------------------------------------
-- Explicit no-shortcut boundaries.
------------------------------------------------------------------------

data KNFApplicationMeansMicrobiomeChangePermission : Set where

data MicrobiomeChangeMeansNutrientIncreasePermission : Set where

data NutrientChangeMeansRootUptakeIncreasePermission : Set where

data RootUptakeMeansFruitInvestmentIncreasePermission : Set where

data FruitInvestmentMeansRepairSuccessPermission : Set where

data FruitInvestmentMeansFitnessIncreasePermission : Set where

data IMOEqualsMycorrhizaPermission : Set where

knfApplicationDoesNotByItselfProveMicrobiomeChange :
  KNFApplicationMeansMicrobiomeChangePermission → ⊥
knfApplicationDoesNotByItselfProveMicrobiomeChange ()

microbiomeChangeDoesNotByItselfProveNutrientIncrease :
  MicrobiomeChangeMeansNutrientIncreasePermission → ⊥
microbiomeChangeDoesNotByItselfProveNutrientIncrease ()

nutrientChangeDoesNotByItselfProveRootUptakeIncrease :
  NutrientChangeMeansRootUptakeIncreasePermission → ⊥
nutrientChangeDoesNotByItselfProveRootUptakeIncrease ()

rootUptakeDoesNotByItselfProveFruitInvestmentIncrease :
  RootUptakeMeansFruitInvestmentIncreasePermission → ⊥
rootUptakeDoesNotByItselfProveFruitInvestmentIncrease ()

fruitInvestmentDoesNotByItselfProveRepairSuccess :
  FruitInvestmentMeansRepairSuccessPermission → ⊥
fruitInvestmentDoesNotByItselfProveRepairSuccess ()

fruitInvestmentDoesNotByItselfProveFitnessIncrease :
  FruitInvestmentMeansFitnessIncreasePermission → ⊥
fruitInvestmentDoesNotByItselfProveFitnessIncrease ()

imoIsNotPromotedToMycorrhizalIdentity : IMOEqualsMycorrhizaPermission → ⊥
imoIsNotPromotedToMycorrhizalIdentity ()

------------------------------------------------------------------------
-- Consumer-relative observation boundary.
------------------------------------------------------------------------

record SoilPlantFruitObservationPacket : Set where
  constructor soil-plant-fruit-observation-packet
  field
    microbialObservation : SoilMicrobialResponse
    nutrientObservation : SoilNutrientResponse
    acquisitionObservation : PlantAcquisitionResponse
    allocationObservation : PlantAllocationResponse
    fruitObservation : FruitResourceResponse
    siteContextReference : String
    timeReference : String
    methodReference : String

open SoilPlantFruitObservationPacket public

record KNFSoilPlantFruitBoundary : Set where
  constructor knf-soil-plant-fruit-boundary
  field
    knfPracticeIsDistinctFromSoilMechanism : Bool
    soilMechanismIsDistinctFromRootUptake : Bool
    rootUptakeIsDistinctFromPlantAllocation : Bool
    plantAllocationIsDistinctFromFruitInvestment : Bool
    fruitInvestmentIsDistinctFromRepairOutcome : Bool
    imoIsDistinctFromMycorrhizalPathway : Bool
    everyCrossDomainArrowNeedsEvidenceOrSameObjectReceipt : Bool

canonicalKNFSoilPlantFruitBoundary : KNFSoilPlantFruitBoundary
canonicalKNFSoilPlantFruitBoundary =
  knf-soil-plant-fruit-boundary
    true true true true true true true
