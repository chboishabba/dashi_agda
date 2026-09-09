module DASHI.Environment.KNFPlantSoilReturnFlowLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Environment.SoilBiogeochemistryProcessNetworkExact as Soil
import DASHI.Environment.RootSoilFungalIonWaterPhysiologyExact as Root
import DASHI.Environment.KNFSoilMicrobePlantFruitResourceLoopExact as Forward

------------------------------------------------------------------------
-- PLANT -> SOIL RETURN FLOW
--
-- The forward KNF lane already owns soil -> root -> allocation -> fruit.
-- This module closes the opposite structural direction without asserting a
-- universal quantitative flux law.  Every return path needs an explicit
-- process / conservation / evidence weld into the existing soil C/N network.
------------------------------------------------------------------------

data PlantSoilReturnKind : Set where
  rootExudation
  rootTurnover
  leafLitter
  fruitResidue
  pruningResidue
  fungalCarbonTransfer : PlantSoilReturnKind

data ReturnFlowResponse : Set where
  returnFlowUnresolved
  returnFlowObserved
  returnFlowNotObserved : ReturnFlowResponse

data SoilReentryResponse : Set where
  soilReentryUnresolved
  soilPoolChanged
  soilPoolUnchanged : SoilReentryResponse

record PlantSoilReturnFlow
    (soil : Soil.SoilCNProcessNetwork) : Set₁ where
  constructor plant-soil-return-flow
  field
    kind : PlantSoilReturnKind
    response : ReturnFlowResponse
    soilNetwork : Soil.SoilCNProcessNetwork
    sameSoilNetwork : soilNetwork ≡ soil
    destinationPoolReference : String
    chemistryTransitionReference : String
    carbonBalanceReference : String
    nitrogenBalanceReference : String
    moistureTemperatureContextReference : String
    temporalSupportReference : String
    evidenceReference : String

open PlantSoilReturnFlow public

------------------------------------------------------------------------
-- Mycorrhizal return flow remains an explicit extension, not a synonym for
-- generic KNF microbial inoculation.
------------------------------------------------------------------------

record MycorrhizalPlantCarbonReturn
    {soil : Soil.SoilCNProcessNetwork}
    (flow : PlantSoilReturnFlow soil) : Set₁ where
  constructor mycorrhizal-plant-carbon-return
  field
    rootMechanism : Root.RootSoilIonWaterMechanism
    extension : Root.MycorrhizalIonWaterExtension rootMechanism
    returnKindIsFungal : kind flow ≡ fungalCarbonTransfer
    plantCarbonCostReference : String
    fungalTransferReference : String
    fieldValidationReference : String

open MycorrhizalPlantCarbonReturn public

------------------------------------------------------------------------
-- Closed structural cycle receipt.
------------------------------------------------------------------------

record SoilPlantFruitSoilCycleReceipt : Set₁ where
  constructor soil-plant-fruit-soil-cycle-receipt
  field
    forward : Forward.KNFSoilPlantFruitLoopReceipt
    returnFlow : PlantSoilReturnFlow (Forward.soil forward)
    reentryResponse : SoilReentryResponse
    returnFeedsExistingSoilProcessNetwork : Bool
    returnProcessMeasured : Bool
    conservationChecked : Bool
    cycleTimeSupportReference : String

open SoilPlantFruitSoilCycleReceipt public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PlantResidueMeansAvailableNutrientPermission : Set where

data ReturnFlowMeansNetFertilityGainPermission : Set where

data RootExudationMeansMicrobialBenefitPermission : Set where

data ClosedCycleMeansNoExternalInputPermission : Set where

data ClosedCycleMeansNoLossPermission : Set where

data KNFIMOEqualsMycorrhizalReturnPermission : Set where

plantResidueDoesNotByItselfMeanAvailableNutrient :
  PlantResidueMeansAvailableNutrientPermission → ⊥
plantResidueDoesNotByItselfMeanAvailableNutrient ()

returnFlowDoesNotByItselfMeanNetFertilityGain :
  ReturnFlowMeansNetFertilityGainPermission → ⊥
returnFlowDoesNotByItselfMeanNetFertilityGain ()

rootExudationDoesNotByItselfMeanMicrobialBenefit :
  RootExudationMeansMicrobialBenefitPermission → ⊥
rootExudationDoesNotByItselfMeanMicrobialBenefit ()

closedCycleDoesNotMeanNoExternalInput :
  ClosedCycleMeansNoExternalInputPermission → ⊥
closedCycleDoesNotMeanNoExternalInput ()

closedCycleDoesNotMeanNoLoss :
  ClosedCycleMeansNoLossPermission → ⊥
closedCycleDoesNotMeanNoLoss ()

knfIMOIsNotMycorrhizalCarbonReturn :
  KNFIMOEqualsMycorrhizalReturnPermission → ⊥
knfIMOIsNotMycorrhizalCarbonReturn ()

record KNFPlantSoilReturnFlowBoundary : Set where
  constructor knf-plant-soil-return-flow-boundary
  field
    plantToSoilReturnIsFirstClass : Bool
    returnUsesExistingSoilProcessNetwork : Bool
    conservationRemainsExplicit : Bool
    mycorrhizalReturnIsDistinctFromKNFIMO : Bool
    returnFlowAutomaticallyMeansNetFertilityGain : Bool
    cycleAutomaticallyMeansClosedToExternalEnvironment : Bool

canonicalKNFPlantSoilReturnFlowBoundary : KNFPlantSoilReturnFlowBoundary
canonicalKNFPlantSoilReturnFlowBoundary =
  knf-plant-soil-return-flow-boundary
    true true true true false false
