module DASHI.Environment.PermacultureEmbodiedEnergyLandscapeBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Units.SI as SI
import DASHI.Biology.FruitEmbodiedEnergyHistoryFibreExact as FruitEnergy
import DASHI.Environment.QuantitiesConservation as Conservation

------------------------------------------------------------------------
-- PERMACULTURE x EMBODIED ENERGY
--
-- Source-facing design reading:
-- David Holmgren's "Catch and Store Energy" principle motivates treating
-- biomass, living soils, water stores and preserved harvests as forms of
-- accumulated landscape capacity / stored resource potential.
--
-- DASHI boundary:
-- This module does not identify Holmgren's broad design-language use of
-- "energy" with SI joules.  Where literal physical energy is required we use
-- the existing SI Energy carrier.  Carbon, water, nutrient inventories and
-- ecological capacity remain separately typed coordinates.
------------------------------------------------------------------------

data LandscapeStoreKind : Set where
  livingBiomass soilOrganicMatter waterStore harvestedFood seedReserve : LandscapeStoreKind

data StoreRole : Set where
  capturedFlow retainedStock mobilisableReserve : StoreRole

record LandscapeStoredCapacity : Set where
  constructor landscape-stored-capacity
  field
    kind : LandscapeStoreKind
    role : StoreRole
    physicalEnergy : FruitEnergy.EmbodiedEnergy
    carbonAccount : Conservation.CarbonBalance
    waterAccount : Conservation.WaterBalance
    provenance : String

open LandscapeStoredCapacity public

------------------------------------------------------------------------
-- Fruit is one nested store in a larger plant/landscape hierarchy.
------------------------------------------------------------------------

record PlantFruitLandscapeEnergyWeld : Set where
  constructor plant-fruit-landscape-energy-weld
  field
    fruitHistory : FruitEnergy.PlantPartHistory
    landscapeStore : LandscapeStoredCapacity
    samePhysicalEnergy :
      FruitEnergy.embodiedEnergy fruitHistory ≡
      physicalEnergy landscapeStore

open PlantFruitLandscapeEnergyWeld public

------------------------------------------------------------------------
-- Design principle vs physical theorem firewall.
------------------------------------------------------------------------

data CatchStoreEnergyMeansSIJouleIdentityPermission : Set where

data BiomassMeansOnlyEnergyPermission : Set where

data StoredEnergyMeansGuaranteedFutureYieldPermission : Set where

data EmbodiedEnergyMeansNaturalCapitalPermission : Set where

catchStoreEnergyDoesNotCollapseToSIJoules :
  CatchStoreEnergyMeansSIJouleIdentityPermission → ⊥
catchStoreEnergyDoesNotCollapseToSIJoules ()

biomassIsNotOnlyAnEnergyCoordinate :
  BiomassMeansOnlyEnergyPermission → ⊥
biomassIsNotOnlyAnEnergyCoordinate ()

storedCapacityDoesNotGuaranteeFutureYield :
  StoredEnergyMeansGuaranteedFutureYieldPermission → ⊥
storedCapacityDoesNotGuaranteeFutureYield ()

embodiedEnergyDoesNotByItselfEqualNaturalCapital :
  EmbodiedEnergyMeansNaturalCapitalPermission → ⊥
embodiedEnergyDoesNotByItselfEqualNaturalCapital ()

record PermacultureEmbodiedEnergyBoundary : Set where
  constructor permaculture-embodied-energy-boundary
  field
    landscapeCanContainNestedStoredCapacity : Bool
    fruitCanBeOneEmbodiedInvestmentStore : Bool
    waterCarbonAndEnergyRemainDistinctTypedLedgers : Bool
    catchStoreEnergyIsLiteralSIIdentity : Bool
    storedCapacityAutomaticallyGuaranteesYield : Bool

canonicalPermacultureEmbodiedEnergyBoundary :
  PermacultureEmbodiedEnergyBoundary
canonicalPermacultureEmbodiedEnergyBoundary =
  permaculture-embodied-energy-boundary true true true false false
