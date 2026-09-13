module DASHI.Environment.KNFPermacultureEmbodiedEnergyBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Environment.KoreanNaturalFarmingExact as KNF
import DASHI.Environment.PermacultureEmbodiedEnergyLandscapeBridgeExact as PermacultureEnergy
import DASHI.Biology.FruitEmbodiedEnergyHistoryFibreExact as FruitEnergy
import DASHI.Environment.QuantitiesConservation as Conservation

------------------------------------------------------------------------
-- KNF x PERMACULTURE x EMBODIED ENERGY
--
-- Shared structural reading:
--   local biological/material flows can be retained, transformed and reused
--   within a site instead of treating every fertility input as an imported
--   terminal commodity.
--
-- No identity is asserted between KNF and permaculture.  KNF is a particular
-- practice lineage; the permaculture owner contributes a design/accounting lens.
------------------------------------------------------------------------

data DependencyDirection : Set where
  importedDependency retainedLocalFlow mixedDependency : DependencyDirection

data TransformationRole : Set where
  collect preserve propagate ferment compost apply : TransformationRole

record LocalFlowTransformation : Set where
  constructor local-flow-transformation
  field
    preparation : KNF.KNFPreparation
    dependency : DependencyDirection
    role : TransformationRole
    embodiedProcessEnergy : FruitEnergy.EmbodiedEnergy
    carbonBalance : Conservation.CarbonBalance
    waterBalance : Conservation.WaterBalance

open LocalFlowTransformation public

------------------------------------------------------------------------
-- The key accounting firewall:
-- retaining a resource within the local system changes provenance/flow graph;
-- it does not create matter or free energy.
------------------------------------------------------------------------

data LocalRetentionMeansNoEnergyCostPermission : Set where

data FermentationCreatesNetFreeEnergyPermission : Set where

data ReducedImportsMeansClosedSystemPermission : Set where

data KNFIsIdenticalToPermaculturePermission : Set where

localRetentionDoesNotEraseEnergeticCost :
  LocalRetentionMeansNoEnergyCostPermission → ⊥
localRetentionDoesNotEraseEnergeticCost ()

fermentationDoesNotCreateNetFreeEnergy :
  FermentationCreatesNetFreeEnergyPermission → ⊥
fermentationDoesNotCreateNetFreeEnergy ()

reducedImportsDoNotMakeSystemClosed :
  ReducedImportsMeansClosedSystemPermission → ⊥
reducedImportsDoNotMakeSystemClosed ()

knfIsNotDefinitionallyPermaculture :
  KNFIsIdenticalToPermaculturePermission → ⊥
knfIsNotDefinitionallyPermaculture ()

------------------------------------------------------------------------
-- Landscape-capacity adapter.
-- A caller may identify a KNF-transformed local flow with a declared landscape
-- store only by supplying exact same-object accounting receipts.
------------------------------------------------------------------------

record KNFLandscapeStoreAdapter : Set where
  constructor knf-landscape-store-adapter
  field
    transformedFlow : LocalFlowTransformation
    landscapeStore : PermacultureEnergy.LandscapeStoredCapacity
    samePhysicalEnergy :
      embodiedProcessEnergy transformedFlow ≡
      PermacultureEnergy.physicalEnergy landscapeStore
    sameCarbonLedger :
      carbonBalance transformedFlow ≡
      PermacultureEnergy.carbonAccount landscapeStore
    sameWaterLedger :
      waterBalance transformedFlow ≡
      PermacultureEnergy.waterAccount landscapeStore

open KNFLandscapeStoreAdapter public

------------------------------------------------------------------------
-- Application-to-outcome evidence remains downstream.
------------------------------------------------------------------------

record KNFDesignEvidencePacket : Set where
  constructor knf-design-evidence-packet
  field
    resourceFlow : LocalFlowTransformation
    application : KNF.KNFApplication
    outcomeEvidence : KNF.KNFOutcomeEvidence
    samePreparation :
      KNF.preparation application ≡ preparation resourceFlow
    evidenceAppliesToApplication :
      KNF.application outcomeEvidence ≡ application

open KNFDesignEvidencePacket public

record KNFPermacultureEmbodiedEnergyBoundary : Set where
  constructor knf-permaculture-embodied-energy-boundary
  field
    localInputsCanChangeDependencyGraph : Bool
    localInputsStillHaveMaterialEnergeticCost : Bool
    fermentationIsTransformationNotFreeEnergyCreation : Bool
    waterCarbonAndEnergyLedgersRemainDistinct : Bool
    knfPracticeAndPermacultureDesignLensRemainDistinct : Bool
    measuredEffectRequiresApplicationSpecificEvidence : Bool

canonicalKNFPermacultureEmbodiedEnergyBoundary :
  KNFPermacultureEmbodiedEnergyBoundary
canonicalKNFPermacultureEmbodiedEnergyBoundary =
  knf-permaculture-embodied-energy-boundary
    true true true true true true
