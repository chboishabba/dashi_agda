module DASHI.Physics.Materials.RezaFangAlloyMetamaterialDiscriminationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact as Reza
import DASHI.Physics.Materials.FangDainingActiveMechanicalMetamaterialBidiExact as Fang

------------------------------------------------------------------------
-- ALLOY != METAMATERIAL BY LABEL
--
-- Reza/Jacinto's source object is a composition/process-defined nickel alloy.
-- Fang's source object is an active mechanical metamaterial/advanced structure
-- whose designed architecture and stimulus-response relation are constitutive.
-- A material could in principle participate in both categories, but only an
-- explicit structure/property/provenance receipt may weld them.
------------------------------------------------------------------------

data MaterialObjectClass : Set where
  compositionProcessAlloy structuredMechanicalMetamaterial hybridMaterialArchitecture : MaterialObjectClass

record MaterialClassificationReceipt : Set where
  constructor material-classification-receipt
  field
    objectReference : String
    objectClass : MaterialObjectClass
    compositionConstitutive : Bool
    architectureConstitutive : Bool
    stimulusResponseConstitutive : Bool
    sourceReference : String

open MaterialClassificationReceipt public

rezaAlloyClassification : MaterialClassificationReceipt
rezaAlloyClassification = material-classification-receipt
  "Jacinto/Hardwick burn-resistant high-tensile nickel alloy"
  compositionProcessAlloy
  true false false
  "US20030053926A1 / US20040208777A1"

fangMetamaterialClassification : MaterialClassificationReceipt
fangMetamaterialClassification = material-classification-receipt
  "Fang/Li active mechanical metamaterials"
  structuredMechanicalMetamaterial
  false true true
  "BIT Institute of Advanced Structure Technology 2021-11-09 institutional research page"

record AlloyMetamaterialBridgeObligation : Set where
  constructor alloy-metamaterial-bridge-obligation
  field
    alloyObject : String
    metamaterialClaim : String
    requiredArchitectureReceipt : String
    requiredEffectivePropertyReceipt : String
    requiredProvenanceReceipt : String
    bridgePaid : Bool

open AlloyMetamaterialBridgeObligation public

mondaloyMetamaterialBridge : AlloyMetamaterialBridgeObligation
mondaloyMetamaterialBridge = alloy-metamaterial-bridge-obligation
  "Jacinto/Hardwick burn-resistant nickel alloy"
  "claim that the alloy is a reverse-engineered / S4 metamaterial"
  "designed sub-wavelength/mesoscale/mechanical architecture showing metamaterial classification for the same object"
  "measured effective property attributable to that architecture rather than nominal alloy composition/process alone"
  "same-object custody/provenance chain to the alleged classified precursor"
  false

alloyPropertyDoesNotImplyMetamaterial : Bool
alloyPropertyDoesNotImplyMetamaterial = true

metamaterialLabelDoesNotImplyExoticProvenance : Bool
metamaterialLabelDoesNotImplyExoticProvenance = true

existingRezaBoundary : Reza.RezaAlloyBoundary
existingRezaBoundary = Reza.canonicalRezaAlloyBoundary

existingFangBoundary : Fang.FangMetamaterialBoundary
existingFangBoundary = Fang.canonicalFangMetamaterialBoundary

record AlloyMetamaterialDiscriminationBoundary : Set where
  constructor alloy-metamaterial-discrimination-boundary
  field
    highTemperatureAlloyAutomaticallyMetamaterial : Bool
    mechanicalMetamaterialAutomaticallyCompositionNovel : Bool
    bothCategoriesAutomaticallyShareProvenance : Bool
    sameObjectCouldOccupyBothWithExplicitReceipt : Bool
    classifiedOriginRequiresIndependentProvenance : Bool

canonicalAlloyMetamaterialDiscriminationBoundary : AlloyMetamaterialDiscriminationBoundary
canonicalAlloyMetamaterialDiscriminationBoundary = alloy-metamaterial-discrimination-boundary
  false false false true true
