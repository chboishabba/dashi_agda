{-# OPTIONS --safe #-}
module DASHI.Physics.Materials.RocketdyneMaterialSurvivabilityCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Propulsion.Rocketdyne1974MaterialIdentityAndConstitutiveDataExact as Mat
import DASHI.Physics.Propulsion.Rocketdyne1974TwoMaterialDiscriminatorExact as Disc
import DASHI.Physics.Propulsion.Rocketdyne1974IdentifiabilityCutExact as Cut
import DASHI.Physics.Materials.FusionPropulsionMaterialSurvivabilityCrossPollinationExact as FusionMat
import DASHI.Physics.Materials.RezaBurnResistantAlloyBidiExact as Reza

------------------------------------------------------------------------
-- MATERIAL-SURVIVABILITY CROSS-POLLINATION
--
-- Rocketdyne's historical Haynes-25 -> coated WC103 comparison supplies a
-- source-indexed example of propulsion material substitution under severe
-- thermal service.  Reza/Mondaloy and fusion-propulsion material work share
-- the engineering grammar (environment -> material state -> qualified
-- survivability) but not the same chemistry, mechanism, or historical object.
------------------------------------------------------------------------

record SurvivabilityTransfer : Set where
  constructor survivability-transfer
  field
    sourceCase : String
    destinationLane : String
    transferableMethod : String
    sameMaterialSystem : Bool
    sameHistoricalProgramme : Bool
    exactEnvironmentTransferPaid : Bool
    remainingPayment : String

rocketdyneToReza : SurvivabilityTransfer
rocketdyneToReza = survivability-transfer
  "1974 Haynes-25 / WC103 nozzle comparison"
  "Reza/Jacinto/Hardwick oxygen-rich chemical-rocket materials"
  "keep operating envelope, material revision, damage observation and qualification evidence as separate coordinates"
  false false false
  "pay oxygen compatibility, alloy microstructure, pressure/temperature history and same-object qualification separately"

rocketdyneToFusion : SurvivabilityTransfer
rocketdyneToFusion = survivability-transfer
  "1974 radiation/insulation-cooled chemical-rocket nozzle"
  "fusion-propulsion material survivability"
  "reuse provenance and same-model discrimination discipline"
  false false false
  "plasma radiation, magnetic loading, neutron/ion damage and thermal environment are distinct producers"

existingFusionMaterialBoundary : FusionMat.FusionMaterialBoundary
existingFusionMaterialBoundary = FusionMat.canonicalFusionMaterialBoundary

existingRezaBoundary : Reza.RezaAlloyBoundary
existingRezaBoundary = Reza.canonicalRezaAlloyBoundary

rocketdyneEmpiricalDiscriminator : Disc.TwoMaterialDiscriminator
rocketdyneEmpiricalDiscriminator = Disc.currentDiscriminator

rocketdyneIdentifiabilityCut : Cut.PhysicalMaxCut
rocketdyneIdentifiabilityCut = Cut.currentPhysicalMaxCut

record CrossPollinationBoundary : Set where
  constructor cross-pollination-boundary
  field
    sharedSurvivabilityGrammar : Bool
    sharedGrammarImpliesSameMaterial : Bool
    sharedGrammarImpliesSameProgramme : Bool
    historicalDiscriminatorMayConstrainMethod : Bool
    destinationStillNeedsOwnValidation : Bool

canonicalCrossPollinationBoundary : CrossPollinationBoundary
canonicalCrossPollinationBoundary =
  cross-pollination-boundary true false false true true
