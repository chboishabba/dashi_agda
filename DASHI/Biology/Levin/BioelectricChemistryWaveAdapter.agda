module DASHI.Biology.Levin.BioelectricChemistryWaveAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.CondensateElectroosmoticState as Condensate
import DASHI.Biology.Levin.ATPDependentCytoplasmicOrganisation as ATP
import DASHI.Biology.Levin.MitochondrialBioenergeticAdapter as Mitochondria

record PhysicalChemistryCarrier : Set where
  field
    ionicCompositionRelevant : Bool
    membranePotentialRelevant : Bool
    hydrationAndPhaseStateRelevant : Bool
    metabolicEnergyRelevant : Bool
    geometryAndBoundaryConditionsRelevant : Bool
    chemicalCarrierDoesNotFixSemanticContent : Bool

record BioelectricChemistryWaveAdapter : Set where
  field
    carrier : PhysicalChemistryCarrier
    ionicAndFieldDynamicsCoupled : Bool
    metabolicSupplyConstrainsOscillation : Bool
    condensateStateMayModulatePropagation : Bool
    chemistryDoesNotReduceToWaveDescription : Bool
    waveDescriptionDoesNotReplaceMolecularMechanism : Bool
    interpretation : String

canonicalPhysicalChemistryCarrier : PhysicalChemistryCarrier
canonicalPhysicalChemistryCarrier = record
  { ionicCompositionRelevant = true
  ; membranePotentialRelevant = true
  ; hydrationAndPhaseStateRelevant = true
  ; metabolicEnergyRelevant = true
  ; geometryAndBoundaryConditionsRelevant = true
  ; chemicalCarrierDoesNotFixSemanticContent = true
  }

canonicalBioelectricChemistryWaveAdapter : BioelectricChemistryWaveAdapter
canonicalBioelectricChemistryWaveAdapter = record
  { carrier = canonicalPhysicalChemistryCarrier
  ; ionicAndFieldDynamicsCoupled = true
  ; metabolicSupplyConstrainsOscillation = true
  ; condensateStateMayModulatePropagation = true
  ; chemistryDoesNotReduceToWaveDescription = true
  ; waveDescriptionDoesNotReplaceMolecularMechanism = true
  ; interpretation = "Oscillatory bioelectric control is constrained by ionic, membrane, hydration, phase and energetic chemistry without being reducible to any single carrier"
  }
