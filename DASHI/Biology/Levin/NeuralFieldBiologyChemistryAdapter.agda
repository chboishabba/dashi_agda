module DASHI.Biology.Levin.NeuralFieldBiologyChemistryAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ExistingBiologyPhysicalStateAdapter as Existing
import DASHI.Biology.Levin.CondensateElectroosmoticState as Condensate
import DASHI.Biology.Levin.ATPDependentCytoplasmicOrganisation as ATP
import DASHI.Biology.Levin.StressGranuleVoltageBoundary as Voltage
import DASHI.Biology.Levin.NeuralMixedSelectivityBoundary as Mixed
import DASHI.Biology.Levin.TravelingFieldControl as Field
import DASHI.Biology.Levin.AnesthesiaPhaseFragmentation as Anesthesia
import DASHI.Biology.Levin.NeuralWaveAnalogComputation as Analog

record MolecularFieldScaleSeparation : Set where
  field
    receptorChemistryIsMicroscopicCarrier : Bool
    membraneAndExtracellularVoltageAreMesoscopicCarriers : Bool
    fieldPatternIsPopulationScaleObservable : Bool
    behaviouralStateIsMacroscopicObservable : Bool
    crossScaleMapRequiresIndependentWitness : Bool

record NeuralFieldBiologyChemistryAdapter : Set where
  field
    existingBiology : Existing.ExistingBiologyPhysicalStateAdapter
    scaleSeparation : MolecularFieldScaleSeparation
    mixedBoundary : Mixed.MixedSelectivityClaimBoundary
    fieldBoundary : Field.FieldControlBoundary
    anesthesiaBoundary : Anesthesia.AnesthesiaClaimBoundary
    analogBoundary : Analog.AnalogComputationBoundary
    chemistryDoesNotCollapseIntoFieldDescription : Bool
    fieldDescriptionDoesNotReplaceChemistry : Bool
    interpretation : String

canonicalScaleSeparation : MolecularFieldScaleSeparation
canonicalScaleSeparation = record
  { receptorChemistryIsMicroscopicCarrier = true
  ; membraneAndExtracellularVoltageAreMesoscopicCarriers = true
  ; fieldPatternIsPopulationScaleObservable = true
  ; behaviouralStateIsMacroscopicObservable = true
  ; crossScaleMapRequiresIndependentWitness = true
  }

canonicalNeuralFieldBiologyChemistryAdapter : NeuralFieldBiologyChemistryAdapter
canonicalNeuralFieldBiologyChemistryAdapter = record
  { existingBiology = Existing.canonicalExistingBiologyPhysicalStateAdapter
  ; scaleSeparation = canonicalScaleSeparation
  ; mixedBoundary = Mixed.canonicalMixedSelectivityClaimBoundary
  ; fieldBoundary = Field.canonicalFieldControlBoundary
  ; anesthesiaBoundary = Anesthesia.canonicalAnesthesiaClaimBoundary
  ; analogBoundary = Analog.canonicalAnalogComputationBoundary
  ; chemistryDoesNotCollapseIntoFieldDescription = true
  ; fieldDescriptionDoesNotReplaceChemistry = true
  ; interpretation = "Neural field dynamics extend the existing biological physical-state lane while molecular receptor, ionic, ATP, condensate, and membrane-voltage mechanisms remain independently typed"
  }
