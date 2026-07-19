module DASHI.Biology.Levin.CorticalFieldComputationCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.MixedSelectivityFieldControl as Mixed
import DASHI.Biology.Levin.TravelingWaveComputationBoundary as Wave
import DASHI.Biology.Levin.OscillatoryMemoryStorageAdapter as Memory
import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as Chemistry
import DASHI.Biology.Levin.ExistingBiologyPhysicalStateAdapter as Existing

record CorticalFieldComputationCore : Set where
  field
    fieldControlBoundary : Mixed.FieldControlBoundary
    travelingWaveBoundary : Wave.TravelingWaveBoundary
    memoryAdapter : Memory.OscillatoryMemoryAdapter
    chemistryAdapter : Chemistry.BioelectricChemistryWaveAdapter
    existingBiologyAdapter : Existing.ExistingBiologyPhysicalStateAdapter
    measuredFieldEffectsAreNotEpiphenomenalByDefinition : Bool
    anesthesiaConvergenceDoesNotProveUniversalConsciousnessMechanism : Bool
    corticalBindingDoesNotSufficeForConsciousness : Bool
    waveOrganisationDoesNotEliminateSynapticComputation : Bool
    nonNeuralWavesDoNotBecomeCognitiveByShapeAlone : Bool
    candidateOnly : Bool
    interpretation : String

canonicalCorticalFieldComputationCore : CorticalFieldComputationCore
canonicalCorticalFieldComputationCore = record
  { fieldControlBoundary = Mixed.canonicalFieldControlBoundary
  ; travelingWaveBoundary = Wave.canonicalTravelingWaveBoundary
  ; memoryAdapter = Memory.canonicalOscillatoryMemoryAdapter
  ; chemistryAdapter = Chemistry.canonicalBioelectricChemistryWaveAdapter
  ; existingBiologyAdapter = Existing.canonicalExistingBiologyPhysicalStateAdapter
  ; measuredFieldEffectsAreNotEpiphenomenalByDefinition = true
  ; anesthesiaConvergenceDoesNotProveUniversalConsciousnessMechanism = true
  ; corticalBindingDoesNotSufficeForConsciousness = true
  ; waveOrganisationDoesNotEliminateSynapticComputation = true
  ; nonNeuralWavesDoNotBecomeCognitiveByShapeAlone = true
  ; candidateOnly = true
  ; interpretation = "Mixed-selectivity, traveling-wave, memory and physical-chemistry surfaces are integrated without promoting oscillatory organisation to a complete theory of cognition or consciousness"
  }
