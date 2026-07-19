module DASHI.Biology.Levin.OscillatoryMemoryStorageAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.PatternMemoryCore as PatternMemory
import DASHI.Biology.Levin.MemoryRemappingAcrossEmbodiment as Remapping
import DASHI.Biology.Levin.BoundaryHiddenStateNonrecurrence as HiddenState

record OscillatoryMemoryAdapter : Set where
  field
    storedTraceAndExpressedWaveSeparated : Bool
    synapticCarrierAndFieldReadoutMayInteract : Bool
    repeatedWaveDoesNotFixUniqueTrace : Bool
    wavePerturbationMayAlterRetrieval : Bool
    plasticityMayRewriteStorage : Bool
    transientWaveIsNotLongTermMemoryByDefinition : Bool
    interpretation : String

canonicalOscillatoryMemoryAdapter : OscillatoryMemoryAdapter
canonicalOscillatoryMemoryAdapter = record
  { storedTraceAndExpressedWaveSeparated = true
  ; synapticCarrierAndFieldReadoutMayInteract = true
  ; repeatedWaveDoesNotFixUniqueTrace = true
  ; wavePerturbationMayAlterRetrieval = true
  ; plasticityMayRewriteStorage = true
  ; transientWaveIsNotLongTermMemoryByDefinition = true
  ; interpretation = "Existing DASHI memory carriers remain distinct from the oscillatory field patterns that express, gate or rewrite them"
  }
