module DASHI.Biology.Levin.BioelectricPatternSharpnessAging where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.PatternMemoryCore as Memory
import DASHI.Biology.Levin.BioelectricChemistryWaveAdapter as Chemistry
import DASHI.Biology.Levin.ExistingBiologyPhysicalStateAdapter as Existing

------------------------------------------------------------------------
-- Candidate aging mechanism: degradation of spatial bioelectric contrast.

record PatternSharpnessObservation : Set where
  field
    spatialVoltageMapMeasured      : Bool
    ageOrSenescenceIndexed         : Bool
    contrastMetricSpecified        : Bool
    repeatabilityEstablished       : Bool
    tissueAndCultureSeparated      : Bool
    chemistryCovariatesMeasured    : Bool
    interpretation                : String

record PatternRestorationWitness : Set where
  field
    interventionSpecified          : Bool
    prePatternMeasured             : Bool
    postPatternMeasured            : Bool
    targetPatternSpecified         : Bool
    morphologyOrFunctionAssessed   : Bool
    offTargetEffectsAssessed       : Bool
    mutationOrDamageStillPresent   : Bool
    causalRestorationSupported     : Bool

record BioelectricAgingBoundary : Set where
  field
    memoryBoundary : Memory.PatternMemoryBoundary
    chemistryLane  : Chemistry.BioelectricChemistryWaveAdapter
    existingBiologyLane : Existing.ExistingBiologyPhysicalStateAdapter
    blurNotScalarVoltageShift : Bool
    correlationNotUltimateCause : Bool
    patternRepairNotWholeBodyRejuvenation : Bool
    animalRepairNotHumanLongevityAuthority : Bool
    electroceuticalChoiceNeedsModelAndValidation : Bool

canonicalBioelectricAgingBoundary : BioelectricAgingBoundary
canonicalBioelectricAgingBoundary = record
  { memoryBoundary = Memory.canonicalPatternMemoryBoundary
  ; chemistryLane = Chemistry.canonicalBioelectricChemistryWaveAdapter
  ; existingBiologyLane = Existing.canonicalExistingBiologyPhysicalStateAdapter
  ; blurNotScalarVoltageShift = true
  ; correlationNotUltimateCause = true
  ; patternRepairNotWholeBodyRejuvenation = true
  ; animalRepairNotHumanLongevityAuthority = true
  ; electroceuticalChoiceNeedsModelAndValidation = true
  }
