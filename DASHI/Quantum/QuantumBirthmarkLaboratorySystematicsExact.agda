{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkLaboratorySystematicsExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MATCHED-HISTORY SYSTEMATICS CUT
------------------------------------------------------------------------

record MatchedHistorySystematicsCut : Set where
  constructor matched-history-systematics-cut
  field
    conventionalStressRematchingAfterHistoryPreparation : Bool
    massGeometryAndPositionControl : Bool
    electrostaticPatchAndChargeControl : Bool
    magneticControl : Bool
    thermalAndMechanicalStateControl : Bool
    opticalReadoutBackactionControl : Bool
    directMechanicalCrossTalkControl : Bool
    vibrationAndAcousticControl : Bool
    historyPreparationBlindOrRandomized : Bool
    synchronousHistoryModulationRequired : Bool
    nullPreparationChannelRequired : Bool
    calibrationSignalRequired : Bool
    preregisteredAnalysisRequired : Bool

    numericalSystematicsBudgetClosed : Bool
    matchedHistoryPreparationDemonstrated : Bool

open MatchedHistorySystematicsCut public

canonicalMatchedHistorySystematicsCut : MatchedHistorySystematicsCut
canonicalMatchedHistorySystematicsCut =
  matched-history-systematics-cut
    true true true true true true true true true true true true true
    false false

systematicsCategoryListOwned : Bool
systematicsCategoryListOwned = true

numericalSystematicsBudgetClosedCanonical : Bool
numericalSystematicsBudgetClosedCanonical =
  numericalSystematicsBudgetClosed canonicalMatchedHistorySystematicsCut

matchedHistoryPreparationDemonstratedCanonical : Bool
matchedHistoryPreparationDemonstratedCanonical =
  matchedHistoryPreparationDemonstrated canonicalMatchedHistorySystematicsCut

synchronousHistoryModulationRequiredCanonical : Bool
synchronousHistoryModulationRequiredCanonical =
  synchronousHistoryModulationRequired canonicalMatchedHistorySystematicsCut

systematicsReading : String
systematicsReading =
  "The history-state switch must be the modulation channel while conventional stress-energy is re-matched and independently monitored. Otherwise a residual force can be ordinary thermal, EM, mechanical, optical or geometric backreaction rather than a history-only gravitational effect."
