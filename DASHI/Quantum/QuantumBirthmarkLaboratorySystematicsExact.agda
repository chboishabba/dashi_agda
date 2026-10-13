{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkLaboratorySystematicsExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MATCHED-HISTORY SYSTEMATICS CUT
--
-- A history-only gravity test is stronger than an ordinary small-force test:
-- the operation used to change the history record can itself change thermal,
-- electromagnetic, mechanical, optical or mass-distribution stress.  Those
-- ordinary channels must be re-measured AFTER history preparation, not merely
-- assumed equal from the nominal apparatus design.
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

numericalSystematicsBudgetClosed : Bool
numericalSystematicsBudgetClosed = false

matchedHistoryPreparationDemonstrated : Bool
matchedHistoryPreparationDemonstrated = false

synchronousHistoryModulationRequired : Bool
synchronousHistoryModulationRequired = true

systematicsReading : String
systematicsReading =
  "The history-state switch must be the modulation channel while conventional stress-energy is re-matched and independently monitored. Otherwise a residual force can be ordinary thermal, EM, mechanical, optical or geometric backreaction rather than a history-only gravitational effect."
