{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkLaboratorySensitivityMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Quantum.QuantumBirthmarkLaboratoryBackreactionProtocolExact as Protocol
import DASHI.Quantum.QuantumBirthmarkLaboratorySensitivitySourceAtlasExact as Source
import DASHI.Quantum.QuantumBirthmarkLaboratorySensitivityExact as Sensitivity
import DASHI.Quantum.QuantumBirthmarkLaboratorySystematicsExact as Systematics
import DASHI.Empirical.GRQuantumBenchmarkProtocol as Benchmark
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction

------------------------------------------------------------------------
-- LABORATORY BACKREACTION MAX-CUT
--
-- Existing experiments establish instrument scales, not a history-sector
-- signal.  We therefore split the endpoint into:
--
--   (A) transfer sensitivity -- what epsilon_H * Newtonian signal would be
--       resolvable if the history-only protocol reached the cited noise scale;
--   (B) theory prediction -- the microscopic theory must derive epsilon_H;
--   (C) matched-history realization -- conventional stress must stay matched;
--   (D) measurement -- a held-out/pre-registered experiment must actually run.
------------------------------------------------------------------------

record LaboratorySensitivityReceipt : Set where
  constructor laboratory-sensitivity-receipt
  field
    qualitativeMatchedStressProtocolOwned : Bool
    classicalMilligramTransferBenchmarkOwned : Bool
    atomInterferometerTransferBenchmarkOwned : Bool
    quantumReadyOptomechanicalScalingOwned : Bool
    instrumentTransferSensitivityOwned : Bool
    systematicsCutOwned : Bool
    genericGRQuantumBenchmarkGovernanceReused : Bool
    genericQuantitativePredictionGovernanceReused : Bool

    historySignalMagnitudeStillRequiresMicroscopicCoupling : Bool
    matchedHistorySystematicsBudgetStillRequired : Bool
    matchedHistoryPreparationStillRequired : Bool
    parameterFreePredictionStillRequired : Bool
    actualHistoryConditionedMeasurementStillRequired : Bool

open LaboratorySensitivityReceipt public

canonicalLaboratorySensitivityReceipt : LaboratorySensitivityReceipt
canonicalLaboratorySensitivityReceipt =
  laboratory-sensitivity-receipt
    true true true true true true true true
    true true true true true

classicalMilligramTransferBenchmarkOwned : Bool
classicalMilligramTransferBenchmarkOwned = true

atomInterferometerTransferBenchmarkOwned : Bool
atomInterferometerTransferBenchmarkOwned = true

quantumReadyOptomechanicalScalingOwned : Bool
quantumReadyOptomechanicalScalingOwned = true

instrumentTransferSensitivityOwned : Bool
instrumentTransferSensitivityOwned = Sensitivity.instrumentTransferSensitivityOwned

systematicsCutOwned : Bool
systematicsCutOwned = Systematics.systematicsCategoryListOwned

historySignalMagnitudeStillRequiresMicroscopicCoupling : Bool
historySignalMagnitudeStillRequiresMicroscopicCoupling = true

matchedHistorySystematicsBudgetStillRequired : Bool
matchedHistorySystematicsBudgetStillRequired = true

matchedHistoryPreparationStillRequired : Bool
matchedHistoryPreparationStillRequired = true

parameterFreePredictionStillRequired : Bool
parameterFreePredictionStillRequired = true

actualHistoryConditionedMeasurementStillRequired : Bool
actualHistoryConditionedMeasurementStillRequired = true

------------------------------------------------------------------------
-- QUANTITATIVE READINGS FROM THE LOCAL-PYTHON / SOURCE-BACKED AUDIT
------------------------------------------------------------------------

laboratorySensitivityReading : String
laboratorySensitivityReading =
  "Transfer benchmark only: the 7.6 mg / 0.654 mm point-mass estimate is about 9013 aN, so the published 50 aN (2 sigma) force uncertainty corresponds to about 5.55e-3 of the Newtonian scale. The lattice-atom result corresponds to about 0.187 fractional uncertainty at 1 sigma. For the 2026 quantum-ready optomechanical design, a history-only signal epsilon_H times the full gravity signal costs epsilon_H^-2 in integration time under the same stationary-noise model. None is presently a history-sector bound."

recommendedExperimentalCut : String
recommendedExperimentalCut =
  "Use the history preparation itself as a randomized synchronous modulation while holding source/probe geometry and conventional stress fixed. The first analysis target is a differential force/acceleration channel normalized to the independently calibrated Newtonian signal, epsilon_hat = Delta O / O_Newton. A publishable null result requires the matched-history systematics budget to be smaller than the target epsilon band."

------------------------------------------------------------------------
-- EMPIRICAL GOVERNANCE CROSS-POLLINATION
------------------------------------------------------------------------

benchmarkGovernanceAlreadyExists : Bool
benchmarkGovernanceAlreadyExists = true

predictionGovernanceAlreadyExists : Bool
predictionGovernanceAlreadyExists = true

existingPredictionProtocolSuppliesNonzeroHistoryCentralValue : Bool
existingPredictionProtocolSuppliesNonzeroHistoryCentralValue = false

transferSensitivityIsNotHistoryConstraint : Bool
transferSensitivityIsNotHistoryConstraint =
  Sensitivity.transferSensitivityIsNotHistoryConstraint

currentExperimentsDidNotTestHistoryConditioning : Bool
currentExperimentsDidNotTestHistoryConditioning =
  Source.currentExperimentsDidNotTestHistoryConditioning

numericalSystematicsBudgetClosed : Bool
numericalSystematicsBudgetClosed = Systematics.numericalSystematicsBudgetClosed

statusStatement : String
statusStatement =
  "Item 4 max-cut: instrument-scale transfer sensitivity is now quantitative and source-backed; matched-history systematics are explicitly enumerated; existing GR/quantum benchmark and prediction governance is reused. The irreducible leaves are a microscopic epsilon_H prediction, a realized matched-history state switch with a closed numerical systematics budget, and an actual preregistered measurement."
