{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkLaboratorySensitivityMaxCutExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.String using (String)

import DASHI.Quantum.QuantumBirthmarkLaboratoryBackreactionProtocolExact as Protocol
import DASHI.Quantum.QuantumBirthmarkLaboratorySensitivitySourceAtlasExact as Source
import DASHI.Quantum.QuantumBirthmarkLaboratorySensitivityExact as Sensitivity
import DASHI.Quantum.QuantumBirthmarkLaboratorySystematicsExact as Systematics
import DASHI.Empirical.GRQuantumBenchmarkProtocol as Benchmark
import DASHI.Empirical.GRQuantumPredictionProtocol as Prediction

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

laboratorySensitivityReading : String
laboratorySensitivityReading =
  "Transfer benchmark only: the 7.6 mg / 0.654 mm point-mass estimate is about 9013 aN, so the published 50 aN (2 sigma) force uncertainty corresponds to about 5.55e-3 of the Newtonian scale. The lattice-atom result corresponds to about 0.187 fractional uncertainty at 1 sigma. For the 2026 quantum-ready optomechanical design, a history-only signal epsilon_H times the full gravity signal costs epsilon_H^-2 in integration time under the same stationary-noise model. None is presently a history-sector bound."

recommendedExperimentalCut : String
recommendedExperimentalCut =
  "Use the history preparation itself as a randomized synchronous modulation while holding source/probe geometry and conventional stress fixed. Estimate epsilon_hat = Delta O / O_Newton against an independently calibrated Newtonian carrier. A publishable null result requires the matched-history systematic floor to be smaller than the target epsilon band."

genericBenchmarkReferences : Benchmark.ExistingBenchmarkReferences
genericBenchmarkReferences = Benchmark.canonicalExistingBenchmarkReferences

birthmarkLaboratoryPredictionRequest : Prediction.PredictionRequestPacket
birthmarkLaboratoryPredictionRequest =
  Prediction.prediction-request-packet
    "DASHI.Quantum.QuantumBirthmarkLaboratoryBackreactionProtocolExact"
    "DASHI.Quantum.QuantumBirthmarkHistoryDarkEnergyTerminalMaxCutExact"
    "DASHI.Quantum.QuantumBirthmarkErgodicityExact"
    "DASHI.Quantum.QuantumBirthmarkHistoryCommonActionVariationExact"
    "DASHI.Empirical.GRQuantumBenchmarkProtocol"
    false
    refl
    "Instrument transfer sensitivity is quantitative, but the microscopic history coupling epsilon_H is not derived. A nonzero physical central value would therefore still be fabricated."

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
numericalSystematicsBudgetClosed =
  Systematics.numericalSystematicsBudgetClosedCanonical

statusStatement : String
statusStatement =
  "Item 4 max-cut: instrument-scale transfer sensitivity is quantitative and source-backed; matched-history systematics are explicitly enumerated; the experiment is routed into the existing GR/quantum matched-benchmark and quantitative-prediction governance. The irreducible leaves are a microscopic epsilon_H prediction, a realized matched-history state switch with a closed numerical systematics budget, and an actual preregistered measurement."
