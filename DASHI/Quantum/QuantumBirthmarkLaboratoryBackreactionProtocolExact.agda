{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkLaboratoryBackreactionProtocolExact where

open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- MATCHED-STRESS LABORATORY DISCRIMINATOR
--
-- The experiment must not confuse ordinary mass/thermal/EM differences with a
-- history-sector effect.  We therefore compare two protocols with matched
-- conventional stress-energy controls but different declared history/birthmark
-- preparation.  A history-dark-energy model must predict a differential
-- gravitational observable; the null predicts no extra history-only signal.
------------------------------------------------------------------------

record MatchedStressHistoryProtocol : Set₁ where
  field
    Preparation : Set
    ConventionalStress : Set
    HistoryRecord : Set
    GravityObservable : Set

    leftPreparation rightPreparation : Preparation

    conventionalStress : Preparation → ConventionalStress
    historyRecord : Preparation → HistoryRecord
    gravityObservable : Preparation → GravityObservable

    conventionalStressMatched :
      conventionalStress leftPreparation
      ≡ conventionalStress rightPreparation

    HistoryDifference : Set
    historyDifferenceEvidence : HistoryDifference

open MatchedStressHistoryProtocol public

record HistoryBackreactionPrediction
    (protocol : MatchedStressHistoryProtocol) : Set₁ where
  field
    DifferentialSignal : Set
    predictedDifferentialSignal : DifferentialSignal

    SignalMatchesObservableDifference : Set
    signalMatchesObservableDifferenceEvidence :
      SignalMatchesObservableDifference

open HistoryBackreactionPrediction public

record NullHistoryBackreactionModel
    (protocol : MatchedStressHistoryProtocol) : Set₁ where
  field
    NoExtraHistorySignal : Set
    noExtraHistorySignal : NoExtraHistorySignal

open NullHistoryBackreactionModel public

matchedConventionalStressRequired : Bool
matchedConventionalStressRequired = true

historyPreparationDifferenceRequired : Bool
historyPreparationDifferenceRequired = true

nonzeroDifferentialSignalPredictedByCurrentTheory : Bool
nonzeroDifferentialSignalPredictedByCurrentTheory = false

instrumentSensitivityDerived : Bool
instrumentSensitivityDerived = false

systematicErrorBudgetDerived : Bool
systematicErrorBudgetDerived = false

positiveSignalUniquelyImpliesQuantumGravity : Bool
positiveSignalUniquelyImpliesQuantumGravity = false

laboratoryProtocolCarrierOwned : Bool
laboratoryProtocolCarrierOwned = true
