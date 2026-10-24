{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkLaboratorySensitivityExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _*_)

------------------------------------------------------------------------
-- FRACTIONAL HISTORY-ONLY SIGNAL MODEL
--
-- epsilon_H is deliberately phenomenological:
--
--   Delta O_H = epsilon_H O_Newton.
--
-- The current microscopic theory does not supply epsilon_H.  The purpose of
-- this module is only to convert existing gravity-instrument scales into the
-- fractional sensitivity a future matched-history experiment would need.
------------------------------------------------------------------------

historyOnlySignal : ℚ → ℚ → ℚ
historyOnlySignal epsilonH referenceSignal = epsilonH * referenceSignal

zeroHistoryCouplingGivesZeroSignal :
  (referenceSignal : ℚ) →
  historyOnlySignal 0ℚ referenceSignal ≡ 0ℚ
zeroHistoryCouplingGivesZeroSignal referenceSignal = refl

------------------------------------------------------------------------
-- 2026 MILLIGRAM TORSION-BALANCE TRANSFER BENCHMARK
------------------------------------------------------------------------

torsionPointMassNewtonianForceAttoNewtonRounded : ℚ
torsionPointMassNewtonianForceAttoNewtonRounded = Int.+ 9013167 / 1000

torsionPublishedTwoSigmaUncertaintyAttoNewton : ℚ
torsionPublishedTwoSigmaUncertaintyAttoNewton = Int.+ 50 / 1

torsionTwoSigmaFractionalTransfer : ℚ
torsionTwoSigmaFractionalTransfer = Int.+ 50000 / 9013167

torsionTwoSigmaFractionalTransferDefinition :
  torsionTwoSigmaFractionalTransfer ≡ Int.+ 50000 / 9013167
torsionTwoSigmaFractionalTransferDefinition = refl

------------------------------------------------------------------------
-- 2024 LATTICE ATOM-INTERFEROMETER TRANSFER BENCHMARK
------------------------------------------------------------------------

atomOneSigmaFractionalTransferSquared : ℚ
atomOneSigmaFractionalTransferSquared = Int.+ 3865 / 110889

atomOneSigmaFractionalTransferSquaredDefinition :
  atomOneSigmaFractionalTransferSquared ≡ Int.+ 3865 / 110889
atomOneSigmaFractionalTransferSquaredDefinition = refl

------------------------------------------------------------------------
-- EXACT SIGNAL-TO-NOISE / WHITE-NOISE PENALTIES
--
-- If signal amplitude is epsilon_H times the full-gravity signal and stationary
-- white noise is unchanged, integration time scales as SNR^2 / epsilon_H^2.
------------------------------------------------------------------------

tenPercentUnitSNRTimePenalty : Nat
tenPercentUnitSNRTimePenalty = 100

onePercentUnitSNRTimePenalty : Nat
onePercentUnitSNRTimePenalty = 10000

onePermilleUnitSNRTimePenalty : Nat
onePermilleUnitSNRTimePenalty = 1000000

tenPercentFiveSigmaTimePenalty : Nat
tenPercentFiveSigmaTimePenalty = 2500

onePercentFiveSigmaTimePenalty : Nat
onePercentFiveSigmaTimePenalty = 250000

onePermilleFiveSigmaTimePenalty : Nat
onePermilleFiveSigmaTimePenalty = 25000000

onePercentFiveSigmaTimePenaltyIs250000 :
  onePercentFiveSigmaTimePenalty ≡ 250000
onePercentFiveSigmaTimePenaltyIs250000 = refl

------------------------------------------------------------------------
-- 2026 QUANTUM-READY OPTOMECHANICAL SCALING
--
-- Source upper endpoint: about 15 h for unit SNR on the FULL gravity signal.
------------------------------------------------------------------------

optoFullGravityUnitSNRUpperHours : Nat
optoFullGravityUnitSNRUpperHours = 15

optoTenPercentUnitSNRUpperHours : Nat
optoTenPercentUnitSNRUpperHours = 1500

optoOnePercentUnitSNRUpperHours : Nat
optoOnePercentUnitSNRUpperHours = 150000

optoOnePermilleUnitSNRUpperHours : Nat
optoOnePermilleUnitSNRUpperHours = 15000000

optoTenPercentFiveSigmaUpperHours : Nat
optoTenPercentFiveSigmaUpperHours = 37500

optoOnePercentFiveSigmaUpperHours : Nat
optoOnePercentFiveSigmaUpperHours = 3750000

optoOnePermilleFiveSigmaUpperHours : Nat
optoOnePermilleFiveSigmaUpperHours = 375000000

optoTenPercentUnitSNRScaling :
  optoTenPercentUnitSNRUpperHours ≡ 1500
optoTenPercentUnitSNRScaling = refl

optoOnePercentUnitSNRScaling :
  optoOnePercentUnitSNRUpperHours ≡ 150000
optoOnePercentUnitSNRScaling = refl

optoOnePermilleUnitSNRScaling :
  optoOnePermilleUnitSNRUpperHours ≡ 15000000
optoOnePermilleUnitSNRScaling = refl

------------------------------------------------------------------------
-- AUTHORITY / INTERPRETATION FIREWALL
------------------------------------------------------------------------

instrumentTransferSensitivityOwned : Bool
instrumentTransferSensitivityOwned = true

transferSensitivityIsNotHistoryConstraint : Bool
transferSensitivityIsNotHistoryConstraint = true

nonzeroHistoryCouplingStillNotPredicted : Bool
nonzeroHistoryCouplingStillNotPredicted = true

pointMassTorsionEstimateIsNotFullWaferGeometryFit : Bool
pointMassTorsionEstimateIsNotFullWaferGeometryFit = true

optomechanicalTimeScalingAssumesSameStationaryNoise : Bool
optomechanicalTimeScalingAssumesSameStationaryNoise = true

existingExperimentsPreparedMatchedHistoryStates : Bool
existingExperimentsPreparedMatchedHistoryStates = false
