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
--
-- Source inputs: m = 7.6 mg for each body, closest separation 0.654 mm,
-- maximum quoted uncertainty 50 aN (2 sigma).
--
-- Local Python using CODATA G and a point-mass approximation gives
--   F_N = 9013.166867... aN.
-- We store the rounded 0.001 aN value below.  The actual silicon-wafer
-- experiment uses its physical geometry; this point-mass number is therefore a
-- sensitivity-transfer estimate, not a re-analysis of its fitted G.
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
--
-- a = 33.3 +/- 5.6_stat +/- 2.7_syst nm s^-2.
-- The exact squared one-sigma fractional uncertainty is
--
--   (5.6^2 + 2.7^2) / 33.3^2
-- = (56^2 + 27^2) / 333^2
-- = 3865 / 110889.
--
-- Local Python gives sqrt(...) = 0.186694..., hence about 0.373388 at 2 sigma.
------------------------------------------------------------------------

atomOneSigmaFractionalTransferSquared : ℚ
atomOneSigmaFractionalTransferSquared = Int.+ 3865 / 110889

atomOneSigmaFractionalTransferSquaredDefinition :
  atomOneSigmaFractionalTransferSquared ≡ Int.+ 3865 / 110889
atomOneSigmaFractionalTransferSquaredDefinition = refl

------------------------------------------------------------------------
-- 2026 QUANTUM-READY OPTOMECHANICAL SCALING
--
-- The source paper reports unit-SNR detection of the FULL Newtonian gravity
-- signal in a range from minutes to approximately 15 hours depending on source
-- drive.  If a history-only signal is epsilon_H times that full signal while
-- the same stationary noise dominates, required integration time scales as
-- epsilon_H^-2.  We use the conservative 15 h endpoint below.
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
