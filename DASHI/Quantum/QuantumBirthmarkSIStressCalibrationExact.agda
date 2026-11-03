{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkSIStressCalibrationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([])
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

------------------------------------------------------------------------
-- SI CALIBRATION / TRANSFER, NOT A PARAMETER-FREE PREDICTION
--
-- Local Python with H0=67.4 km s^-1 Mpc^-1 and CODATA-2022
-- G=6.67430e-11 m^3 kg^-1 s^-2 gives
--
--   rho_c = 8.532855...e-27 kg m^-3.
--
-- Store the 6-decimal coefficient 8.532855 in units 1e-27 kg m^-3.
-- With the existing observational calibration f_H = 0.685 = 137/200,
-- the transferred history density is 5.845005675e-27 kg m^-3.
------------------------------------------------------------------------

criticalDensityReferenceEminus27 : ℚ
criticalDensityReferenceEminus27 = Int.+ 8532855 / 1000000

calibratedHistoryFraction : ℚ
calibratedHistoryFraction = Int.+ 137 / 200

calibratedHistoryDensityEminus27 : ℚ
calibratedHistoryDensityEminus27 =
  calibratedHistoryFraction * criticalDensityReferenceEminus27

calibratedHistoryDensityIsReferenceFraction :
  calibratedHistoryDensityEminus27
  ≡ Int.+ 233800227 / 40000000
calibratedHistoryDensityIsReferenceFraction = solve []

siMagnitudeTransferOwned : Bool
siMagnitudeTransferOwned = true

hubbleReferenceIsCalibrationInput : Bool
hubbleReferenceIsCalibrationInput = true

historyFractionIsCalibrationInput : Bool
historyFractionIsCalibrationInput = true

sourceNativeMagnitudePredictionStillRequired : Bool
sourceNativeMagnitudePredictionStillRequired = true

codataGReference : Bool
codataGReference = true

parameterFreeDarkEnergyDensityDerived : Bool
parameterFreeDarkEnergyDensityDerived = false
