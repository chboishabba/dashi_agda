{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkDarkEnergyCalibrationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 1ℚ; _/_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Quantum.QuantumBirthmarkHistoryHorizonScalingExact as Horizon

------------------------------------------------------------------------
-- OBSERVATIONAL CALIBRATION FIXTURE -- NOT A PARAMETER-FREE PREDICTION
--
-- PDG 2025 reference cosmology quotes Omega_Lambda = 0.685(7) and
-- rho_Lambda = 5.83(16)e-30 g cm^-3.  We use the central Omega value as a
-- calibration target for the phenomenological H^2 tracking carrier.
------------------------------------------------------------------------

observedOmegaLambdaCentral : ℚ
observedOmegaLambdaCentral = Int.+ 137 / 200

calibratedAlpha : ℚ
calibratedAlpha = observedOmegaLambdaCentral

calibratedBeta : ℚ
calibratedBeta = 1ℚ

calibratedHistoryDensity : ℚ → ℚ
calibratedHistoryDensity hubble =
  Horizon.historyDensity calibratedAlpha hubble

calibratedCriticalDensityCarrier : ℚ → ℚ
calibratedCriticalDensityCarrier hubble =
  Horizon.criticalDensityCarrier calibratedBeta hubble

calibratedTrackingCrossProduct :
  (hubble : ℚ) →
  calibratedBeta * calibratedHistoryDensity hubble
  ≡
  calibratedAlpha * calibratedCriticalDensityCarrier hubble
calibratedTrackingCrossProduct hubble =
  Horizon.horizonTrackingCrossProduct calibratedAlpha calibratedBeta hubble

calibratedFractionCentralValue :
  calibratedAlpha ≡ Int.+ 137 / 200
calibratedFractionCentralValue = refl

------------------------------------------------------------------------
-- Source metadata and epistemic status.
------------------------------------------------------------------------

pdgOmegaLambdaSource : String
pdgOmegaLambdaSource =
  "Particle Data Group astrophysical constants/parameters: Omega_Lambda = 0.685(7)"

pdgDarkEnergyDensitySource : String
pdgDarkEnergyDensitySource =
  "Particle Data Group: rho_Lambda = 5.83(16)e-30 g cm^-3 = 5.83(16)e-27 kg m^-3"

observationalFractionCalibrationOwned : Bool
observationalFractionCalibrationOwned = true

observationalMassDensityCalibrationRecorded : Bool
observationalMassDensityCalibrationRecorded = true

parameterFreeOmegaPredictionOwned : Bool
parameterFreeOmegaPredictionOwned = false

microscopicAlphaDerivationOwned : Bool
microscopicAlphaDerivationOwned = false

calibrationIsNotCoincidenceSolution : Bool
calibrationIsNotCoincidenceSolution = true
