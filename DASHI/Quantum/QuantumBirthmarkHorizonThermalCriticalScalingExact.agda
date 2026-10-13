{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHorizonThermalCriticalScalingExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 1ℚ; _/_; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

------------------------------------------------------------------------
-- HORIZON THERMODYNAMIC NORMALIZATION OF THE H^2 MODEL
--
-- Strip the common dimensional factors pi, G and powers of H and retain their
-- exact rational coefficients:
--
--   T_H         = (1/2) * H/pi
--   S_H         = 1 * pi/(G H^2)
--   1/V_H       = (3/4) * H^3/pi
--
-- Therefore T_H S_H / V_H has rational coefficient
--   (1/2) * 1 * (3/4) = 3/8
-- and H exponent 1 + (-2) + 3 = 2.
-- Reattaching the common factor 1/(pi G) gives
--   rho = 3 H^2/(8 pi G),
-- exactly the standard flat critical-density coefficient.
--
-- A history-sector fraction f_H of this thermodynamic carrier therefore has
-- rho_H = f_H rho_c and hence Omega_H = f_H algebraically.  The microscopic
-- theory still has to derive f_H; this module does not identify Landauer cost
-- with gravitational energy by definition.
------------------------------------------------------------------------

temperatureCoefficient : ℚ
temperatureCoefficient = Int.+ 1 / 2

entropyCoefficient : ℚ
entropyCoefficient = 1ℚ

inverseVolumeCoefficient : ℚ
inverseVolumeCoefficient = Int.+ 3 / 4

horizonThermalCoefficient : ℚ
horizonThermalCoefficient =
  temperatureCoefficient * entropyCoefficient * inverseVolumeCoefficient

horizonThermalCoefficientIsThreeEighths :
  horizonThermalCoefficient ≡ Int.+ 3 / 8
horizonThermalCoefficientIsThreeEighths = solve []

temperatureHubbleExponent : ℚ
temperatureHubbleExponent = 1ℚ

entropyHubbleExponent : ℚ
entropyHubbleExponent = - (Int.+ 2 / 1)

inverseVolumeHubbleExponent : ℚ
inverseVolumeHubbleExponent = Int.+ 3 / 1

horizonThermalHubbleExponent : ℚ
horizonThermalHubbleExponent =
  temperatureHubbleExponent
  + entropyHubbleExponent
  + inverseVolumeHubbleExponent

horizonThermalHubbleExponentIsTwo :
  horizonThermalHubbleExponent ≡ Int.+ 2 / 1
horizonThermalHubbleExponentIsTwo = solve []

criticalDensityRationalCoefficient : ℚ
criticalDensityRationalCoefficient = Int.+ 3 / 8

historyDensityRationalCoefficient : ℚ → ℚ
historyDensityRationalCoefficient historyFraction =
  historyFraction * horizonThermalCoefficient

historyFractionEqualsCriticalFraction :
  (historyFraction : ℚ) →
  historyDensityRationalCoefficient historyFraction
  ≡ historyFraction * criticalDensityRationalCoefficient
historyFractionEqualsCriticalFraction historyFraction =
  solve (historyFraction ∷ [])

horizonThermalHubbleScalingOwned : Bool
horizonThermalHubbleScalingOwned = true

criticalDensityNormalizationRecoveredAtCoefficientLevel : Bool
criticalDensityNormalizationRecoveredAtCoefficientLevel = true

historyFractionStillMicroscopicInput : Bool
historyFractionStillMicroscopicInput = true

observedOmegaDerivedFromBirthmarkDynamics : Bool
observedOmegaDerivedFromBirthmarkDynamics = false

landauerConverseUsedAsTheorem : Bool
landauerConverseUsedAsTheorem = false

horizonThermodynamicInterpretationIsPhysicalInput : Bool
horizonThermodynamicInterpretationIsPhysicalInput = true
