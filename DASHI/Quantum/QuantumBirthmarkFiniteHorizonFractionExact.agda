{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkFiniteHorizonFractionExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_)

import DASHI.Quantum.QuantumBirthmarkCommonHistoryIdentityBenchmarkExact as Birthmark
import DASHI.Quantum.QuantumBirthmarkHorizonThermalCriticalScalingExact as Horizon

------------------------------------------------------------------------
-- FINITE HISTORY-FRACTION MODEL
--
-- This is a model-layer composition only.  A normalized finite history weight
-- may be used as a candidate fraction f_H of the horizon thermodynamic carrier;
-- the horizon owner then gives rho_H = f_H rho_c algebraically.  Nothing here
-- identifies the finite toy fraction with observed Omega_DE.
------------------------------------------------------------------------

historyFraction : Birthmark.BirthmarkClass → ℚ
historyFraction Birthmark.lowBirthmark = Int.+ 1 / 4
historyFraction Birthmark.highBirthmark = Int.+ 3 / 4

historyDensityCoefficient : Birthmark.BirthmarkClass → ℚ
historyDensityCoefficient birthmark =
  Horizon.historyDensityRationalCoefficient (historyFraction birthmark)

historyDensityTracksCriticalDensity :
  (birthmark : Birthmark.BirthmarkClass) →
  historyDensityCoefficient birthmark
  ≡ historyFraction birthmark * Horizon.criticalDensityRationalCoefficient
historyDensityTracksCriticalDensity birthmark =
  Horizon.historyFractionEqualsCriticalFraction (historyFraction birthmark)

lowHistoryFraction :
  historyFraction Birthmark.lowBirthmark ≡ Int.+ 1 / 4
lowHistoryFraction = refl

highHistoryFraction :
  historyFraction Birthmark.highBirthmark ≡ Int.+ 3 / 4
highHistoryFraction = refl

finiteHistoryFractionModelOwned : Bool
finiteHistoryFractionModelOwned = true

historyFractionIsNotObservedOmegaByDefinition : Bool
historyFractionIsNotObservedOmegaByDefinition = true

microscopicHistoryFractionStillRequired : Bool
microscopicHistoryFractionStillRequired = true

observedOmega685Derived : Bool
observedOmega685Derived = false
