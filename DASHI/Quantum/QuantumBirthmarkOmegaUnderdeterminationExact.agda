{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkOmegaUnderdeterminationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_)

import DASHI.Quantum.QuantumBirthmarkCommonHistoryIdentityBenchmarkExact as Birthmark
import DASHI.Quantum.QuantumBirthmarkFiniteHorizonFractionExact as Fraction

------------------------------------------------------------------------
-- THE HORIZON NORMALIZATION FIXES THE CARRIER, NOT ITS MICROSCOPIC FRACTION
------------------------------------------------------------------------

lowModelOmega :
  Fraction.historyFraction Birthmark.lowBirthmark ≡ Int.+ 1 / 4
lowModelOmega = Fraction.lowHistoryFraction

highModelOmega :
  Fraction.historyFraction Birthmark.highBirthmark ≡ Int.+ 3 / 4
highModelOmega = Fraction.highHistoryFraction

omegaNotFixedByHorizonNormalization : Bool
omegaNotFixedByHorizonNormalization = true

observedOmegaRequiresMicroscopicFraction : Bool
observedOmegaRequiresMicroscopicFraction = true

observedOmega685FollowsWithoutCalibration : Bool
observedOmega685FollowsWithoutCalibration = false

horizonCoefficientAndHistoryFractionAreSeparateInputs : Bool
horizonCoefficientAndHistoryFractionAreSeparateInputs = true
