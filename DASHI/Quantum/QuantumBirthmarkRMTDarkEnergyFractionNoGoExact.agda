{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkRMTDarkEnergyFractionNoGoExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using ([])
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

------------------------------------------------------------------------
-- NUMERICAL-SEMANTIC FIREWALL
--
-- A tempting but unjustified map is to turn the universal birthmark enhancement
-- B into an "excess fraction" (B-1)/B.  At large N this gives 1/2 for the
-- no-TRS/GUE-like factor B=2 and 2/3 for the TRS/GOE-like factor B=3.
-- Neither equality is a physical theorem relating return statistics to energy.
-- Moreover the GOE number does not equal the 0.685 calibration.
------------------------------------------------------------------------

gueLargeNExcessFraction : ℚ
gueLargeNExcessFraction = Int.+ 1 / 2

goeLargeNExcessFraction : ℚ
goeLargeNExcessFraction = Int.+ 2 / 3

observedCalibrationFraction : ℚ
observedCalibrationFraction = Int.+ 137 / 200

goeToObservedGap : ℚ
goeToObservedGap = observedCalibrationFraction - goeLargeNExcessFraction

goeToObservedGapIsElevenSixHundredths :
  goeToObservedGap ≡ Int.+ 11 / 600
goeToObservedGapIsElevenSixHundredths = solve []

-- For N=100, beta_N=3N/(N+2)=50/17 and (beta_N-1)/beta_N=33/50.
goeFiniteN100ExcessFraction : ℚ
goeFiniteN100ExcessFraction = Int.+ 33 / 50

goeFiniteN100BelowLargeN :
  goeLargeNExcessFraction - goeFiniteN100ExcessFraction
  ≡ Int.+ 1 / 150
goeFiniteN100BelowLargeN = solve []

finiteNCorrectionMovesBelowTwoThirds : Bool
finiteNCorrectionMovesBelowTwoThirds = true

rmtEnhancementCannotBeIdentifiedWithOmegaByThisNaiveMap : Bool
rmtEnhancementCannotBeIdentifiedWithOmegaByThisNaiveMap = true

returnProbabilityEnhancementIsEnergyFractionByDefinition : Bool
returnProbabilityEnhancementIsEnergyFractionByDefinition = false

parameterFreeOmegaStillRequiresPhysicalMap : Bool
parameterFreeOmegaStillRequiresPhysicalMap = true
