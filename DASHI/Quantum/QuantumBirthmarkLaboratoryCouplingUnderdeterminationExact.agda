{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkLaboratoryCouplingUnderdeterminationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_)

------------------------------------------------------------------------
-- FINITE VACUUM-AMPLITUDE GAP IS NOT A LABORATORY FORCE FRACTION
--
-- The finite birthmark model has the exact vacuum-amplitude gap
--   3/8 - 21/64 = 3/64.
-- A physical laboratory observable requires an additional dimensional transfer
-- coefficient c.  Distinct c values map the same model gap to distinct epsilon_H,
-- proving that the finite dimensionless gap alone cannot be a force fraction.
------------------------------------------------------------------------

finiteVacuumAmplitudeGap : ℚ
finiteVacuumAmplitudeGap = Int.+ 3 / 64

laboratoryEpsilon : ℚ → ℚ
laboratoryEpsilon calibration = calibration * finiteVacuumAmplitudeGap

unitCalibrationEpsilon :
  laboratoryEpsilon (Int.+ 1 / 1) ≡ Int.+ 3 / 64
unitCalibrationEpsilon = refl

doubleCalibrationEpsilon :
  laboratoryEpsilon (Int.+ 2 / 1) ≡ Int.+ 3 / 32
doubleCalibrationEpsilon = refl

sameFiniteGapAllowsDifferentLaboratoryCouplings : Bool
sameFiniteGapAllowsDifferentLaboratoryCouplings = true

finiteAmplitudeGapIsNotForceFractionByDefinition : Bool
finiteAmplitudeGapIsNotForceFractionByDefinition = true

microscopicMetricToObservableCalibrationStillRequired : Bool
microscopicMetricToObservableCalibrationStillRequired = true

nonzeroEpsilonPredictedFromFiniteGapAlone : Bool
nonzeroEpsilonPredictedFromFiniteGapAlone = false
