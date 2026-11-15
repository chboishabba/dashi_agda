{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTVacuumAmplitudeDifferentialRenormalizationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)

------------------------------------------------------------------------
-- DIFFERENTIAL VACUUM-AMPLITUDE RENORMALIZATION
------------------------------------------------------------------------

physicalVacuumAmplitude : ℚ → ℚ → ℚ → ℚ
physicalVacuumAmplitude multiplicative sourceAmplitude additive =
  multiplicative * sourceAmplitude + additive

commonCountertermCancelsInDifference :
  ∀ multiplicative source0 source1 additive →
  physicalVacuumAmplitude multiplicative source1 additive
    - physicalVacuumAmplitude multiplicative source0 additive
  ≡ multiplicative * (source1 - source0)
commonCountertermCancelsInDifference = solve-∀

record CommonCountertermVacuumModulation : Set where
  constructor common-counterterm-vacuum-modulation
  field
    multiplicative : ℚ
    multiplicativePositive : 0ℚ < multiplicative
    sourceOff : ℚ
    sourceOn : ℚ
    additiveCounterterm : ℚ

    StateIndependentCountertermReceipt : Set
    stateIndependentCountertermReceipt : StateIndependentCountertermReceipt

open CommonCountertermVacuumModulation public

physicalVacuumDifference : CommonCountertermVacuumModulation → ℚ
physicalVacuumDifference modulation =
  physicalVacuumAmplitude
    (multiplicative modulation)
    (sourceOn modulation)
    (additiveCounterterm modulation)
  - physicalVacuumAmplitude
      (multiplicative modulation)
      (sourceOff modulation)
      (additiveCounterterm modulation)

physicalVacuumDifferenceIsMultiplicativeSourceDifference :
  ∀ modulation →
  physicalVacuumDifference modulation
  ≡ multiplicative modulation * (sourceOn modulation - sourceOff modulation)
physicalVacuumDifferenceIsMultiplicativeSourceDifference modulation =
  commonCountertermCancelsInDifference
    (multiplicative modulation)
    (sourceOff modulation)
    (sourceOn modulation)
    (additiveCounterterm modulation)

record DifferentialVacuumRenormalizationBoundary : Set where
  constructor differential-vacuum-renormalization-boundary
  field
    commonAdditiveCountertermCancelsExactly : Bool
    positiveMultiplicativeCalibrationIsLiteralInequality : Bool
    absoluteStaticLambdaRecoveredFromDifference : Bool
    modulatedVacuumDifferenceNeedsAbsoluteAdditiveZero : Bool
    stateIndependentCountertermStillNeedsPhysicalReceipt : Bool
    multiplicativeCalibrationStillNeededForAbsoluteDeltaLambda : Bool
    sourceDifferenceCanDriveLockInLaneModuloCalibration : Bool

canonicalDifferentialVacuumRenormalizationBoundary :
  DifferentialVacuumRenormalizationBoundary
canonicalDifferentialVacuumRenormalizationBoundary =
  differential-vacuum-renormalization-boundary
    true true false false true true true
