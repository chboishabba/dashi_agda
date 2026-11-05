{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSingleVacuumNormalizationScaleCovarianceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Foundations.GRQFTSingleVacuumSafeBandExact as Safe

------------------------------------------------------------------------
-- SINGLE-VACUUM NORMALIZATION / GEOMETRIC SCALE COVARIANCE
------------------------------------------------------------------------

rescaledVacuumAmplitude : ℚ → ℚ → ℚ
rescaledVacuumAmplitude lambda k = k * k * lambda

record InverseRadialScaleMatch (k oldRadius newRadius : ℚ) : Set where
  constructor inverse-radial-scale-match
  field
    radialScaleMatch : k * newRadius ≡ oldRadius

open InverseRadialScaleMatch public

conicQNormalizationScaleCovariant :
  ∀ lambda k oldRadius newRadius →
  InverseRadialScaleMatch k oldRadius newRadius →
  Safe.conicQ (rescaledVacuumAmplitude lambda k) newRadius
    ≡ Safe.conicQ lambda oldRadius
conicQNormalizationScaleCovariant lambda k oldRadius newRadius match
  rewrite sym (radialScaleMatch match) =
    solve-∀ lambda k newRadius

record PhysicalVacuumMultiplicativePromotion : Set where
  constructor physical-vacuum-multiplicative-promotion
  field
    sourceAmplitude : ℚ
    calibrationFactor : ℚ
    calibrationFactorPositive : 0ℚ < calibrationFactor
    physicalAmplitude : ℚ
    physicalAmplitudeDefinition :
      physicalAmplitude
        ≡ rescaledVacuumAmplitude sourceAmplitude calibrationFactor

    NoAdditiveCountertermReceipt : Set
    noAdditiveCountertermReceipt : NoAdditiveCountertermReceipt

open PhysicalVacuumMultiplicativePromotion public

record SingleVacuumNormalizationScaleBoundary : Set where
  constructor single-vacuum-normalization-scale-boundary
  field
    safeBandDependsOnDimensionlessLambdaRSquared : Bool
    multiplicativeSquareNormalizationAbsorbableIntoRadius : Bool
    positiveCalibrationIsLiteralInequality : Bool
    unknownMultiplicativeMagnitudeBlocksGeometricExistence : Bool
    unknownMultiplicativeMagnitudeStillBlocksAbsoluteDeviceSize : Bool
    additiveVacuumCountertermAbsorbedByThisTheorem : Bool
    physicalSignConventionStillRequiresSourceBackedReceipt : Bool
    SIAmplitudeNormalizationStillRequiredForDeviceDimensions : Bool

canonicalSingleVacuumNormalizationScaleBoundary :
  SingleVacuumNormalizationScaleBoundary
canonicalSingleVacuumNormalizationScaleBoundary =
  single-vacuum-normalization-scale-boundary
    true true true false true false true true
