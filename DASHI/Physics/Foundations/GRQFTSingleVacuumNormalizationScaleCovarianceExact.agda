{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSingleVacuumNormalizationScaleCovarianceExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve-∀)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Foundations.GRQFTSingleVacuumSafeBandExact as Safe

------------------------------------------------------------------------
-- SINGLE-VACUUM NORMALIZATION / GEOMETRIC SCALE COVARIANCE
--
-- The source-to-metric promotion may carry an unknown positive multiplicative
-- normalization.  The single-vacuum safe-band geometry depends on the
-- dimensionless combination
--
--   q = Lambda R^2.
--
-- If a calibration rescales Lambda by k^2 while the physical radial parameter
-- is rescaled inversely (k * R' = R), q is unchanged.  We encode the statement
-- without division or square roots, so it is exact in the rational lane.
--
-- This does NOT absorb an additive vacuum/cosmological counterterm and does
-- NOT prove that the action coefficient is already the physical Lambda.  It
-- proves only that an unknown nonzero multiplicative magnitude, once its sign
-- and multiplicative character are physically justified, fixes device scale
-- rather than destroying existence of the safe-band geometry.
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
    physicalAmplitude : ℚ
    physicalAmplitudeDefinition :
      physicalAmplitude
        ≡ rescaledVacuumAmplitude sourceAmplitude calibrationFactor

    PositiveCalibrationReceipt : Set
    positiveCalibrationReceipt : PositiveCalibrationReceipt

    NoAdditiveCountertermReceipt : Set
    noAdditiveCountertermReceipt : NoAdditiveCountertermReceipt

open PhysicalVacuumMultiplicativePromotion public

record SingleVacuumNormalizationScaleBoundary : Set where
  constructor single-vacuum-normalization-scale-boundary
  field
    safeBandDependsOnDimensionlessLambdaRSquared : Bool
    multiplicativeSquareNormalizationAbsorbableIntoRadius : Bool
    unknownMultiplicativeMagnitudeBlocksGeometricExistence : Bool
    unknownMultiplicativeMagnitudeStillBlocksAbsoluteDeviceSize : Bool
    additiveVacuumCountertermAbsorbedByThisTheorem : Bool
    physicalSignConventionStillRequiresSourceBackedReceipt : Bool
    SIAmplitudeNormalizationStillRequiredForDeviceDimensions : Bool

canonicalSingleVacuumNormalizationScaleBoundary :
  SingleVacuumNormalizationScaleBoundary
canonicalSingleVacuumNormalizationScaleBoundary =
  single-vacuum-normalization-scale-boundary
    true true false true false true true
