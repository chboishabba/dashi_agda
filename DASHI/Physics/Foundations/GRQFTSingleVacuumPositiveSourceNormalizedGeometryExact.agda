{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSingleVacuumPositiveSourceNormalizedGeometryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
import Data.Integer.Base as Int
open import Relation.Binary.PropositionalEquality using (_≡_; cong; subst; sym; trans)

import DASHI.Physics.Foundations.GRQFTSingleVacuumIsraelKottlerExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

------------------------------------------------------------------------
-- GENERAL POSITIVE NORMALIZATION -> ONE EXISTING SAFE STATIC GEOMETRY
--
-- The square-rescaling theorem is useful when one already knows a physical
-- k^2 calibration.  It is not needed for normalized existence.  Given ANY
-- positive rational source amplitude lambda_s, a general positive
-- multiplicative calibration
--
--   a := (5/12) * lambda_s^{-1}
--
-- sends it exactly to the already-owned same-vacuum fixture lambda=5/12.
-- This proves normalized static geometric existence conditional on positive
-- source sign.  It deliberately does NOT identify `a` with the physical SI
-- calibration; absolute device dimensions therefore remain external.
------------------------------------------------------------------------

canonicalSafePhysicalAmplitude : ℚ
canonicalSafePhysicalAmplitude = Int.+ 5 / 12

canonicalSafePhysicalAmplitudePositive : 0ℚ < canonicalSafePhysicalAmplitude
canonicalSafePhysicalAmplitudePositive = ℚP.positive⁻¹ canonicalSafePhysicalAmplitude

positiveSourceCalibrationFactor : ℚ → ℚ
positiveSourceCalibrationFactor source =
  canonicalSafePhysicalAmplitude * Reciprocal.safeRationalReciprocal source

positiveSourceCalibrationFactorPositive :
  ∀ source → 0ℚ < source → 0ℚ < positiveSourceCalibrationFactor source
positiveSourceCalibrationFactorPositive source sourcePositive =
  let
    sourcePositiveInstance : Positive source
    sourcePositiveInstance = positive sourcePositive

    reciprocalPositiveInstance :
      Positive (Reciprocal.safeRationalReciprocal source)
    reciprocalPositiveInstance =
      Reciprocal.safeRationalReciprocalPositive source sourcePositiveInstance

    reciprocalPositive :
      0ℚ < Reciprocal.safeRationalReciprocal source
    reciprocalPositive =
      let instance _ = reciprocalPositiveInstance
      in ℚP.positive⁻¹ (Reciprocal.safeRationalReciprocal source)

    instance
      targetPositive : Positive canonicalSafePhysicalAmplitude
      targetPositive = positive canonicalSafePhysicalAmplitudePositive

    scaled :
      canonicalSafePhysicalAmplitude * 0ℚ
      < canonicalSafePhysicalAmplitude * Reciprocal.safeRationalReciprocal source
    scaled =
      ℚP.*-monoˡ-<-pos canonicalSafePhysicalAmplitude reciprocalPositive
  in
  subst
    (λ left → left < positiveSourceCalibrationFactor source)
    (Ring.solve-∀ canonicalSafePhysicalAmplitude)
    scaled

calibratedAmplitude : ℚ → ℚ
calibratedAmplitude source = positiveSourceCalibrationFactor source * source

calibratedAmplitudeIsCanonicalSafeAmplitude :
  ∀ source → 0ℚ < source →
  calibratedAmplitude source ≡ canonicalSafePhysicalAmplitude
calibratedAmplitudeIsCanonicalSafeAmplitude source sourcePositive =
  let
    sourcePositiveInstance : Positive source
    sourcePositiveInstance = positive sourcePositive

    reciprocalLaw :
      Reciprocal.safeRationalReciprocal source * source ≡ 1ℚ
    reciprocalLaw =
      Reciprocal.safeRationalReciprocalTimesPositive source sourcePositiveInstance
  in
  trans
    (Ring.solve-∀
      canonicalSafePhysicalAmplitude
      (Reciprocal.safeRationalReciprocal source)
      source)
    (trans
      (cong (λ x → canonicalSafePhysicalAmplitude * x) reciprocalLaw)
      (Ring.solve-∀ canonicalSafePhysicalAmplitude))

canonicalSafeAmplitudeMatchesFixture :
  canonicalSafePhysicalAmplitude ≡ Geometry.fixtureLambda
canonicalSafeAmplitudeMatchesFixture = sym Geometry.fixtureLambdaIsFiveTwelfths

canonicalSafeMassPositive : 0ℚ < Geometry.fixtureMass
canonicalSafeMassPositive =
  subst
    (λ x → 0ℚ < x)
    (sym Geometry.fixtureMassIsNineteenTwoTwentyFifths)
    (ℚP.positive⁻¹ (Int.+ 19 / 225))

canonicalSafeOutwardAccelerationPositive :
  0ℚ < Geometry.sameVacuumOutwardScaled
    Geometry.fixtureRadius Geometry.fixtureX Geometry.fixtureY
canonicalSafeOutwardAccelerationPositive =
  subst
    (λ x → 0ℚ < x)
    (sym Geometry.fixtureOutwardScaledIsSeventySevenSeventyFifths)
    (ℚP.positive⁻¹ (Int.+ 77 / 75))

canonicalSafeNECDECMarginPositive :
  0ℚ < Geometry.sameVacuumNECDECMargin
    Geometry.fixtureRadius Geometry.fixtureX Geometry.fixtureY
canonicalSafeNECDECMarginPositive =
  subst
    (λ x → 0ℚ < x)
    (sym Geometry.fixtureNECDECMarginIsEightTwoTwentyFifths)
    (ℚP.positive⁻¹ (Int.+ 8 / 225))

canonicalSafeSECViolationMarginPositive :
  0ℚ < Geometry.sameVacuumSECViolationMargin
    Geometry.fixtureRadius Geometry.fixtureX Geometry.fixtureY
canonicalSafeSECViolationMarginPositive =
  subst
    (λ x → 0ℚ < x)
    (sym Geometry.fixtureSECViolationMarginIsFourTwoTwentyFifths)
    (ℚP.positive⁻¹ (Int.+ 4 / 225))

record PositiveSourceNormalizedStaticGeometry (sourceAmplitude : ℚ) : Set where
  constructor positive-source-normalized-static-geometry
  field
    sourcePositive : 0ℚ < sourceAmplitude
    calibrationFactor : ℚ
    calibrationPositive : 0ℚ < calibrationFactor
    physicalAmplitude : ℚ
    physicalAmplitudeIsCalibrated :
      physicalAmplitude ≡ calibrationFactor * sourceAmplitude
    physicalAmplitudeIsSafeFixture :
      physicalAmplitude ≡ Geometry.fixtureLambda
    radius interiorLapseRoot exteriorLapseRoot : ℚ
    geometryIsCanonicalFixture :
      radius ≡ Geometry.fixtureRadius
    interiorRootIsCanonicalFixture :
      interiorLapseRoot ≡ Geometry.fixtureX
    exteriorRootIsCanonicalFixture :
      exteriorLapseRoot ≡ Geometry.fixtureY
    positiveMetricMass : 0ℚ < Geometry.fixtureMass
    outwardAccelerationPositive :
      0ℚ < Geometry.sameVacuumOutwardScaled
        Geometry.fixtureRadius Geometry.fixtureX Geometry.fixtureY
    necDecCompatible :
      0ℚ < Geometry.sameVacuumNECDECMargin
        Geometry.fixtureRadius Geometry.fixtureX Geometry.fixtureY
    secViolated :
      0ℚ < Geometry.sameVacuumSECViolationMargin
        Geometry.fixtureRadius Geometry.fixtureX Geometry.fixtureY

positiveSourceHasNormalizedStaticGeometry :
  ∀ sourceAmplitude → 0ℚ < sourceAmplitude →
  PositiveSourceNormalizedStaticGeometry sourceAmplitude
positiveSourceHasNormalizedStaticGeometry sourceAmplitude sourcePositive =
  positive-source-normalized-static-geometry
    sourcePositive
    (positiveSourceCalibrationFactor sourceAmplitude)
    (positiveSourceCalibrationFactorPositive sourceAmplitude sourcePositive)
    (calibratedAmplitude sourceAmplitude)
    refl
    (trans
      (calibratedAmplitudeIsCanonicalSafeAmplitude sourceAmplitude sourcePositive)
      canonicalSafeAmplitudeMatchesFixture)
    Geometry.fixtureRadius Geometry.fixtureX Geometry.fixtureY
    refl refl refl
    canonicalSafeMassPositive
    canonicalSafeOutwardAccelerationPositive
    canonicalSafeNECDECMarginPositive
    canonicalSafeSECViolationMarginPositive

record PositiveSourceNormalizedGeometryBoundary : Set where
  constructor positive-source-normalized-geometry-boundary
  field
    arbitraryPositiveRationalSourceHasNormalizedStaticGeometry : Bool
    rationalSquareDensityTheoremRequired : Bool
    physicalCalibrationValueStillExternal : Bool
    absoluteSIDeviceScaleStillExternal : Bool
    positiveSourceSignStillRequired : Bool

canonicalPositiveSourceNormalizedGeometryBoundary :
  PositiveSourceNormalizedGeometryBoundary
canonicalPositiveSourceNormalizedGeometryBoundary =
  positive-source-normalized-geometry-boundary true false true true true

physicalCalibrationValueStillExternal : Bool
physicalCalibrationValueStillExternal = true
