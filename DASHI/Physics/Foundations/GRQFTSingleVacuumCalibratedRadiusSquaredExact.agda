{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSingleVacuumCalibratedRadiusSquaredExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _/_; _*_; _<_; Positive; positive)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Foundations.GRQFTSingleVacuumIsraelKottlerExact as Geometry
import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

------------------------------------------------------------------------
-- PHYSICAL LAMBDA -> DIMENSIONED RADIUS-SQUARED TARGET
--
-- The canonical same-vacuum fixture already satisfies
--
--   Lambda R^2 = (5/12) * 2^2 = 5/3.
--
-- Once a positive physical cosmological amplitude is supplied in a declared
-- inverse-area unit, the exact target AREA is therefore
--
--   R^2 = (5/3) / Lambda.
--
-- We deliberately compile R^2 rather than R.  This removes an irrelevant
-- square-root/rationality obstruction: the Kottler equations use Lambda R^2,
-- and a physical metrology layer may later choose an appropriate real-valued
-- square-root representation.  The theorem below fixes the dimension and exact
-- rational magnitude relation; it does NOT manufacture a metre-scale decimal
-- calibration for the supplied physical Lambda.
------------------------------------------------------------------------

canonicalFixtureQ : ℚ
canonicalFixtureQ =
  Geometry.fixtureLambda * Geometry.fixtureRadius * Geometry.fixtureRadius

canonicalFixtureQIsFiveThirds :
  canonicalFixtureQ ≡ Int.+ 5 / 3
canonicalFixtureQIsFiveThirds = Ring.solve []

canonicalFixtureQPositive : 0ℚ < canonicalFixtureQ
canonicalFixtureQPositive =
  subst
    (λ q → 0ℚ < q)
    (sym canonicalFixtureQIsFiveThirds)
    (ℚP.positive⁻¹ (Int.+ 5 / 3))

physicalLambdaQuantity : ℚ → Dim.Quantity ℚ Dim.inverseAreaDimension
physicalLambdaQuantity = Dim.quantity

radiusSquaredQuantity : ℚ → Dim.Quantity ℚ Dim.areaDimension
radiusSquaredQuantity = Dim.quantity

radiusSquaredFromPhysicalLambda :
  Dim.Quantity ℚ Dim.inverseAreaDimension →
  Dim.Quantity ℚ Dim.areaDimension
radiusSquaredFromPhysicalLambda lambda =
  Dim.quantity
    (canonicalFixtureQ
      * Reciprocal.safeRationalReciprocal (Dim.magnitude lambda))

inverseAreaTimesAreaIsDimensionless :
  Dim.inverseAreaDimension Dim.⊗ᴰ Dim.areaDimension ≡ Dim.dimensionless
inverseAreaTimesAreaIsDimensionless = refl

lambdaTimesRadiusSquaredIsCanonicalQ :
  ∀ lambda →
  0ℚ < Dim.magnitude lambda →
  Dim.magnitude lambda
    * Dim.magnitude (radiusSquaredFromPhysicalLambda lambda)
  ≡ canonicalFixtureQ
lambdaTimesRadiusSquaredIsCanonicalQ lambda lambdaPositive =
  let
    magnitude = Dim.magnitude lambda
    magnitudePositiveInstance : Positive magnitude
    magnitudePositiveInstance = positive lambdaPositive

    reciprocalLaw :
      Reciprocal.safeRationalReciprocal magnitude * magnitude ≡ 1ℚ
    reciprocalLaw =
      Reciprocal.safeRationalReciprocalTimesPositive
        magnitude magnitudePositiveInstance
  in
  trans
    (Ring.solve-∀
      canonicalFixtureQ
      magnitude
      (Reciprocal.safeRationalReciprocal magnitude))
    (trans
      (cong (λ x → canonicalFixtureQ * x) reciprocalLaw)
      (Ring.solve-∀ canonicalFixtureQ))

radiusSquaredFromPositiveLambdaIsPositive :
  ∀ lambda →
  0ℚ < Dim.magnitude lambda →
  0ℚ < Dim.magnitude (radiusSquaredFromPhysicalLambda lambda)
radiusSquaredFromPositiveLambdaIsPositive lambda lambdaPositive =
  let
    magnitude = Dim.magnitude lambda
    magnitudePositiveInstance : Positive magnitude
    magnitudePositiveInstance = positive lambdaPositive

    reciprocalPositiveInstance :
      Positive (Reciprocal.safeRationalReciprocal magnitude)
    reciprocalPositiveInstance =
      Reciprocal.safeRationalReciprocalPositive
        magnitude magnitudePositiveInstance

    reciprocalPositive :
      0ℚ < Reciprocal.safeRationalReciprocal magnitude
    reciprocalPositive =
      let instance _ = reciprocalPositiveInstance
      in ℚP.positive⁻¹ (Reciprocal.safeRationalReciprocal magnitude)

    instance
      qPositive : Positive canonicalFixtureQ
      qPositive = positive canonicalFixtureQPositive

    scaled :
      canonicalFixtureQ * 0ℚ
      < canonicalFixtureQ * Reciprocal.safeRationalReciprocal magnitude
    scaled =
      ℚP.*-monoˡ-<-pos canonicalFixtureQ reciprocalPositive
  in
  subst
    (λ left →
      left
      < Dim.magnitude (radiusSquaredFromPhysicalLambda lambda))
    (Ring.solve-∀ canonicalFixtureQ)
    scaled

record CalibratedRadiusSquaredTarget : Set where
  constructor calibrated-radius-squared-target
  field
    physicalLambda : Dim.Quantity ℚ Dim.inverseAreaDimension
    physicalLambdaPositive : 0ℚ < Dim.magnitude physicalLambda
    radiusSquared : Dim.Quantity ℚ Dim.areaDimension
    radiusSquaredDefinition :
      radiusSquared ≡ radiusSquaredFromPhysicalLambda physicalLambda
    lambdaRadiusSquaredProduct :
      Dim.magnitude physicalLambda * Dim.magnitude radiusSquared
      ≡ canonicalFixtureQ
    radiusSquaredPositive : 0ℚ < Dim.magnitude radiusSquared

calibratedRadiusSquaredTarget :
  (lambda : Dim.Quantity ℚ Dim.inverseAreaDimension) →
  0ℚ < Dim.magnitude lambda →
  CalibratedRadiusSquaredTarget
calibratedRadiusSquaredTarget lambda lambdaPositive =
  calibrated-radius-squared-target
    lambda
    lambdaPositive
    (radiusSquaredFromPhysicalLambda lambda)
    refl
    (lambdaTimesRadiusSquaredIsCanonicalQ lambda lambdaPositive)
    (radiusSquaredFromPositiveLambdaIsPositive lambda lambdaPositive)

record CalibratedRadiusSquaredBoundary : Set where
  constructor calibrated-radius-squared-boundary
  field
    canonicalFixtureDimensionlessQOwned : Bool
    positivePhysicalLambdaDeterminesRadiusSquaredTarget : Bool
    squareRootNotRequiredForRadiusSquaredTarget : Bool
    inverseAreaTimesAreaDimensionless : Bool
    absoluteSIDecimalScaleStillRequiresReceipt : Bool
    physicalLambdaCalibrationManufacturedByThisModule : Bool

canonicalCalibratedRadiusSquaredBoundary : CalibratedRadiusSquaredBoundary
canonicalCalibratedRadiusSquaredBoundary =
  calibrated-radius-squared-boundary
    true true true true true false

squareRootNotRequiredForRadiusSquaredTarget : Bool
squareRootNotRequiredForRadiusSquaredTarget = true

absoluteSIDecimalScaleStillRequiresReceipt : Bool
absoluteSIDecimalScaleStillRequiresReceipt = true
