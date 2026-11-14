{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.AntigravityStressLengthSquaredTargetIntervalExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; _<_; Positive; NonNegative)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Foundations.CMP119AntigravityPhysicalEinsteinCalibrationExact as Physical
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quotient

------------------------------------------------------------------------
-- P2 / REQUIRED STRESS*LENGTH^2 TARGET INTERVAL
--
-- The physical Einstein coupling remains a measured/transcendental quantity
-- represented by an accepted interval.  This owner does NOT replace it by a
-- rational value.  It closes only the exact rational interval algebra:
--
-- for any rational diagnostic kappa point inside the accepted enclosure and
-- positive source magnitude C, the product S_L2 required to hit target Lambda
-- is
--
--       S_L2 = Lambda / (kappa * C),
--
-- and therefore lies between the endpoint quotients
--
--       Lambda / (kappa_upper * C)
--       Lambda / (kappa_lower * C).
--
-- Hence the remaining P2 datum is empirical/same-apparatus: identify or
-- measure the actual source/device stress*length^2 product.  No unresolved
-- reciprocal/order algebra should be counted as physical progress.
------------------------------------------------------------------------

record RationalKappaPoint
    (interval : Physical.PhysicalEinsteinCouplingInterval) : Set where
  field
    value : ℚ
    lowerSound : Physical.lower interval ≤ value
    upperSound : value ≤ Physical.upper interval

open RationalKappaPoint public

module _
    (interval : Physical.PhysicalEinsteinCouplingInterval)
    (sourceMagnitude targetAmplitude : ℚ)
    (sourcePositive : 0ℚ < sourceMagnitude)
    (targetNonnegative : 0ℚ ≤ targetAmplitude)
  where

  sourceNonnegative : NonNegative sourceMagnitude
  sourceNonnegative = ℚ.nonNegative (ℚP.<⇒≤ sourcePositive)

  denominatorLower : ℚ
  denominatorLower = Physical.lower interval * sourceMagnitude

  denominatorUpper : ℚ
  denominatorUpper = Physical.upper interval * sourceMagnitude

  denominatorLowerPositive : 0ℚ < denominatorLower
  denominatorLowerPositive =
    let
      instance lowerPositive : Positive (Physical.lower interval)
      lowerPositive = ℚ.positive (Physical.lowerPositive interval)

      instance sourceIsPositive : Positive sourceMagnitude
      sourceIsPositive = ℚ.positive sourcePositive

      instance productPositive : Positive denominatorLower
      productPositive =
        ℚP.pos*pos⇒pos (Physical.lower interval) sourceMagnitude
    in
    ℚP.positive⁻¹ denominatorLower

  denominatorOrdered : denominatorLower ≤ denominatorUpper
  denominatorOrdered =
    let instance sourceNN : NonNegative sourceMagnitude
        sourceNN = sourceNonnegative
    in
    ℚP.*-monoʳ-≤-nonNeg sourceMagnitude (Physical.ordered interval)

  denominatorUpperPositive : 0ℚ < denominatorUpper
  denominatorUpperPositive =
    Quotient.upperDenominatorPositive
      denominatorLower denominatorUpper
      denominatorLowerPositive denominatorOrdered

  targetSignCase : Quotient.NumeratorSignCase targetAmplitude targetAmplitude
  targetSignCase = Quotient.numeratorNonnegative targetNonnegative

  requiredStressLengthSquaredLower : ℚ
  requiredStressLengthSquaredLower =
    Quotient.quotientLowerEndpoint
      targetSignCase
      denominatorLower denominatorUpper
      denominatorLowerPositive denominatorOrdered

  requiredStressLengthSquaredUpper : ℚ
  requiredStressLengthSquaredUpper =
    Quotient.quotientUpperEndpoint
      targetSignCase
      denominatorLower denominatorUpper
      denominatorLowerPositive denominatorOrdered

  actualDenominator : RationalKappaPoint interval → ℚ
  actualDenominator point = value point * sourceMagnitude

  actualDenominatorPositive :
    (point : RationalKappaPoint interval) →
    0ℚ < actualDenominator point
  actualDenominatorPositive point =
    ℚP.<-≤-trans
      denominatorLowerPositive
      (let instance sourceNN : NonNegative sourceMagnitude
           sourceNN = sourceNonnegative
       in ℚP.*-monoʳ-≤-nonNeg sourceMagnitude (lowerSound point))

  requiredStressLengthSquaredAt : RationalKappaPoint interval → ℚ
  requiredStressLengthSquaredAt point =
    Quotient.dividePositive
      targetAmplitude
      (actualDenominator point)
      (actualDenominatorPositive point)

  requiredStressLengthSquaredEnclosed :
    (point : RationalKappaPoint interval) →
    Quotient.LiesBetween
      requiredStressLengthSquaredLower
      (requiredStressLengthSquaredAt point)
      requiredStressLengthSquaredUpper
  requiredStressLengthSquaredEnclosed point =
    Quotient.positiveDenominatorQuotientEnclosure
      targetSignCase
      denominatorLowerPositive
      denominatorOrdered
      ℚP.≤-refl
      ℚP.≤-refl
      (let instance sourceNN : NonNegative sourceMagnitude
           sourceNN = sourceNonnegative
       in ℚP.*-monoʳ-≤-nonNeg sourceMagnitude (lowerSound point))
      (let instance sourceNN : NonNegative sourceMagnitude
           sourceNN = sourceNonnegative
       in ℚP.*-monoʳ-≤-nonNeg sourceMagnitude (upperSound point))

remainingP2DatumIsSameApparatusStressLengthSquaredProduct : Bool
remainingP2DatumIsSameApparatusStressLengthSquaredProduct = true

rationalPointDiagnosticPromotesMeasuredKappaToExact : Bool
rationalPointDiagnosticPromotesMeasuredKappaToExact = false

remainingP2DatumIsSameApparatusStressLengthSquaredProductIsTrue :
  remainingP2DatumIsSameApparatusStressLengthSquaredProduct ≡ true
remainingP2DatumIsSameApparatusStressLengthSquaredProductIsTrue = refl

rationalPointDiagnosticPromotesMeasuredKappaToExactIsFalse :
  rationalPointDiagnosticPromotesMeasuredKappaToExact ≡ false
rationalPointDiagnosticPromotesMeasuredKappaToExactIsFalse = refl
