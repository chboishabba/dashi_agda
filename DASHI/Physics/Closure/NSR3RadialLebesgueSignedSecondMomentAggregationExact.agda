module DASHI.Physics.Closure.NSR3RadialLebesgueSignedSecondMomentAggregationExact where

------------------------------------------------------------------------
-- A / RADIAL LEBESGUE SIGNED SECOND-MOMENT AGGREGATION
--
-- This is the measure-aware counterpart of NSLebesgueSignedSecondMoment-
-- AggregationExact.  It consumes the sharper R^3 radial factor budget:
--
--   Gram <= q G
--   secondMoment <= q Q
--   radial density = q
--   a = nu q
--
-- and therefore aggregates the already-paid integrand
--
--   q * a^{-3} * Gram * secondMoment
--
-- under the ordinary majorant
--
--   nu^{-3} * G * Q.
--
-- The singular inverse cube is never integrated in isolation.  The radial
-- density is used before domination, so no artificial pointwise |xi|^6
-- obligation is reintroduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanLebesgueSignedAggregationExact as Lebesgue
import DASHI.Physics.Closure.NSLebesgueSignedSecondMomentAggregationExact as Ordered
import DASHI.Physics.Closure.NSWholeSpaceR3RadialOriginCancellationExact as Radial
import DASHI.Physics.Closure.NSWholeSpaceR3RadialFactorBudgetExact as Budget

record RadialLowFrequencySecondMomentField
    {dataSet : Euclidean.EuclideanSignedFluxData}
    (base : Lebesgue.EuclideanLebesgueIntegralAuthority dataSet) : Set₁ where
  field
    radialData :
      Euclidean.EuclideanInteraction →
      Radial.PositiveViscosityRadiusSquare

    gramFactor :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    secondMomentFactor :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    gramMajorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    secondMomentMajorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    pointwiseFactorBudget :
      (I : Euclidean.EuclideanInteraction) →
      Budget.R3RadialFactorBudget
        (radialData I)
        (gramFactor I)
        (secondMomentFactor I)
        (gramMajorant I)
        (secondMomentMajorant I)

    paidIntegrandNonnegative :
      (I : Euclidean.EuclideanInteraction) →
      BishopReal.NonNegative
        (BishopReal._*_
          (Radial.radiusSquared (radialData I))
          (BishopReal._*_
            (Radial.inverseCube
              (Radial.heatRate (radialData I))
              (Radial.heatRateNonzero (radialData I)))
            (BishopReal._*_
              (gramFactor I)
              (secondMomentFactor I))))

    radialMajorantIntegrable :
      Lebesgue.Integrable base
        (λ I →
          BishopReal._*_
            (Radial.inverseCube
              (Radial.viscosity (radialData I))
              (Radial.viscosityNonzero (radialData I)))
            (BishopReal._*_
              (gramMajorant I)
              (secondMomentMajorant I)))

open RadialLowFrequencySecondMomentField public

radiallyPaidIntegrand :
  ∀ {dataSet base} →
  RadialLowFrequencySecondMomentField {dataSet} base →
  Euclidean.EuclideanInteraction → BishopReal.ℝ
radiallyPaidIntegrand field I =
  BishopReal._*_
    (Radial.radiusSquared (radialData field I))
    (BishopReal._*_
      (Radial.inverseCube
        (Radial.heatRate (radialData field I))
        (Radial.heatRateNonzero (radialData field I)))
      (BishopReal._*_
        (gramFactor field I)
        (secondMomentFactor field I)))

radialPaidMajorant :
  ∀ {dataSet base} →
  RadialLowFrequencySecondMomentField {dataSet} base →
  Euclidean.EuclideanInteraction → BishopReal.ℝ
radialPaidMajorant field I =
  BishopReal._*_
    (Radial.inverseCube
      (Radial.viscosity (radialData field I))
      (Radial.viscosityNonzero (radialData field I)))
    (BishopReal._*_
      (gramMajorant field I)
      (secondMomentMajorant field I))

pointwiseRadialPayment :
  ∀ {dataSet base}
    (field : RadialLowFrequencySecondMomentField {dataSet} base) →
  (I : Euclidean.EuclideanInteraction) →
  BishopReal._≤_
    (radiallyPaidIntegrand field I)
    (radialPaidMajorant field I)
pointwiseRadialPayment field I =
  Budget.radialInverseCubeFactorPayment
    (pointwiseFactorBudget field I)

radiallyPaidIntegrable :
  ∀ {dataSet base}
    (ordered : Ordered.OrderedEuclideanLebesgueAuthority base)
    (field : RadialLowFrequencySecondMomentField {dataSet} base) →
  Lebesgue.Integrable base
    (radiallyPaidIntegrand field)
radiallyPaidIntegrable ordered field =
  Ordered.dominatedIntegrableNonnegative ordered
    (radialMajorantIntegrable field)
    (paidIntegrandNonnegative field)
    (pointwiseRadialPayment field)

integratedRadialSecondMomentBound :
  ∀ {dataSet base}
    (ordered : Ordered.OrderedEuclideanLebesgueAuthority base)
    (field : RadialLowFrequencySecondMomentField {dataSet} base) →
  BishopReal._≤_
    (Lebesgue.integral base
      (radiallyPaidIntegrand field))
    (Lebesgue.integral base
      (radialPaidMajorant field))
integratedRadialSecondMomentBound ordered field =
  Ordered.integralMonotone ordered
    (radiallyPaidIntegrable ordered field)
    (radialMajorantIntegrable field)
    (pointwiseRadialPayment field)

------------------------------------------------------------------------
-- Honest boundary:
--
-- This compiler assumes the integral authority presented here is the actual
-- radialized low-frequency Lebesgue integral.  The remaining same-object weld
-- must identify its q-density with the canonical R^3 measure/Fubini
-- decomposition; no such identification is postulated in this file.
------------------------------------------------------------------------

radialPaymentBeforeDominationClosed : Bool
radialPaymentBeforeDominationClosed = true

pointwiseXiSixRequiredByAggregator : Bool
pointwiseXiSixRequiredByAggregator = false

singularInverseCubeIntegratedAlone : Bool
singularInverseCubeIntegratedAlone = false

physicalSecondMomentQProducerClosedHere : Bool
physicalSecondMomentQProducerClosedHere = false

radialLebesgueSameObjectWeldClosedHere : Bool
radialLebesgueSameObjectWeldClosedHere = false

clayPromotion : Bool
clayPromotion = false

radialPaymentBeforeDominationClosedIsTrue :
  radialPaymentBeforeDominationClosed ≡ true
radialPaymentBeforeDominationClosedIsTrue = refl

pointwiseXiSixRequiredByAggregatorIsFalse :
  pointwiseXiSixRequiredByAggregator ≡ false
pointwiseXiSixRequiredByAggregatorIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
