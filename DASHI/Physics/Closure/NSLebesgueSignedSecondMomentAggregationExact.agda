module DASHI.Physics.Closure.NSLebesgueSignedSecondMomentAggregationExact where

------------------------------------------------------------------------
-- A / LEBESGUE AGGREGATION OF THE COMPENSATED SECOND-MOMENT PRODUCT
--
-- The low-frequency singularity is not integrated as |xi|^{-6} by itself.
-- The pointwise producer first supplies
--
--   stateFactor <= a^3 majorant,
--
-- and NSWholeSpaceLowFrequencyCompensationExact proves on the SAME Bishop-real
-- carrier
--
--   coefficient * a^{-3} * stateFactor
--      <= coefficient * majorant.
--
-- This owner performs the next operation in the mandated order:
--
--   signed/centered identity
--     -> pointwise heat-cube compensation
--     -> nonnegative integrable majorant
--     -> Lebesgue aggregation.
--
-- No lattice count, shell cardinality, or premature absolute majorant appears.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanLebesgueSignedAggregationExact as Lebesgue
import DASHI.Physics.Closure.NSWholeSpaceLowFrequencyCompensationExact as Low
import DASHI.Foundations.BishopGeometricReciprocalSquareFromCrossExact as Reciprocal

record OrderedEuclideanLebesgueAuthority
    {dataSet : Euclidean.EuclideanSignedFluxData}
    (base : Lebesgue.EuclideanLebesgueIntegralAuthority dataSet) : Set₁ where
  field
    dominatedIntegrableNonnegative :
      {f g : Euclidean.EuclideanInteraction → BishopReal.ℝ} →
      Lebesgue.Integrable base g →
      ((I : Euclidean.EuclideanInteraction) →
        BishopReal.NonNegative (f I)) →
      ((I : Euclidean.EuclideanInteraction) →
        BishopReal._≤_ (f I) (g I)) →
      Lebesgue.Integrable base f

    integralMonotone :
      {f g : Euclidean.EuclideanInteraction → BishopReal.ℝ} →
      Lebesgue.Integrable base f →
      Lebesgue.Integrable base g →
      ((I : Euclidean.EuclideanInteraction) →
        BishopReal._≤_ (f I) (g I)) →
      BishopReal._≤_
        (Lebesgue.integral base f)
        (Lebesgue.integral base g)

open OrderedEuclideanLebesgueAuthority public

record LowFrequencySecondMomentField
    {dataSet : Euclidean.EuclideanSignedFluxData}
    (base : Lebesgue.EuclideanLebesgueIntegralAuthority dataSet) : Set₁ where
  field
    heatRate :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    stateFactor :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    majorant :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    coefficient :
      Euclidean.EuclideanInteraction → BishopReal.ℝ

    coefficientNonnegative :
      (I : Euclidean.EuclideanInteraction) →
      BishopReal.NonNegative (coefficient I)

    pointwiseCompensation :
      (I : Euclidean.EuclideanInteraction) →
      Low.BishopLowFrequencyStateCompensation
        (heatRate I)
        (stateFactor I)
        (majorant I)

    compensatedIntegrandNonnegative :
      (I : Euclidean.EuclideanInteraction) →
      BishopReal.NonNegative
        (BishopReal._*_
          (coefficient I)
          (BishopReal._*_
            (Low.inverseCube
              (heatRate I)
              (Reciprocal.xNonzero
                (Low.heatRatePositive (pointwiseCompensation I))))
            (stateFactor I)))

    compensatedMajorantIntegrable :
      Lebesgue.Integrable base
        (λ I →
          BishopReal._*_
            (coefficient I)
            (majorant I))

open LowFrequencySecondMomentField public

compensatedSecondMomentIntegrand :
  ∀ {dataSet base} →
  LowFrequencySecondMomentField {dataSet} base →
  Euclidean.EuclideanInteraction → BishopReal.ℝ
compensatedSecondMomentIntegrand field I =
  BishopReal._*_
    (coefficient field I)
    (BishopReal._*_
      (Low.inverseCube
        (heatRate field I)
        (Reciprocal.xNonzero
          (Low.heatRatePositive (pointwiseCompensation field I))))
      (stateFactor field I))

compensatedSecondMomentMajorant :
  ∀ {dataSet base} →
  LowFrequencySecondMomentField {dataSet} base →
  Euclidean.EuclideanInteraction → BishopReal.ℝ
compensatedSecondMomentMajorant field I =
  BishopReal._*_
    (coefficient field I)
    (majorant field I)

pointwiseCompensatedSecondMomentBound :
  ∀ {dataSet base}
    (field : LowFrequencySecondMomentField {dataSet} base) →
  (I : Euclidean.EuclideanInteraction) →
  BishopReal._≤_
    (compensatedSecondMomentIntegrand field I)
    (compensatedSecondMomentMajorant field I)
pointwiseCompensatedSecondMomentBound field I =
  Low.coefficientScaledCompensation
    (coefficient field I)
    (heatRate field I)
    (stateFactor field I)
    (majorant field I)
    (coefficientNonnegative field I)
    (pointwiseCompensation field I)

compensatedSecondMomentIntegrable :
  ∀ {dataSet base}
    (ordered : OrderedEuclideanLebesgueAuthority base)
    (field : LowFrequencySecondMomentField {dataSet} base) →
  Lebesgue.Integrable base
    (compensatedSecondMomentIntegrand field)
compensatedSecondMomentIntegrable ordered field =
  dominatedIntegrableNonnegative ordered
    (compensatedMajorantIntegrable field)
    (compensatedIntegrandNonnegative field)
    (pointwiseCompensatedSecondMomentBound field)

integratedCompensatedSecondMomentBound :
  ∀ {dataSet base}
    (ordered : OrderedEuclideanLebesgueAuthority base)
    (field : LowFrequencySecondMomentField {dataSet} base) →
  BishopReal._≤_
    (Lebesgue.integral base
      (compensatedSecondMomentIntegrand field))
    (Lebesgue.integral base
      (compensatedSecondMomentMajorant field))
integratedCompensatedSecondMomentBound ordered field =
  integralMonotone ordered
    (compensatedSecondMomentIntegrable ordered field)
    (compensatedMajorantIntegrable field)
    (pointwiseCompensatedSecondMomentBound field)

------------------------------------------------------------------------
-- This is the exact continuous analogue of the finite second-moment aggregation
-- step: the singular multiplier is paid BEFORE integration.  The remaining
-- A-specific producer is now sharply localized to constructing the physical
-- stateFactor/majorant field from the Fourier/Leray/Waleffe geometry and
-- proving the majorant integrable on the selected low-frequency region.
------------------------------------------------------------------------

lowFrequencyCompensationBeforeLebesgueClosed : Bool
lowFrequencyCompensationBeforeLebesgueClosed = true

singularCurvatureIntegratedInIsolation : Bool
singularCurvatureIntegratedInIsolation = false

latticeCardinalityUsed : Bool
latticeCardinalityUsed = false

physicalHeatCubeProducerClosedHere : Bool
physicalHeatCubeProducerClosedHere = false

concreteLebesgueMeasureConstructedHere : Bool
concreteLebesgueMeasureConstructedHere = false

clayPromotion : Bool
clayPromotion = false

lowFrequencyCompensationBeforeLebesgueClosedIsTrue :
  lowFrequencyCompensationBeforeLebesgueClosed ≡ true
lowFrequencyCompensationBeforeLebesgueClosedIsTrue = refl

singularCurvatureIntegratedInIsolationIsFalse :
  singularCurvatureIntegratedInIsolation ≡ false
singularCurvatureIntegratedInIsolationIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
