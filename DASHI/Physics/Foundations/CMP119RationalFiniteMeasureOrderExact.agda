{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact where

------------------------------------------------------------------------
-- POSITIVE RATIONAL HAAR INTEGRATION -> WEIGHTED NUMERATOR MONOTONICITY.
--
-- The older rational stress integration owner retained only linearity.  For the
-- Eq.(2.23) sign max-cut we also need the standard order property of integration
-- against a nonnegative density.  This file isolates exactly that additional
-- finite-measure law and compiles pointwise sector bounds to weighted-numerator
-- bounds.  No sector sign or cosmological sign is assumed here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Linear
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

record RationalPositiveFiniteMeasureOrderLaws
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) : Set₁ where
  field
    linear : Linear.RationalFiniteMeasureIntegrationLaws measure

    densityNonnegative :
      ∀ configuration → 0ℚ ≤ Physical.density measure configuration

    haarIntegralMonotone :
      ∀ left right →
      (∀ configuration → left configuration ≤ right configuration) →
      Physical.haarIntegral measure left
      ≤ Physical.haarIntegral measure right

open RationalPositiveFiniteMeasureOrderLaws public

weightedNumerator :
  ∀ {Configuration} →
  Physical.PhysicalFiniteYMMeasure Configuration ℚ →
  (Configuration → ℚ) → ℚ
weightedNumerator measure observable =
  Physical.haarIntegral measure
    (λ configuration →
      Physical.density measure configuration * observable configuration)

weightedNumeratorMonotone :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (laws : RationalPositiveFiniteMeasureOrderLaws measure)
    left right →
  (∀ configuration → left configuration ≤ right configuration) →
  weightedNumerator measure left ≤ weightedNumerator measure right
weightedNumeratorMonotone {measure = measure} laws left right pointwise =
  haarIntegralMonotone laws _ _
    (λ configuration →
      ℚP.*-monoˡ-≤-nonNeg
        (Physical.density measure configuration)
        (densityNonnegative laws configuration)
        (pointwise configuration))

constantObservable :
  ∀ {Configuration} → ℚ → Configuration → ℚ
constantObservable upper _ = upper

weightedNumeratorBelowConstant :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (laws : RationalPositiveFiniteMeasureOrderLaws measure)
    observable upper →
  (∀ configuration → observable configuration ≤ upper) →
  weightedNumerator measure observable
  ≤ weightedNumerator measure (constantObservable upper)
weightedNumeratorBelowConstant laws observable upper pointwise =
  weightedNumeratorMonotone laws observable (constantObservable upper) pointwise

positiveHaarOrderIsStandardFiniteMeasureLaw : Bool
positiveHaarOrderIsStandardFiniteMeasureLaw = true

pointwiseSectorMajorantNowCompilesToWeightedNumeratorMajorant : Bool
pointwiseSectorMajorantNowCompilesToWeightedNumeratorMajorant = true
