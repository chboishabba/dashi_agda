{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact where

------------------------------------------------------------------------
-- POSITIVE RATIONAL HAAR INTEGRATION -> WEIGHTED NUMERATOR MONOTONICITY.
--
-- The older rational stress integration owner retained only additive linearity.
-- For the Eq.(2.23) sign max-cut we also need the standard order property of
-- integration against a nonnegative density and scalar linearity.  The latter
-- lets constant pointwise majorants factor through the common density integral,
-- which is what ultimately cancels the finite-measure normalization from the
-- E/R/B-versus-vacuum sign comparison.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (trans)

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

    haarIntegralScale :
      ∀ scalar observable →
      Physical.haarIntegral measure
        (λ configuration → scalar * observable configuration)
      ≡
      scalar * Physical.haarIntegral measure observable

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
  haarIntegralMonotone laws _ _ pointwiseWeighted
  where
  pointwiseWeighted : ∀ configuration →
    Physical.density measure configuration * left configuration
    ≤ Physical.density measure configuration * right configuration
  pointwiseWeighted configuration =
    let
      instance
        densityNN : NonNegative (Physical.density measure configuration)
        densityNN = nonNegative (densityNonnegative laws configuration)
    in
    ℚP.*-monoˡ-≤-nonNeg
      (Physical.density measure configuration)
      (pointwise configuration)

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

weightedConstantFactorsDensityIntegral :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (laws : RationalPositiveFiniteMeasureOrderLaws measure)
    scalar →
  weightedNumerator measure (constantObservable scalar)
  ≡
  scalar * Physical.haarIntegral measure (Physical.density measure)
weightedConstantFactorsDensityIntegral {measure = measure} laws scalar =
  trans
    (Linear.haarIntegralCongruent (linear laws)
      (λ configuration →
        Physical.density measure configuration * scalar)
      (λ configuration →
        scalar * Physical.density measure configuration)
      (λ configuration →
        Ring.solve-∀ (Physical.density measure configuration) scalar))
    (haarIntegralScale laws scalar (Physical.density measure))

positiveHaarOrderIsStandardFiniteMeasureLaw : Bool
positiveHaarOrderIsStandardFiniteMeasureLaw = true

pointwiseSectorMajorantNowCompilesToWeightedNumeratorMajorant : Bool
pointwiseSectorMajorantNowCompilesToWeightedNumeratorMajorant = true

constantMajorantsFactorThroughCommonDensityIntegral : Bool
constantMajorantsFactorThroughCommonDensityIntegral = true
