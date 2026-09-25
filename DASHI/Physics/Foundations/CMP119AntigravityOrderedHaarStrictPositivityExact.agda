{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityOrderedHaarStrictPositivityExact where

open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; _<_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureIntegrationLawsExact as Linear
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- STRICT POSITIVITY ON THE ACTUAL HAAR FUNCTIONAL
--
-- A continuous compact-group Haar integral is not, in general, an exact finite
-- quadrature on arbitrary integrands.  The least-privilege strict-positivity
-- theorem instead asks for:
--
--   * monotonicity of the actual Haar integral;
--   * a minorant whose Haar integral is strictly positive.
--
-- This is the correct target for a positive-measure neighborhood/cylinder
-- argument.  It works for the partition function and for density * F^2 without
-- replacing Haar integration by a finite atomic measure.
------------------------------------------------------------------------

record OrderedRationalHaarIntegrationLaws
    {Configuration : Set}
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ) : Set₁ where
  field
    linear :
      Linear.RationalFiniteMeasureIntegrationLaws measure

    haarIntegralMonotone :
      ∀ left right →
      (∀ configuration → left configuration ≤ right configuration) →
      Physical.haarIntegral measure left
      ≤ Physical.haarIntegral measure right

    partitionFunctionIsDensityIntegral :
      Physical.partitionFunction measure
      ≡ Physical.haarIntegral measure (Physical.density measure)

open OrderedRationalHaarIntegrationLaws public

record StrictPositiveHaarMinorant
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (laws : OrderedRationalHaarIntegrationLaws measure)
    (integrand : Configuration → ℚ) : Set₁ where
  field
    minorant : Configuration → ℚ

    minorantBelow :
      ∀ configuration →
      minorant configuration ≤ integrand configuration

    minorantIntegralPositive :
      0ℚ < Physical.haarIntegral measure minorant

open StrictPositiveHaarMinorant public

haarIntegralStrictlyPositiveFromMinorant :
  ∀ {Configuration measure}
    {laws : OrderedRationalHaarIntegrationLaws
      {Configuration = Configuration} measure}
    {integrand : Configuration → ℚ} →
  StrictPositiveHaarMinorant laws integrand →
  0ℚ < Physical.haarIntegral measure integrand
haarIntegralStrictlyPositiveFromMinorant {measure = measure} {laws = laws} witness =
  let
    lower =
      haarIntegralMonotone laws
        (minorant witness)
        _
        (minorantBelow witness)
  in
  Data.Rational.Properties.<-≤-trans
    (minorantIntegralPositive witness)
    lower

record PositivePartitionHaarWitness
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (laws : OrderedRationalHaarIntegrationLaws measure) : Set₁ where
  field
    densityMinorant :
      StrictPositiveHaarMinorant laws (Physical.density measure)

open PositivePartitionHaarWitness public

partitionFunctionPositive :
  ∀ {Configuration measure}
    (laws : OrderedRationalHaarIntegrationLaws
      {Configuration = Configuration} measure) →
  PositivePartitionHaarWitness laws →
  0ℚ < Physical.partitionFunction measure
partitionFunctionPositive {measure = measure} laws witness =
  subst
    (λ value → 0ℚ < value)
    (sym (partitionFunctionIsDensityIntegral laws))
    (haarIntegralStrictlyPositiveFromMinorant
      (densityMinorant witness))

weightedF2Integrand :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  (Configuration → ℚ) →
  Configuration → ℚ
weightedF2Integrand {measure = measure} fieldStrengthSquare configuration =
  Physical.density measure configuration
  * fieldStrengthSquare configuration

fieldStrengthSquareNumerator :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ} →
  (Configuration → ℚ) →
  ℚ
fieldStrengthSquareNumerator {measure = measure} fieldStrengthSquare =
  Physical.haarIntegral measure
    (weightedF2Integrand fieldStrengthSquare)

record PositiveWeightedF2HaarWitness
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ}
    (laws : OrderedRationalHaarIntegrationLaws measure)
    (fieldStrengthSquare : Configuration → ℚ) : Set₁ where
  field
    weightedF2Minorant :
      StrictPositiveHaarMinorant laws
        (weightedF2Integrand fieldStrengthSquare)

open PositiveWeightedF2HaarWitness public

fieldStrengthSquareNumeratorPositive :
  ∀ {Configuration measure}
    (laws : OrderedRationalHaarIntegrationLaws
      {Configuration = Configuration} measure)
    (fieldStrengthSquare : Configuration → ℚ) →
  PositiveWeightedF2HaarWitness laws fieldStrengthSquare →
  0ℚ < fieldStrengthSquareNumerator
    {measure = measure} fieldStrengthSquare
fieldStrengthSquareNumeratorPositive laws fieldStrengthSquare witness =
  haarIntegralStrictlyPositiveFromMinorant
    (weightedF2Minorant witness)
