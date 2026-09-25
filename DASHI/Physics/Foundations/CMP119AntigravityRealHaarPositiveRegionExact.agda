{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealHaarPositiveRegionExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarStrictPositivityExact as Haar
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- POSITIVE-HAAR REGION COMPILER
--
-- A continuous compact Haar proof should expose a positive-mass region, not a
-- single point.  Once a nonnegative region weight has strictly positive Haar
-- integral, any integrand uniformly bounded below by a positive multiple of
-- that weight has strictly positive Haar integral.
------------------------------------------------------------------------

record PositiveRealHaarRegion
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (ordered : Haar.OrderedRealHaarIntegrationLaws measure) : Set₁ where
  field
    regionWeight : Configuration → ℝ

    regionWeightNonnegative :
      ∀ configuration →
      0ℝ ≤ℝ regionWeight configuration

    regionMassPositive :
      0ℝ <ℝ Physical.haarIntegral measure regionWeight

open PositiveRealHaarRegion public

record UniformPositiveLowerBoundOnRegion
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    {ordered : Haar.OrderedRealHaarIntegrationLaws measure}
    (region : PositiveRealHaarRegion ordered)
    (integrand : Configuration → ℝ) : Set₁ where
  field
    lowerCoefficient : ℝ

    lowerCoefficientPositive :
      0ℝ <ℝ lowerCoefficient

    scaledRegionBelowIntegrand :
      ∀ configuration →
      lowerCoefficient *ℝ regionWeight region configuration
      ≤ℝ integrand configuration

open UniformPositiveLowerBoundOnRegion public

asStrictPositiveMinorant :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    {ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure}
    {region : PositiveRealHaarRegion ordered}
    {integrand : Configuration → ℝ} →
  UniformPositiveLowerBoundOnRegion region integrand →
  Haar.StrictPositiveRealHaarMinorant ordered integrand
asStrictPositiveMinorant {measure = measure} strict {region = region} lower =
  record
    { Haar.StrictPositiveRealHaarMinorant.minorant =
        λ configuration →
          lowerCoefficient lower *ℝ regionWeight region configuration
    ; Haar.StrictPositiveRealHaarMinorant.minorantBelow =
        scaledRegionBelowIntegrand lower
    ; Haar.StrictPositiveRealHaarMinorant.minorantIntegralPositive =
        let
          -- This equality is deliberately an explicit integration-law input
          -- below.  Without scalar-linearity, positivity of the scaled region
          -- cannot be manufactured from pointwise order alone.
          scaledIntegralPositive =
            scaledRegionIntegralPositive strict lower
        in scaledIntegralPositive
    }

------------------------------------------------------------------------
-- Scalar-linearity needed to compile a region mass into a minorant mass.
------------------------------------------------------------------------

record PositiveRegionScalingLaw
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (ordered : Haar.OrderedRealHaarIntegrationLaws measure) : Set₁ where
  field
    haarIntegralScale :
      ∀ scalar observable →
      Physical.haarIntegral measure
        (λ configuration → scalar *ℝ observable configuration)
      ≡
      scalar *ℝ Physical.haarIntegral measure observable

open PositiveRegionScalingLaw public

scaledRegionIntegralPositive :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    {ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure}
    {region : PositiveRealHaarRegion ordered}
    {integrand : Configuration → ℝ}
    (scaling : PositiveRegionScalingLaw ordered)
    (lower : UniformPositiveLowerBoundOnRegion region integrand) →
  0ℝ <ℝ
    Physical.haarIntegral measure
      (λ configuration →
        lowerCoefficient lower *ℝ regionWeight region configuration)
scaledRegionIntegralPositive
    {measure = measure} strict {region = region} scaling lower =
  let
    productPositive =
      Strict.positiveTimesPositive strict
        (lowerCoefficientPositive lower)
        (regionMassPositive region)
  in
  Relation.Binary.PropositionalEquality.subst
    (λ value → 0ℝ <ℝ value)
    (Relation.Binary.PropositionalEquality.sym
      (haarIntegralScale scaling
        (lowerCoefficient lower)
        (regionWeight region)))
    productPositive

asStrictPositiveMinorantWithScaling :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    {ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure}
    {region : PositiveRealHaarRegion ordered}
    {integrand : Configuration → ℝ}
    (scaling : PositiveRegionScalingLaw ordered) →
  UniformPositiveLowerBoundOnRegion region integrand →
  Haar.StrictPositiveRealHaarMinorant ordered integrand
asStrictPositiveMinorantWithScaling strict {region = region} scaling lower =
  record
    { Haar.StrictPositiveRealHaarMinorant.minorant =
        λ configuration →
          lowerCoefficient lower *ℝ regionWeight region configuration
    ; Haar.StrictPositiveRealHaarMinorant.minorantBelow =
        scaledRegionBelowIntegrand lower
    ; Haar.StrictPositiveRealHaarMinorant.minorantIntegralPositive =
        scaledRegionIntegralPositive strict scaling lower
    }

flatIdentityPointAloneSufficesForF2StrictPositivity : Bool
flatIdentityPointAloneSufficesForF2StrictPositivity = false

flatIdentityPointAloneSufficesForF2StrictPositivityIsFalse :
  flatIdentityPointAloneSufficesForF2StrictPositivity ≡ false
flatIdentityPointAloneSufficesForF2StrictPositivityIsFalse = refl
