{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealHaarRegionSourceSignsExact where

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarStrictPositivityExact as Haar
import DASHI.Physics.Foundations.CMP119AntigravityRealHaarPositiveRegionExact as Region
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical

------------------------------------------------------------------------
-- ONE POSITIVE-HAAR REGION PAYS BOTH STRICT SOURCE SIGNS
--
-- The physical content is now exactly:
--
--   1. a region of positive product-Haar mass;
--   2. density >= c_Z * regionWeight with c_Z > 0;
--   3. density*F^2 >= c_F * regionWeight with c_F > 0.
--
-- This is the correct local-continuity/support target around a genuinely
-- nonzero-curvature configuration.
------------------------------------------------------------------------

record RealHaarRegionSourceSignInput
    {Configuration : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    (ordered : Haar.OrderedRealHaarIntegrationLaws measure)
    (fieldStrengthSquare : Configuration → ℝ) : Set₁ where
  field
    positiveRegion :
      Region.PositiveRealHaarRegion ordered

    densityLower :
      Region.UniformPositiveLowerBoundOnRegion
        positiveRegion
        (Physical.density measure)

    weightedF2Lower :
      Region.UniformPositiveLowerBoundOnRegion
        positiveRegion
        (Haar.weightedObservable
          {measure = measure}
          fieldStrengthSquare)

open RealHaarRegionSourceSignInput public

asPartitionWitness :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    {ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure}
    {fieldStrengthSquare : Configuration → ℝ} →
  RealHaarRegionSourceSignInput ordered fieldStrengthSquare →
  Haar.PositiveRealPartitionWitness ordered
asPartitionWitness {ordered = ordered} strict input = record
  { Haar.PositiveRealPartitionWitness.densityMinorant =
      Region.asStrictPositiveMinorantWithScaling
        strict
        (Region.scalingLawFromOrderedBase ordered)
        (densityLower input)
  }

asWeightedF2Witness :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    {ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure}
    {fieldStrengthSquare : Configuration → ℝ} →
  RealHaarRegionSourceSignInput ordered fieldStrengthSquare →
  Haar.PositiveWeightedRealHaarWitness ordered fieldStrengthSquare
asWeightedF2Witness {ordered = ordered} strict input = record
  { Haar.PositiveWeightedRealHaarWitness.weightedMinorant =
      Region.asStrictPositiveMinorantWithScaling
        strict
        (Region.scalingLawFromOrderedBase ordered)
        (weightedF2Lower input)
  }

regionSourcePartitionPositive :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure)
    (fieldStrengthSquare : Configuration → ℝ)
    (input :
      RealHaarRegionSourceSignInput ordered fieldStrengthSquare) →
  0ℝ <ℝ Physical.partitionFunction measure
regionSourcePartitionPositive strict ordered fieldStrengthSquare input =
  Haar.partitionFunctionPositive
    strict ordered
    (asPartitionWitness strict input)

regionSourceF2NumeratorPositive :
  ∀ {Configuration measure}
    (strict : Strict.RealStrictSignLaws)
    (ordered : Haar.OrderedRealHaarIntegrationLaws
      {Configuration = Configuration} measure)
    (fieldStrengthSquare : Configuration → ℝ)
    (input :
      RealHaarRegionSourceSignInput ordered fieldStrengthSquare) →
  0ℝ <ℝ
    Haar.weightedNumerator
      {measure = measure}
      fieldStrengthSquare
regionSourceF2NumeratorPositive strict ordered fieldStrengthSquare input =
  Haar.weightedNumeratorPositive
    strict ordered fieldStrengthSquare
    (asWeightedF2Witness strict input)
