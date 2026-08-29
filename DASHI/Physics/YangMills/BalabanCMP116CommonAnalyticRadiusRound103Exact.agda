{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1: ONE ACTUAL COMMON POSITIVE ANALYTIC RADIUS
--
-- One radius is quantified over every Scale/Volume.  Uniformity is therefore
-- structural; no separate `Set` receipt is stored.  Membership of each physical
-- coordinate is evidence-bearing through the `inside...` fields below.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP116CommonAnalyticRadius (Scale Volume : Set) : Set₁ where
  field
    radius : ℚ
    radiusPositive : 0ℚ < radius

    BackgroundCoordinateInside : Scale → Volume → Set
    SourceCoordinateInside : Scale → Volume → Set
    LocalActivityCoordinateInside : Scale → Volume → Set
    SubstitutedBackgroundInside : Scale → Volume → Set

    backgroundCoordinateInside :
      ∀ scale volume → BackgroundCoordinateInside scale volume
    sourceCoordinateInside :
      ∀ scale volume → SourceCoordinateInside scale volume
    localActivityCoordinateInside :
      ∀ scale volume → LocalActivityCoordinateInside scale volume
    substitutedBackgroundInside :
      ∀ scale volume → SubstitutedBackgroundInside scale volume

open CMP116CommonAnalyticRadius public

record FirstSecondDerivativeUseSameRadius
    {Scale Volume : Set}
    (radiusData : CMP116CommonAnalyticRadius Scale Volume) : Set₁ where
  field
    FirstDerivativeCauchyValid : Scale → Volume → Set
    SecondDerivativeCauchyValid : Scale → Volume → Set
    firstDerivativeCauchyValid :
      ∀ scale volume → FirstDerivativeCauchyValid scale volume
    secondDerivativeCauchyValid :
      ∀ scale volume → SecondDerivativeCauchyValid scale volume

open FirstSecondDerivativeUseSameRadius public

commonRadiusPositiveNonnegative :
  ∀ {Scale Volume}
    (dataSet : CMP116CommonAnalyticRadius Scale Volume) →
  0ℚ ≤ radius dataSet
commonRadiusPositiveNonnegative dataSet =
  ℚP.<⇒≤ (radiusPositive dataSet)

cmp116CommonRadiusPackagingLevel : ProofLevel
cmp116CommonRadiusPackagingLevel = machineChecked

cmp116CommonAnalyticDomainSourceLevel : ProofLevel
cmp116CommonAnalyticDomainSourceLevel = standardImported

literalCMP116UniformCommonRadiusInstantiationLevel : ProofLevel
literalCMP116UniformCommonRadiusInstantiationLevel = conditional
