{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact where

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP116CommonAnalyticRadius (Scale Volume : Set) : Set₁ where
  field
    radius : ℚ
    radiusPositive : 0ℚ < radius

    backgroundCoordinateInside : Scale → Volume → Set
    sourceCoordinateInside : Scale → Volume → Set
    localActivityCoordinateInside : Scale → Volume → Set
    substitutedBackgroundInside : Scale → Volume → Set

    cutoffVolumeScaleUniform : Set

open CMP116CommonAnalyticRadius public

record FirstSecondDerivativeUseSameRadius
    {Scale Volume : Set}
    (radiusData : CMP116CommonAnalyticRadius Scale Volume) : Set₁ where
  field
    firstDerivativeCauchyValid : Scale → Volume → Set
    secondDerivativeCauchyValid : Scale → Volume → Set
    firstDerivativeUsesRadius : Scale → Volume → Set
    secondDerivativeUsesRadius : Scale → Volume → Set

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
