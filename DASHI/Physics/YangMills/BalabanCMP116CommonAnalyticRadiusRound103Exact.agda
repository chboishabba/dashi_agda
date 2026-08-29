{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CommonAnalyticRadiusRound103Exact where

------------------------------------------------------------------------
-- ROUND103 BC1: ONE COMMON POSITIVE ANALYTIC RADIUS
--
-- CMP116 Sect.1 works on a common complex analytic domain in U,J,A and then
-- differentiates by Cauchy's formula after the nonlocal substitutions.  The Clay
-- consumer needs uniformity, but it does NOT need a canonical numerical radius.
-- Keep one positive radius and explicit inclusion of every physical source
-- coordinate into that domain.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_; _<_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record CMP116CommonAnalyticRadius (Scale Volume : Set) : Set₁ where
  field
    radius : ℚ
    radiusPositive : 0ℚ < radius

    -- The same radius works throughout the literal finite-cutoff family.
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
  ℚ.<⇒≤ (radiusPositive dataSet)

cmp116CommonRadiusPackagingLevel : ProofLevel
cmp116CommonRadiusPackagingLevel = machineChecked

-- Source authority supplies existence/analyticity on sufficiently small common
-- domains, but does not print a canonical numerical radius.  The remaining
-- physical task is a literal uniform instantiation on the same cutoff family.
cmp116CommonAnalyticDomainSourceLevel : ProofLevel
cmp116CommonAnalyticDomainSourceLevel = standardImported

literalCMP116UniformCommonRadiusInstantiationLevel : ProofLevel
literalCMP116UniformCommonRadiusInstantiationLevel = conditional
