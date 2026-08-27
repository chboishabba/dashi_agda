module DASHI.Analysis.PoleRankTwoQuotientedExteriorDeskTestExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Robust G21 carrier after the literal source audit.
--
-- The Weil explicit formula contributes two pole-evaluation profiles.  Unless
-- an additional theorem collapses them to one common direction, the nuisance
-- space must be allowed rank two.  Four samples then leave two residual
-- dimensions, enough for a two-channel exterior coordinate.
------------------------------------------------------------------------

record PoleRankTwoQuotientedExteriorSystem : Set₁ where
  field
    Sample Scalar : Set

    positivePoleProfile negativePoleProfile : Sample → Scalar
    response₁ response₂ : Sample → Scalar
    residual₁ residual₂ : Sample → Scalar

    -- Coefficients describe how each response channel contains the two known
    -- nuisance profiles.  No claim is made here about their analytic values.
    Coefficient : Set
    synthesize : Coefficient → (Sample → Scalar) → Sample → Scalar
    combine3 : Scalar → Scalar → Scalar → Scalar

    positiveCoefficient₁ negativeCoefficient₁ : Coefficient
    positiveCoefficient₂ negativeCoefficient₂ : Coefficient

    response₁Decomposes :
      (x : Sample) →
      response₁ x ≡
      combine3
        (synthesize positiveCoefficient₁ positivePoleProfile x)
        (synthesize negativeCoefficient₁ negativePoleProfile x)
        (residual₁ x)

    response₂Decomposes :
      (x : Sample) →
      response₂ x ≡
      combine3
        (synthesize positiveCoefficient₂ positivePoleProfile x)
        (synthesize negativeCoefficient₂ negativePoleProfile x)
        (residual₂ x)

    det4At :
      Sample → Sample → Sample → Sample →
      (Sample → Scalar) →
      (Sample → Scalar) →
      (Sample → Scalar) →
      (Sample → Scalar) →
      Scalar

    augmentedDeterminantKillsBothPoleDirections :
      (x₁ x₂ x₃ x₄ : Sample) →
      det4At x₁ x₂ x₃ x₄
        response₁ response₂ positivePoleProfile negativePoleProfile
      ≡
      det4At x₁ x₂ x₃ x₄
        residual₁ residual₂ positivePoleProfile negativePoleProfile

    systemReading : String

open PoleRankTwoQuotientedExteriorSystem public

record RankTwoExteriorDimensionReceipt : Set where
  constructor rankTwoExteriorDimensionReceipt
  field
    sampleDimension nuisanceRank residualDimension : Nat
    sampleDimensionIsFour : sampleDimension ≡ 4
    nuisanceRankIsTwo : nuisanceRank ≡ 2
    residualDimensionIsTwo : residualDimension ≡ 2
    balance : nuisanceRank + residualDimension ≡ sampleDimension

canonicalRankTwoExteriorDimensionReceipt : RankTwoExteriorDimensionReceipt
canonicalRankTwoExteriorDimensionReceipt =
  rankTwoExteriorDimensionReceipt 4 2 2 refl refl refl refl

record RankTwoPoleQuotientBoundary : Set where
  constructor rankTwoPoleQuotientBoundary
  field
    requiresRankOnePoleReduction : Bool
    requiresRankOnePoleReductionIsFalse : requiresRankOnePoleReduction ≡ false

    retainsTwoResidualDimensions : Bool
    retainsTwoResidualDimensionsIsTrue : retainsTwoResidualDimensions ≡ true

    literalFourByFourIdentityAlreadyDerived : Bool
    literalFourByFourIdentityAlreadyDerivedIsFalse :
      literalFourByFourIdentityAlreadyDerived ≡ false

    fourSamplesAloneProveOffLineSignal : Bool
    fourSamplesAloneProveOffLineSignalIsFalse :
      fourSamplesAloneProveOffLineSignal ≡ false

canonicalRankTwoPoleQuotientBoundary : RankTwoPoleQuotientBoundary
canonicalRankTwoPoleQuotientBoundary =
  rankTwoPoleQuotientBoundary false refl true refl false refl false refl
