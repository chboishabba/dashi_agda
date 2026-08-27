module DASHI.Analysis.PoleQuotientedExteriorDeskTestExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Post-G20 desk-test owner.
--
-- The intended analytic specialization is
--
--   S_i(x) = c_i m(x) + E_i(x)
--
-- with the augmented determinant
--
--   det [ S_1(x_j) ; S_2(x_j) ; m(x_j) ]_{j=1}^3.
--
-- If the pole response is rank one with known profile m, row subtraction
-- should identify this determinant exactly with the residual determinant
-- det[E_1;E_2;m], killing both pure-pole and mixed pole/error terms before
-- any estimate.  This module makes that exact identity an explicit gate; it
-- does not pretend current DASHI has already proved it for a literal Weil EF.
------------------------------------------------------------------------

record PoleQuotientedExteriorSystem : Set₁ where
  field
    Sample Scalar : Set

    zeroS : Scalar
    _+S_ _*S_ : Scalar → Scalar → Scalar

    poleProfile : Sample → Scalar
    response₁ response₂ : Sample → Scalar
    residual₁ residual₂ : Sample → Scalar
    poleCoefficient₁ poleCoefficient₂ : Scalar

    response₁Decomposes :
      (x : Sample) →
      response₁ x ≡
      poleCoefficient₁ *S poleProfile x +S residual₁ x

    response₂Decomposes :
      (x : Sample) →
      response₂ x ≡
      poleCoefficient₂ *S poleProfile x +S residual₂ x

    det3At :
      Sample → Sample → Sample →
      (Sample → Scalar) →
      (Sample → Scalar) →
      (Sample → Scalar) →
      Scalar

    augmentedDeterminantKillsPoleAndMixedTerms :
      (x₁ x₂ x₃ : Sample) →
      det3At x₁ x₂ x₃ response₁ response₂ poleProfile
      ≡
      det3At x₁ x₂ x₃ residual₁ residual₂ poleProfile

    systemReading : String

open PoleQuotientedExteriorSystem public

------------------------------------------------------------------------
-- Dimension accounting: three samples minus one known nuisance direction
-- leaves a two-dimensional quotient, the minimum dimension supporting a
-- nontrivial two-channel exterior coordinate.
------------------------------------------------------------------------

record ExteriorQuotientDimensionReceipt : Set where
  constructor exteriorQuotientDimensionReceipt
  field
    sampleDimension : Nat
    nuisanceRank : Nat
    residualDimension : Nat

    sampleDimensionIsThree : sampleDimension ≡ 3
    nuisanceRankIsOne : nuisanceRank ≡ 1
    residualDimensionIsTwo : residualDimension ≡ 2

    dimensionBalance : nuisanceRank + residualDimension ≡ sampleDimension

canonicalExteriorQuotientDimensionReceipt : ExteriorQuotientDimensionReceipt
canonicalExteriorQuotientDimensionReceipt =
  exteriorQuotientDimensionReceipt
    3 1 2
    refl refl refl refl

------------------------------------------------------------------------
-- Five-lemma admission experiment.
------------------------------------------------------------------------

data G21GateStatus : Set where
  derivedHere : G21GateStatus
  interfaceOnly : G21GateStatus
  sourceBackedOnly : G21GateStatus
  rejected : G21GateStatus

record G21ExteriorDeskTest : Set₁ where
  field
    commonPoleProfileFactorization : G21GateStatus
    augmentedPoleAndMixedCancellation : G21GateStatus
    offLineZeroQuotientNondegeneracy : G21GateStatus
    literalPrimePairKernelIdentity : G21GateStatus
    primePairScaleGate : G21GateStatus

    dimensionReceipt : ExteriorQuotientDimensionReceipt
    deskTestReading : String

open G21ExteriorDeskTest public

canonicalG21ExteriorDeskTestBoundary : G21ExteriorDeskTest
canonicalG21ExteriorDeskTestBoundary =
  record
    { commonPoleProfileFactorization = interfaceOnly
    ; augmentedPoleAndMixedCancellation = interfaceOnly
    ; offLineZeroQuotientNondegeneracy = interfaceOnly
    ; literalPrimePairKernelIdentity = interfaceOnly
    ; primePairScaleGate = interfaceOnly
    ; dimensionReceipt = canonicalExteriorQuotientDimensionReceipt
    ; deskTestReading =
        "G21 is admitted only if the literal two-channel Weil system factors through one known pole profile, the 3x3 augmented determinant removes pole and mixed terms exactly, an off-line zero survives in the pole quotient, the literal EF expands to a diagonal-free relational prime-pair kernel, and the surviving arithmetic scale is favorable before any heroic estimate."
    }

record PoleQuotientedExteriorNonPromotionBoundary : Set where
  constructor poleQuotientedExteriorNonPromotionBoundary
  field
    rankOnePoleImpliesMixedTermsCancelInTwoByTwoDeterminant : Bool
    rankOnePoleImpliesMixedTermsCancelInTwoByTwoDeterminantIsFalse :
      rankOnePoleImpliesMixedTermsCancelInTwoByTwoDeterminant ≡ false

    threeSamplesProveOffLineZeroRankTwo : Bool
    threeSamplesProveOffLineZeroRankTwoIsFalse :
      threeSamplesProveOffLineZeroRankTwo ≡ false

    algebraicPoleQuotientProvesRH : Bool
    algebraicPoleQuotientProvesRHIsFalse :
      algebraicPoleQuotientProvesRH ≡ false

canonicalPoleQuotientedExteriorNonPromotionBoundary :
  PoleQuotientedExteriorNonPromotionBoundary
canonicalPoleQuotientedExteriorNonPromotionBoundary =
  poleQuotientedExteriorNonPromotionBoundary
    false refl
    false refl
    false refl
