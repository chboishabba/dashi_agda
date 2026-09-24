module DASHI.Analysis.RiemannG2InverseSquareCoefficientR2TargetExact where

------------------------------------------------------------------------
-- COARSE ABSOLUTE INVERSE-SQUARE COMPATIBILITY TARGET
--
-- This surface remains mathematically valid as a sufficient producer, but the
-- vendored 8889 theorem bytes show it is not the canonical uniform acquisition
-- surface.  The actual cluster theorem is centered at baselineCluster and its
-- surplus vanishes like a^2.  A fixed 144*A/t^2 far envelope therefore cannot
-- be uniformly sufficient as a -> 0.
--
-- Prefer RiemannG2BaselineExcessR2TargetExact plus the displacement-adaptive
-- far-shell donor for the prize-facing route.
------------------------------------------------------------------------

open import Agda.Primitive using (Set₁)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

record InverseSquareR2RateTarget : Set₁ where
  field
    Scalar : Set

    t : Scalar
    A : Scalar

    nearValue : Scalar
    gammaValue : Scalar
    actualClusterValue : Scalar

    cNear : Scalar
    cGamma : Scalar
    cCluster : Scalar

    -- These propositions intentionally remain on the selected source scalar
    -- presentation.  A theorem-bearing transport into the final R2 order is a
    -- separate same-object payment.
    Positive : Scalar → Set
    Nonnegative : Scalar → Set
    _≤_ _<_ : Scalar → Scalar → Set

    invSquare : Scalar → Scalar
    add : Scalar → Scalar → Scalar
    mul : Scalar → Scalar → Scalar

    one : Scalar
    oneFourFour : Scalar

    highOrdinate : Positive t
    amplitudeNonnegative : Nonnegative A

    nearInverseSquareBound :
      _≤_ nearValue (mul cNear (invSquare t))

    gammaInverseSquareBound :
      _≤_ gammaValue (mul cGamma (invSquare t))

    actualClusterInverseSquareLower :
      _≤_ (mul cCluster (invSquare t)) actualClusterValue

    coefficientSlack :
      _<_
        (add (add cNear (mul oneFourFour A)) cGamma)
        cCluster

    sameScalarArithmeticAsLeanComposition : Set
    sameScalarArithmeticAsLeanCompositionReceipt :
      sameScalarArithmeticAsLeanComposition

    targetReference : String

open InverseSquareR2RateTarget public

record InverseSquareR2RateBoundary : Set where
  constructor inverse-square-r2-rate-boundary
  field
    farCoefficientFreeParameter : Bool
    farCoefficientFixedByQuarticDonor : Bool
    nearRateStillAnalytic : Bool
    gammaRateStillAnalytic : Bool
    actualClusterLowerRateStillAnalytic : Bool
    coefficientSlackStillAnalytic : Bool
    coefficientCompositionNeedsFreshMathematics : Bool
    coefficientCompositionNeedsCrossProverReplayOrLocalProof : Bool
    canonicalUniformAcquisitionSurface : Bool
    fixedQuarticUniformAsHorizontalDisplacementTendsToZero : Bool
    r2DerivedHere : Bool

open InverseSquareR2RateBoundary public

canonicalInverseSquareR2RateBoundary : InverseSquareR2RateBoundary
canonicalInverseSquareR2RateBoundary =
  inverse-square-r2-rate-boundary
    false
    true
    true
    true
    true
    true
    false
    true
    false
    false
    false
