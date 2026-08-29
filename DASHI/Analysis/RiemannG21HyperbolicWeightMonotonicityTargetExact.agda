module DASHI.Analysis.RiemannG21HyperbolicWeightMonotonicityTargetExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Narrow analytic target for the G21 moment-ratio lane.
--
-- For an actual off-line zeta zero the intended heights satisfy
--
--   0 < a = |alpha| < p = 1/2.
--
-- At positive radii 0 < u < v, the relative-weight statements needed by the
-- covariance argument are the division-free 2x2 inequalities
--
--   cosh(p v) cosh(a u) > cosh(p u) cosh(a v),
--
--   sinh(p v) sinh(a u) > sinh(p u) sinh(a v).
--
-- Equivalently, u -> cosh(pu)/cosh(au) and
-- u -> sinh(pu)/sinh(au) are strictly increasing.  A standard calculus route
-- differentiates their logarithms:
--
--   p tanh(pu) - a tanh(au) > 0,
--   p coth(pu) - a coth(au) > 0.
--
-- This module records that exact target and does not claim DASHI has yet
-- formalized the real hyperbolic calculus needed to discharge it.
------------------------------------------------------------------------

record PositiveOrderedHeights : Set₁ where
  field
    Height : Set
    offLineHeight poleHeight : Height
    Positive : Height → Set
    StrictlyBelow : Height → Height → Set

    offLinePositive : Positive offLineHeight
    polePositive : Positive poleHeight
    offLineBelowPole : StrictlyBelow offLineHeight poleHeight

open PositiveOrderedHeights public

record PositiveOrderedRadii : Set₁ where
  field
    Radius : Set
    inner outer : Radius
    Positive : Radius → Set
    StrictlyBelow : Radius → Radius → Set

    innerPositive : Positive inner
    outerPositive : Positive outer
    innerBelowOuter : StrictlyBelow inner outer

open PositiveOrderedRadii public

record HyperbolicRelativeWeightTarget
    (heights : PositiveOrderedHeights)
    (radii : PositiveOrderedRadii) : Set₁ where
  field
    Scalar : Set
    coshWeight sinhWeight : Height heights → Radius radii → Scalar
    StrictGreater : Scalar → Scalar → Set
    multiply : Scalar → Scalar → Scalar

    coshOuterRelativeUpweight :
      StrictGreater
        (multiply
          (coshWeight (poleHeight heights) (outer radii))
          (coshWeight (offLineHeight heights) (inner radii)))
        (multiply
          (coshWeight (poleHeight heights) (inner radii))
          (coshWeight (offLineHeight heights) (outer radii)))

    sinhOuterRelativeUpweight :
      StrictGreater
        (multiply
          (sinhWeight (poleHeight heights) (outer radii))
          (sinhWeight (offLineHeight heights) (inner radii)))
        (multiply
          (sinhWeight (poleHeight heights) (inner radii))
          (sinhWeight (offLineHeight heights) (outer radii)))

    targetReading : String

open HyperbolicRelativeWeightTarget public

------------------------------------------------------------------------
-- Calculus factorization of the target.
------------------------------------------------------------------------

record HyperbolicLogDerivativeProducer
    (heights : PositiveOrderedHeights)
    (radii : PositiveOrderedRadii) : Set₁ where
  field
    Scalar : Set
    evaluateHeightRadius : Height heights → Radius radii → Scalar
    tanh coth : Scalar → Scalar
    multiply : Scalar → Scalar → Scalar
    StrictGreater : Scalar → Scalar → Set

    coshLogDerivativePositiveAtInner :
      StrictGreater
        (multiply
          (evaluateHeightRadius (poleHeight heights) (inner radii))
          (tanh (evaluateHeightRadius (poleHeight heights) (inner radii))))
        (multiply
          (evaluateHeightRadius (offLineHeight heights) (inner radii))
          (tanh (evaluateHeightRadius (offLineHeight heights) (inner radii))))

    sinhLogDerivativePositiveAtInner :
      StrictGreater
        (multiply
          (evaluateHeightRadius (poleHeight heights) (inner radii))
          (coth (evaluateHeightRadius (poleHeight heights) (inner radii))))
        (multiply
          (evaluateHeightRadius (offLineHeight heights) (inner radii))
          (coth (evaluateHeightRadius (offLineHeight heights) (inner radii))))

    derivativeSignExtendsAcrossInterval : Set
    derivativeSignToRatioMonotonicity : Set

    producerReading : String

record HyperbolicWeightMonotonicityBoundary : Set where
  constructor hyperbolicWeightMonotonicityBoundary
  field
    divisionFreeCoshMinorTargetExplicit : Bool
    divisionFreeCoshMinorTargetExplicitIsTrue :
      divisionFreeCoshMinorTargetExplicit ≡ true

    divisionFreeSinhMinorTargetExplicit : Bool
    divisionFreeSinhMinorTargetExplicitIsTrue :
      divisionFreeSinhMinorTargetExplicit ≡ true

    actualCoshRatioMonotonicityProved : Bool
    actualCoshRatioMonotonicityProvedIsFalse :
      actualCoshRatioMonotonicityProved ≡ false

    actualSinhRatioMonotonicityProved : Bool
    actualSinhRatioMonotonicityProvedIsFalse :
      actualSinhRatioMonotonicityProved ≡ false

canonicalHyperbolicWeightMonotonicityBoundary :
  HyperbolicWeightMonotonicityBoundary
canonicalHyperbolicWeightMonotonicityBoundary =
  hyperbolicWeightMonotonicityBoundary
    true refl true refl false refl false refl
