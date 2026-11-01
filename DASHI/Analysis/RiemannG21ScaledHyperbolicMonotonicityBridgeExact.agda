module DASHI.Analysis.RiemannG21ScaledHyperbolicMonotonicityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG21HyperbolicWeightMonotonicityTargetExact as Target

------------------------------------------------------------------------
-- Smallest calculus bridge for the G21 hyperbolic-weight gate.
--
-- Put x = a u and y = p u with 0 < a < p and u > 0.  Then x < y.
-- The two log-derivative signs required upstream are exactly consequences of
-- strict monotonicity on the positive axis of
--
--   F_tanh(x) = x tanh x,
--   F_coth(x) = x coth x.
--
-- Indeed
--
--   p tanh(pu) - a tanh(au)
--     = (1/u) [ (pu)tanh(pu) - (au)tanh(au) ],
--
-- and similarly for coth.  No division is needed in the order formulation:
-- strict increase of F at au < pu gives the desired scaled comparison.
--
-- This module owns only that factorization.  The real-calculus theorem that
-- F_tanh and F_coth are strictly increasing on (0,inf) remains a separate
-- analytic producer obligation.
------------------------------------------------------------------------

record PositiveScaledOrder : Set₁ where
  field
    Scalar : Set
    offLineScale poleScale radius : Scalar
    multiply : Scalar → Scalar → Scalar
    StrictlyPositive : Scalar → Set
    StrictlyBelow : Scalar → Scalar → Set

    offLineScalePositive : StrictlyPositive offLineScale
    poleScalePositive : StrictlyPositive poleScale
    radiusPositive : StrictlyPositive radius
    offLineScaleBelowPoleScale : StrictlyBelow offLineScale poleScale
    scalingPreservesStrictOrder :
      StrictlyBelow
        (multiply offLineScale radius)
        (multiply poleScale radius)

open PositiveScaledOrder public

record ScaledHyperbolicMonotonicity
    (order : PositiveScaledOrder) : Set₁ where
  field
    tanh coth : Scalar order → Scalar order
    StrictlyBelow : Scalar order → Scalar order → Set
    multiply : Scalar order → Scalar order → Scalar order

    scaledTanhStrictlyIncreasing :
      StrictlyBelow
        (multiply
          (multiply (offLineScale order) (radius order))
          (tanh (multiply (offLineScale order) (radius order))))
        (multiply
          (multiply (poleScale order) (radius order))
          (tanh (multiply (poleScale order) (radius order))))

    scaledCothStrictlyIncreasing :
      StrictlyBelow
        (multiply
          (multiply (offLineScale order) (radius order))
          (coth (multiply (offLineScale order) (radius order))))
        (multiply
          (multiply (poleScale order) (radius order))
          (coth (multiply (poleScale order) (radius order))))

    monotonicityReading : String

open ScaledHyperbolicMonotonicity public

------------------------------------------------------------------------
-- Source-facing calculus target.  The usual derivative route is
--
--   d/dx [x tanh x] = tanh x + x sech^2 x > 0,
--
--   d/dx [x coth x]
--     = coth x - x csch^2 x
--     = (sinh x cosh x - x) / sinh^2 x > 0,
--
-- with sinh x cosh x > x for x > 0.  These are intentionally represented as
-- obligations rather than postulates or claimed theorems.
------------------------------------------------------------------------

record ScaledHyperbolicCalculusProducer : Set₁ where
  field
    Real : Set
    zero : Real
    tanh coth sinh cosh : Real → Real
    add multiply subtract : Real → Real → Real
    square : Real → Real
    StrictGreater : Real → Real → Set
    Positive : Real → Set

    tanhScaledDerivative : Real → Real
    cothScaledDerivative : Real → Real

    tanhScaledDerivativeFormula :
      (x : Real) → Set

    cothScaledDerivativeFormula :
      (x : Real) → Set

    sinhCoshDominatesIdentity :
      (x : Real) → Positive x → Set

    tanhScaledDerivativePositive :
      (x : Real) → Positive x → StrictGreater (tanhScaledDerivative x) zero

    cothScaledDerivativePositive :
      (x : Real) → Positive x → StrictGreater (cothScaledDerivative x) zero

    derivativePositiveImpliesStrictIncrease : Set
    producerReading : String

record ScaledHyperbolicMonotonicityBoundary : Set where
  constructor scaledHyperbolicMonotonicityBoundary
  field
    logDerivativeReducedToXTanhX : Bool
    logDerivativeReducedToXTanhXIsTrue : logDerivativeReducedToXTanhX ≡ true
    logDerivativeReducedToXCothX : Bool
    logDerivativeReducedToXCothXIsTrue : logDerivativeReducedToXCothX ≡ true
    actualXTanhXMonotonicityDerived : Bool
    actualXTanhXMonotonicityDerivedIsFalse : actualXTanhXMonotonicityDerived ≡ false
    actualXCothXMonotonicityDerived : Bool
    actualXCothXMonotonicityDerivedIsFalse : actualXCothXMonotonicityDerived ≡ false

canonicalScaledHyperbolicMonotonicityBoundary :
  ScaledHyperbolicMonotonicityBoundary
canonicalScaledHyperbolicMonotonicityBoundary =
  scaledHyperbolicMonotonicityBoundary
    true refl true refl false refl false refl
