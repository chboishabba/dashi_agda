module DASHI.Analysis.ConstructiveRealCubicCoefficientNormalisationExact where

open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong₂)

import DASHI.Analysis.ConstructiveRealSpine as R
import DASHI.Analysis.MarxDifferentialCore as Marx
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Norm
import DASHI.Analysis.ConstructiveRealCubicMarxDerivativeExact as Cubic

------------------------------------------------------------------------
-- NORMALISE THE CUBIC DERIVATIVE TO 3*x^2
------------------------------------------------------------------------

three :
  (real : R.ConstructedOrderedCompleteReal) →
  R.Real real
three real = R._+_ real (R._+_ real (R.one real) (R.one real)) (R.one real)

square :
  (real : R.ConstructedOrderedCompleteReal) →
  R.Real real → R.Real real
square real x = R._*_ real x x

threeTimesSquare :
  (real : R.ConstructedOrderedCompleteReal) →
  R.Real real → R.Real real
threeTimesSquare real x = R._*_ real (three real) (square real x)

threeTimesSquareIsTripleSquare :
  (real : R.ConstructedOrderedCompleteReal) →
  (x : R.Real real) →
  threeTimesSquare real x ≡ Cubic.tripleSquare real x
threeTimesSquareIsTripleSquare real x =
  trans
    (R.distribRight real
      (R._+_ real (R.one real) (R.one real))
      (R.one real)
      (square real x))
    (cong₂
      (R._+_ real)
      (trans
        (R.distribRight real (R.one real) (R.one real) (square real x))
        (cong₂
          (R._+_ real)
          (R.mulOneLeft real (square real x))
          (R.mulOneLeft real (square real x))))
      (R.mulOneLeft real (square real x)))

cubeMarxDerivativeIsThreeTimesSquare :
  {real : R.ConstructedOrderedCompleteReal} →
  (laws : Norm.ConstructedRealRingNormalisationLaws real) →
  (x : R.Real real) →
  Marx.marxDerivative (Cubic.cubeFactorisation laws) x
  ≡ threeTimesSquare real x
cubeMarxDerivativeIsThreeTimesSquare {real} laws x =
  trans
    (Cubic.cubeMarxDerivativeIsTripleSquare laws x)
    (sym (threeTimesSquareIsTripleSquare real x))
