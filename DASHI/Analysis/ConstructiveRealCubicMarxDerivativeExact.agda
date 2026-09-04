module DASHI.Analysis.ConstructiveRealCubicMarxDerivativeExact where

open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong; cong₂)

import DASHI.Analysis.ConstructiveRealSpine as R
import DASHI.Analysis.MarxDifferentialCore as Marx
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Norm

------------------------------------------------------------------------
-- EXACT CUBIC DERIVATIVE ON THE CONSTRUCTED-REAL MARX CARRIER
--
-- This is finite-difference algebra, not a limit assumption.  The existing
-- Marx product rule and constructed-real ring normalization derive
--
--   D(x^3) = x^2 + x^2 + x^2.
--
-- A later field/division authority may re-express this as 3*x^2 and therefore
-- identify (1/3)u^3 as a primitive of u^2.  Improper-integral and endpoint
-- theorems remain separate analytic payments.
------------------------------------------------------------------------

private
  algebra :
    {real : R.ConstructedOrderedCompleteReal} →
    Norm.ConstructedRealRingNormalisationLaws real →
    Marx.MarxAlgebra
  algebra = Norm.ordinaryConstructiveRealMarxAlgebra

squareFactorisation :
  {real : R.ConstructedOrderedCompleteReal} →
  (laws : Norm.ConstructedRealRingNormalisationLaws real) →
  Marx.MarxFactorisation
    (algebra laws)
    (Marx.multiplyFunctions {A = algebra laws}
      Marx.identityFunction Marx.identityFunction)
squareFactorisation laws =
  Marx.productFactorisations Marx.identityFactorisation Marx.identityFactorisation

cubeFactorisation :
  {real : R.ConstructedOrderedCompleteReal} →
  (laws : Norm.ConstructedRealRingNormalisationLaws real) →
  Marx.MarxFactorisation
    (algebra laws)
    (Marx.multiplyFunctions {A = algebra laws}
      (Marx.multiplyFunctions {A = algebra laws}
        Marx.identityFunction Marx.identityFunction)
      Marx.identityFunction)
cubeFactorisation laws =
  Marx.productFactorisations
    (squareFactorisation laws)
    Marx.identityFactorisation

tripleSquare :
  (real : R.ConstructedOrderedCompleteReal) →
  R.Real real → R.Real real
tripleSquare real x =
  R._+_ real
    (R._+_ real (R._*_ real x x) (R._*_ real x x))
    (R._*_ real x x)

cubeMarxDerivativeIsTripleSquare :
  {real : R.ConstructedOrderedCompleteReal} →
  (laws : Norm.ConstructedRealRingNormalisationLaws real) →
  (x : R.Real real) →
  Marx.marxDerivative (cubeFactorisation laws) x
  ≡ tripleSquare real x
cubeMarxDerivativeIsTripleSquare {real} laws x
  rewrite Marx.productRule
    (squareFactorisation laws)
    Marx.identityFactorisation
    x
  | Marx.productRule
    Marx.identityFactorisation
    Marx.identityFactorisation
    x
  | Marx.identityDerivative x =
  trans
    (cong₂
      (R._+_ real)
      (cong
        (λ t → R._*_ real t x)
        (cong₂
          (R._+_ real)
          (R.mulOneLeft real x)
          (R.mulOneRight real x)))
      (R.mulOneRight real (R._*_ real x x)))
    (cong
      (λ t → R._+_ real t (R._*_ real x x))
      (R.distribRight real x x x))
