module DASHI.Mathematics.Automorphic.EllipticInfiniteLFunctionRoadExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

import DASHI.Mathematics.Arithmetic.EllipticCurveFrobeniusExact as Elliptic
import DASHI.Mathematics.Arithmetic.EllipticCurveGlobalLocalCoefficientExact as Global

record EllipticInfiniteAnalyticRoad
    (curve : Elliptic.ShortWeierstrassCurve)
    (localFamily : Global.EllipticCurveGlobalLocalCoefficient curve) : Set₁ where
  field
    Complex : Set
    realPart : Complex → ℚ
    finiteEulerTruncation : Nat → Complex → Complex
    dirichletPartialSum : Nat → Complex → Complex
    infiniteL : Complex → Complex
    eulerTruncationsConvergeToL : Set
    dirichletPartialSumsConvergeToL : Set
    eulerDirichletSameObject : Set
    completedL : Complex → Complex
    mellinIntegralRealization : Set
    gammaCompletionMeaning : Set
    analyticContinuation : Set
    functionalEquation : Set
    centralPoint : Complex
    centralDerivative : Nat → Complex
    analyticRank : Nat
    analyticRankMeansOrderOfVanishing : Set

open EllipticInfiniteAnalyticRoad public

record EllipticInfiniteAnalyticRoadBoundary : Set where
  constructor elliptic-infinite-analytic-road-boundary
  field
    allPrimeLocalCarrierPaid : Bool
    infiniteRoadInterfacePaid : Bool
    absoluteConvergencePaid : Bool
    infiniteEulerProductPaid : Bool
    eulerDirichletWeldPaid : Bool
    mellinRealizationPaid : Bool
    analyticContinuationPaid : Bool
    functionalEquationPaid : Bool
    analyticRankRealized : Bool
    bsdRankEqualityPaid : Bool

canonicalEllipticInfiniteAnalyticRoadBoundary :
  EllipticInfiniteAnalyticRoadBoundary
canonicalEllipticInfiniteAnalyticRoadBoundary =
  elliptic-infinite-analytic-road-boundary
    true true false false false false false false false false
