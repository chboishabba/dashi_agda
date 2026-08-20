module DASHI.Moonshine.LegendreExceptionalBranchSimpleRootExact where

------------------------------------------------------------------------
-- ALGEBRAIC SIMPLE-ROOT / COMPLEMENTARY-FACTOR GEOMETRY
--
-- PRIMARY SOURCES / CONTEXT
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", 2nd ed., GTM 106, Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publ. Math. IHES 37 (1969), 27--115.
-- DOI: 10.1007/BF02684886.
--
-- DASHI CONTRIBUTION
--
-- The exceptional Legendre powers 3 and 2 are already exact polynomial
-- factors.  This file lowers the local-unit boundary further by proving the
-- integral identities which show why the selected inner branch is simple and
-- why simultaneous vanishing of complementary exceptional factors is confined
-- to the low characteristics 2 or 3.
--
-- For q(lambda)=lambda^2-lambda+1,
--
--   q(lambda)-q(lambda0)
--     = (lambda-lambda0)(lambda+lambda0-1).
--
-- At a q-root lambda0 the complementary factor becomes 2 lambda0 - 1.
-- The exact identity
--
--   4 q(lambda0) = (2 lambda0 - 1)^2 + 3
--
-- shows that simultaneous vanishing forces characteristic 3.  Thus the j=0
-- inner branch is simple for characteristic >3.
--
-- For j=1728 the three selected factors have roots
--
--   lambda=2, lambda=-1, 2lambda=1.
--
-- Pairwise collisions are separated by a factor of 3.  The integral roots
-- lambda=2,-1 avoid the Legendre denominator directly; for 2lambda=1 the
-- denominator-cleared coordinate mu=2lambda gives
--
--   16 lambda^2(1-lambda)^2 = mu^2(2-mu)^2,
--
-- which equals 1 at mu=1.  Residue-unit promotion remains a local-ring task.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Integer as Int
import Data.Integer.Tactic.RingSolver as ℤRing

import DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact as Legendre

------------------------------------------------------------------------
-- j=0 simple-root factorization.
------------------------------------------------------------------------

quadraticDifferenceFactors :
  (lambda lambda0 : ℤ) →
  Int._-_ (Legendre.legendreQuadratic lambda)
          (Legendre.legendreQuadratic lambda0)
  ≡ Int._*_
      (Int._-_ lambda lambda0)
      (Int._-_ (Int._+_ lambda lambda0) (+ 1))
quadraticDifferenceFactors lambda lambda0 =
  ℤRing.solve (lambda ∷ lambda0 ∷ [])

fourTimesQuadraticIsDerivativeSquarePlusThree :
  (lambda0 : ℤ) →
  Int._*_ (+ 4) (Legendre.legendreQuadratic lambda0)
  ≡ Int._+_
      (Int._*_
        (Int._-_ (Int._*_ (+ 2) lambda0) (+ 1))
        (Int._-_ (Int._*_ (+ 2) lambda0) (+ 1)))
      (+ 3)
fourTimesQuadraticIsDerivativeSquarePlusThree lambda0 =
  ℤRing.solve (lambda0 ∷ [])

------------------------------------------------------------------------
-- j=1728 pairwise root separations.
--
-- These exact differences become unit obstructions away from characteristic 3.
------------------------------------------------------------------------

minusTwoVsPlusOneSeparation :
  (lambda : ℤ) →
  Int._-_ (Int._+_ lambda (+ 1)) (Int._-_ lambda (+ 2)) ≡ + 3
minusTwoVsPlusOneSeparation lambda = ℤRing.solve (lambda ∷ [])

minusTwoVsTwoLambdaMinusOneSeparation :
  (lambda : ℤ) →
  Int._-_ (Int._-_ (Int._*_ (+ 2) lambda) (+ 1))
          (Int._*_ (+ 2) (Int._-_ lambda (+ 2)))
  ≡ + 3
minusTwoVsTwoLambdaMinusOneSeparation lambda =
  ℤRing.solve (lambda ∷ [])

plusOneVsTwoLambdaMinusOneSeparation :
  (lambda : ℤ) →
  Int._+_
    (Int._-_ (Int._*_ (+ 2) lambda) (+ 1))
    (Int._*_ (-[1+ 1 ]) (Int._+_ lambda (+ 1)))
  ≡ -[1+ 2 ]
plusOneVsTwoLambdaMinusOneSeparation lambda =
  ℤRing.solve (lambda ∷ [])

------------------------------------------------------------------------
-- Denominator avoidance at the three j=1728 branch roots.
------------------------------------------------------------------------

lambdaTwoDenominator : Legendre.legendreDenominator (+ 2) ≡ + 4
lambdaTwoDenominator = refl

lambdaMinusOneDenominator :
  Legendre.legendreDenominator (-[1+ 0 ]) ≡ + 4
lambdaMinusOneDenominator = refl

clearedHalfDenominator : ℤ → ℤ
clearedHalfDenominator mu =
  Int._*_ (Int._*_ mu mu)
    (Int._*_
      (Int._-_ (+ 2) mu)
      (Int._-_ (+ 2) mu))

halfRootDenominatorCleared : clearedHalfDenominator (+ 1) ≡ + 1
halfRootDenominatorCleared = refl

record LegendreExceptionalBranchSimpleRootBoundary : Set where
  field
    jZeroDifferenceFactorizationDerived : Bool
    jZeroDerivativeObstructionThreeDerived : Bool
    j1728ComplementSeparationsDerived : Bool
    j1728DenominatorAvoidanceDerived : Bool
    characteristicTwoThreeExceptionalVisible : Bool
    residueNonzeroImpliesPadicUnitConstructedHere : Bool
    chosenPadicParameterDepthOneConstructedHere : Bool

canonicalLegendreExceptionalBranchSimpleRootBoundary :
  LegendreExceptionalBranchSimpleRootBoundary
canonicalLegendreExceptionalBranchSimpleRootBoundary = record
  { jZeroDifferenceFactorizationDerived = true
  ; jZeroDerivativeObstructionThreeDerived = true
  ; j1728ComplementSeparationsDerived = true
  ; j1728DenominatorAvoidanceDerived = true
  ; characteristicTwoThreeExceptionalVisible = true
  ; residueNonzeroImpliesPadicUnitConstructedHere = false
  ; chosenPadicParameterDepthOneConstructedHere = false
  }
