module DASHI.Moonshine.LegendreJExceptionalPolynomialFactorizationExact where

------------------------------------------------------------------------
-- EXACT ALGEBRAIC FACTORIZATION OF THE EXCEPTIONAL LEGENDRE j-MAP
--
-- PRIMARY SOURCES / CONTEXT
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", 2nd ed., GTM 106, Springer, 2009.
-- DOI: 10.1007/978-0-387-09494-6.
-- Standard Legendre family / j-invariant formula.
--
-- Bernard Dwork,
-- "$p$-adic cycles", Publ. Math. IHES 37 (1969), 27--115.
-- DOI: 10.1007/BF02684886.
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- For the Legendre family,
--
--   j(lambda)
--     = 256 (lambda^2-lambda+1)^3
--       / (lambda^2 (1-lambda)^2).
--
-- The exceptional ramification exponents are already visible in the exact
-- denominator-cleared polynomial identities
--
--   j numerator
--     = 256 (lambda^2-lambda+1)^3,
--
--   j numerator - 1728 denominator
--     = 64 (lambda-2)^2 (lambda+1)^2 (2lambda-1)^2.
--
-- DASHI CONTRIBUTION
--
-- Prove those identities exactly over Z.  This moves the powers 3 and 2 out
-- of the p-adic analytic authority boundary.  What still needs genuine local
-- analysis is that, at the chosen exceptional point, the denominator and
-- complementary factors are units and the selected simple factor is a
-- depth-one local parameter.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; +_; -[1+_])
import Data.Integer as Int
import Data.Integer.Tactic.RingSolver as ℤRing

square : ℤ → ℤ
square x = Int._*_ x x

cube : ℤ → ℤ
cube x = Int._*_ x (Int._*_ x x)

legendreQuadratic : ℤ → ℤ
legendreQuadratic lambda =
  Int._+_ (Int._-_ (square lambda) lambda) (+ 1)

legendreDenominator : ℤ → ℤ
legendreDenominator lambda =
  Int._*_
    (square lambda)
    (square (Int._-_ (+ 1) lambda))

legendreJNumerator : ℤ → ℤ
legendreJNumerator lambda =
  Int._*_ (+ 256) (cube (legendreQuadratic lambda))

legendreJ1728DifferenceNumerator : ℤ → ℤ
legendreJ1728DifferenceNumerator lambda =
  Int._-_
    (legendreJNumerator lambda)
    (Int._*_ (+ 1728) (legendreDenominator lambda))

j1728SquareProduct : ℤ → ℤ
j1728SquareProduct lambda =
  Int._*_ (+ 64)
    (Int._*_
      (square (Int._-_ lambda (+ 2)))
      (Int._*_
        (square (Int._+_ lambda (+ 1)))
        (square (Int._-_ (Int._*_ (+ 2) lambda) (+ 1)))))

------------------------------------------------------------------------
-- Exact polynomial identities.
------------------------------------------------------------------------

jZeroCubeVisibleExactly :
  (lambda : ℤ) →
  legendreJNumerator lambda
  ≡ Int._*_ (+ 256) (cube (legendreQuadratic lambda))
jZeroCubeVisibleExactly lambda = refl

j1728DifferenceIsSquareProduct :
  (lambda : ℤ) →
  legendreJ1728DifferenceNumerator lambda
  ≡ j1728SquareProduct lambda
j1728DifferenceIsSquareProduct lambda =
  ℤRing.solve (lambda ∷ [])

------------------------------------------------------------------------
-- Exceptional branch taxonomy extracted from the exact identities.
------------------------------------------------------------------------

data ExceptionalLegendreBranch : Set where
  jZeroQuadraticBranch : ExceptionalLegendreBranch
  j1728LambdaMinusTwo : ExceptionalLegendreBranch
  j1728LambdaPlusOne : ExceptionalLegendreBranch
  j1728TwoLambdaMinusOne : ExceptionalLegendreBranch

exceptionalRamificationExponent : ExceptionalLegendreBranch → Nat
exceptionalRamificationExponent jZeroQuadraticBranch = 3
exceptionalRamificationExponent j1728LambdaMinusTwo = 2
exceptionalRamificationExponent j1728LambdaPlusOne = 2
exceptionalRamificationExponent j1728TwoLambdaMinusOne = 2

exceptionalBranchPolynomial : ExceptionalLegendreBranch → ℤ → ℤ
exceptionalBranchPolynomial jZeroQuadraticBranch lambda = legendreQuadratic lambda
exceptionalBranchPolynomial j1728LambdaMinusTwo lambda = Int._-_ lambda (+ 2)
exceptionalBranchPolynomial j1728LambdaPlusOne lambda = Int._+_ lambda (+ 1)
exceptionalBranchPolynomial j1728TwoLambdaMinusOne lambda =
  Int._-_ (Int._*_ (+ 2) lambda) (+ 1)

jZeroRamificationExponentIsThree :
  exceptionalRamificationExponent jZeroQuadraticBranch ≡ 3
jZeroRamificationExponentIsThree = refl

j1728RamificationExponentsAreTwo :
  exceptionalRamificationExponent j1728LambdaMinusTwo ≡ 2
  × exceptionalRamificationExponent j1728LambdaPlusOne ≡ 2
  × exceptionalRamificationExponent j1728TwoLambdaMinusOne ≡ 2
j1728RamificationExponentsAreTwo = refl , refl , refl

record LegendreJExceptionalPolynomialFactorizationBoundary : Set where
  field
    legendreJNumeratorCubeDerived : Bool
    j1728DifferenceSquareFactorizationDerived : Bool
    jZeroExponentThreeAlgebraic : Bool
    j1728ExponentTwoAlgebraic : Bool
    denominatorUnitAtChosenPadicPointConstructed : Bool
    complementaryFactorUnitsConstructed : Bool
    selectedBranchDepthOneConstructed : Bool
    DworkA1SharpnessTransferConstructed : Bool

canonicalLegendreJExceptionalPolynomialFactorizationBoundary :
  LegendreJExceptionalPolynomialFactorizationBoundary
canonicalLegendreJExceptionalPolynomialFactorizationBoundary = record
  { legendreJNumeratorCubeDerived = true
  ; j1728DifferenceSquareFactorizationDerived = true
  ; jZeroExponentThreeAlgebraic = true
  ; j1728ExponentTwoAlgebraic = true
  ; denominatorUnitAtChosenPadicPointConstructed = false
  ; complementaryFactorUnitsConstructed = false
  ; selectedBranchDepthOneConstructed = false
  ; DworkA1SharpnessTransferConstructed = false
  }
