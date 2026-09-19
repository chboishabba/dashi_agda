module DASHI.Foundations.BishopNonnegativeSquareReflectionExact where

------------------------------------------------------------------------
-- CONCRETE BISHOP NONNEGATIVE SQUARE-ORDER REFLECTION
--
-- For Bishop reals x,y >= 0:
--
--     x*x <= y*y  ->  x <= y.
--
-- Proof: if y < x, then y <= x and x is positive.  Monotonicity gives
--
--     y*y <= x*y < x*x,
--
-- contradicting x*x <= y*y.  Bishop's located order turns not(y<x) into
-- x<=y.  No square-root or classical trichotomy principle is used.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm

squareReflectsOnNonnegative :
  ∀ {left right : BishopReal.ℝ} →
  BishopReal.NonNegative left →
  BishopReal.NonNegative right →
  BishopReal._≤_
    (BishopReal._*_ left left)
    (BishopReal._*_ right right) →
  BishopReal._≤_ left right
squareReflectsOnNonnegative {left} {right} leftNN rightNN squared =
  BishopP.≮⇒≥ notRightBelowLeft
  where
    notRightBelowLeft :
      ¬ BishopReal._<_ right left
    notRightBelowLeft rightBelowLeft =
      let
        rightLeLeft : BishopReal._≤_ right left
        rightLeLeft = BishopP.<⇒≤ rightBelowLeft

        leftPositive : BishopReal.Positive left
        leftPositive =
          BishopP.0<x⇒posx
            (BishopP.≤-<-trans
              (BishopP.nonNegx⇒0≤x rightNN)
              rightBelowLeft)

        rightSquareLeMixed :
          BishopReal._≤_
            (BishopReal._*_ right right)
            (BishopReal._*_ left right)
        rightSquareLeMixed =
          BishopP.*-monoʳ-≤-nonNeg
            rightLeLeft
            rightNN

        mixedLtLeftSquare :
          BishopReal._<_
            (BishopReal._*_ left right)
            (BishopReal._*_ left left)
        mixedLtLeftSquare =
          BishopP.*-monoʳ-<-pos
            leftPositive
            rightBelowLeft

        rightSquareLtLeftSquare :
          BishopReal._<_
            (BishopReal._*_ right right)
            (BishopReal._*_ left left)
        rightSquareLtLeftSquare =
          BishopP.≤-<-trans
            rightSquareLeMixed
            mixedLtLeftSquare

        impossible :
          BishopReal._<_
            (BishopReal._*_ left left)
            (BishopReal._*_ left left)
        impossible =
          BishopP.≤-<-trans squared rightSquareLtLeftSquare
      in
      BishopP.<-irrefl BishopP.≃-refl impossible

bishopNonnegativeSquareReflection :
  Norm.BishopNonnegativeSquareReflection
bishopNonnegativeSquareReflection = record
  { Norm.squareReflects = squareReflectsOnNonnegative
  }
