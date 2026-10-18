module DASHI.Mathematics.Arithmetic.EllipticRationalKummerOpenExact where

------------------------------------------------------------------------
-- RATIONAL 2-DESCENT KUMMER COORDINATES ON THE NONEXCEPTIONAL LOCUS
--
-- For E : y^2 = x^3 - x = x(x-1)(x+1), the chosen pair of descent
-- coordinates [x],[x-1] is defined whenever x and x-1 are nonzero.  In
-- particular the torsion point x=-1 belongs to this ordinary locus.
--
--   [x] , [x-1]
--
-- in Q*/Q*^2.  The third factor x+1 is constrained because the product of the
-- three factors is y^2.  Exceptional values at x=-1,0,1 are intentionally
-- kept separate: they require the standard torsion conventions and must be
-- welded to the existing finite C2 x C2 Kummer seed explicitly.
------------------------------------------------------------------------

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Data.Rational.Base as ℚ using (ℚ; 1ℚ; _-_; _+_; _*_; NonZero)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Foundations.QuotientSetoidSurface as Quotient
import DASHI.Mathematics.Arithmetic.EllipticCurveTwoTorsionAndBadPrimeExact as Curve
import DASHI.Mathematics.Arithmetic.RationalSquareClassSetoidExact as Square

record RationalSquareClassPairRepresentative : Set where
  constructor square-class-pair-representative
  field
    first second : Square.NonzeroRational

open RationalSquareClassPairRepresentative public

data RationalSquareClassPairEquivalent :
    RationalSquareClassPairRepresentative →
    RationalSquareClassPairRepresentative →
    Set where
  pair-equivalent :
    ∀ {left right} →
    Square.RationalSquareEquivalent
      (first left) (first right) →
    Square.RationalSquareEquivalent
      (second left) (second right) →
    RationalSquareClassPairEquivalent left right

pairSquareEquivalence :
  Quotient.IsEquivalence RationalSquareClassPairEquivalent
pairSquareEquivalence = record
  { Quotient.refl≈ =
      λ pair →
        pair-equivalent
          (Square.square-refl (first pair))
          (Square.square-refl (second pair))
  ; Quotient.sym≈ =
      λ where
        (pair-equivalent firstEq secondEq) →
          pair-equivalent
            (Square.square-sym firstEq)
            (Square.square-sym secondEq)
  ; Quotient.trans≈ =
      λ where
        (pair-equivalent firstEq secondEq)
        (pair-equivalent firstEq' secondEq') →
          pair-equivalent
            (Square.square-trans firstEq firstEq')
            (Square.square-trans secondEq secondEq')
  }

rationalSquareClassPairSetoid :
  Quotient.SetoidSurface lzero lzero
rationalSquareClassPairSetoid = record
  { Quotient.Carrier = RationalSquareClassPairRepresentative
  ; Quotient._≈_ = RationalSquareClassPairEquivalent
  ; Quotient.isEquivalence = pairSquareEquivalence
  }

record NonexceptionalKummerDomain
    (point : Curve.RationalAffinePointOnCurve) : Set where
  field
    xNonzero :
      NonZero (Curve.xCoordinate point)

    xMinusOneNonzero :
      NonZero (Curve.xCoordinate point - 1ℚ)

open NonexceptionalKummerDomain public

rationalKummerRepresentative :
  (point : Curve.RationalAffinePointOnCurve) →
  NonexceptionalKummerDomain point →
  RationalSquareClassPairRepresentative
rationalKummerRepresentative point domain =
  square-class-pair-representative
    (Square.nonzero-rational
      (Curve.xCoordinate point)
      (xNonzero domain))
    (Square.nonzero-rational
      (Curve.xCoordinate point - 1ℚ)
      (xMinusOneNonzero domain))

curveFactorization :
  (point : Curve.RationalAffinePointOnCurve) →
  Curve.yCoordinate point * Curve.yCoordinate point
  ≡
  (Curve.xCoordinate point
    * (Curve.xCoordinate point - 1ℚ))
    * (Curve.xCoordinate point + 1ℚ)
curveFactorization point =
  trans
    (Curve.liesOnCurve point)
    (solve (Curve.xCoordinate point ∷ []))

record ThirdFactorNonzero
    (point : Curve.RationalAffinePointOnCurve) : Set where
  field
    xPlusOneNonzero :
      NonZero (Curve.xCoordinate point + 1ℚ)

open ThirdFactorNonzero public

thirdKummerFactor :
  (point : Curve.RationalAffinePointOnCurve) →
  ThirdFactorNonzero point →
  Square.NonzeroRational
thirdKummerFactor point third =
  Square.nonzero-rational
    (Curve.xCoordinate point + 1ℚ)
    (xPlusOneNonzero third)

kummerThreeFactorProductIsSquare :
  (point : Curve.RationalAffinePointOnCurve) →
  (domain : NonexceptionalKummerDomain point) →
  (third : ThirdFactorNonzero point) →
  Square.value
    (first (rationalKummerRepresentative point domain))
  * Square.value
    (second (rationalKummerRepresentative point domain))
  * Square.value (thirdKummerFactor point third)
  ≡ Curve.yCoordinate point * Curve.yCoordinate point
kummerThreeFactorProductIsSquare point domain third =
  sym (curveFactorization point)

record EllipticRationalKummerOpenBoundary : Set where
  constructor elliptic-rational-kummer-open-boundary
  field
    squareClassPairSetoidPaid : Bool
    nonexceptionalDomainPaid : Bool
    nonexceptionalRationalKummerMapPaid : Bool
    cubicFactorizationPaid : Bool
    threeFactorProductSquarePaid : Bool
    exceptionalTwoTorsionValuesPaid : Bool
    finiteSeedCompatibilityPaid : Bool
    localKummerRestrictionPaid : Bool
    globalSelmerComputationPaid : Bool
    bsdRankEqualityPaid : Bool

canonicalEllipticRationalKummerOpenBoundary :
  EllipticRationalKummerOpenBoundary
canonicalEllipticRationalKummerOpenBoundary =
  elliptic-rational-kummer-open-boundary
    true true true true true false false false false false
