module DASHI.Moonshine.JInvariantComplexModulusMultiplicationCompilerExact where

------------------------------------------------------------------------
-- FACTORED ORDINARY COMPLEX MODULUS MULTIPLICATION
--
-- CROSS-POLLINATION
--
-- The composition-algebra / quaternion lanes correctly separate the
-- polynomial identity
--
--   normSq (z * w) = normSq z * normSq w
--
-- from analytic square-root facts.  The Moonshine q-power lane previously
-- exposed only the final modulus-multiplication authority.  This compiler
-- factors that authority into the exact two missing theorem families:
--
--   1. quadratic norm composition on the literal ConcreteComplex carrier;
--   2. multiplication/uniqueness laws for the selected nonnegative square root.
--
-- No quotient, order, polar branch, or q-specific theorem is manufactured.
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

import DASHI.Analysis.ConstructiveRealSpine as Real
import DASHI.Analysis.ConcreteComplex as Complex
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Moonshine.JInvariantQPowerModulusExact as QPower

record ComplexNormSquareCompositionLaws
    (C : Complex.ConstructedComplexPackage) : Set₁ where
  private
    R = Real.real (Complex.realPackage C)
  field
    normSqOne :
      Complex.normSqC (Complex.oneC {R}) ≡ Real.one R

    normSqMultiply :
      ∀ left right →
      Complex.normSqC (Complex._*C_ left right)
      ≡ Real._*_ R
          (Complex.normSqC left)
          (Complex.normSqC right)

open ComplexNormSquareCompositionLaws public

record NonnegativeSquareRootMultiplicationLaws
    (R : Real.ConstructedOrderedCompleteReal)
    (D : Polar.RealDivisionAndSquareRoot R) : Set₁ where
  field
    zeroLeOne : Real._≤_ R (Real.zero R) (Real.one R)

    mulNonnegative :
      ∀ {left right} →
      Real._≤_ R (Real.zero R) left →
      Real._≤_ R (Real.zero R) right →
      Real._≤_ R (Real.zero R) (Real._*_ R left right)

    sqrtProofIrrelevant :
      ∀ value
        (first second : Real._≤_ R (Real.zero R) value) →
      Polar.sqrtNonnegative D value first
      ≡ Polar.sqrtNonnegative D value second

    sqrtOne :
      Polar.sqrtNonnegative D (Real.one R) zeroLeOne
      ≡ Real.one R

    sqrtMultiply :
      ∀ left right
        (leftNN : Real._≤_ R (Real.zero R) left)
        (rightNN : Real._≤_ R (Real.zero R) right) →
      Polar.sqrtNonnegative D
        (Real._*_ R left right)
        (mulNonnegative leftNN rightNN)
      ≡ Real._*_ R
          (Polar.sqrtNonnegative D left leftNN)
          (Polar.sqrtNonnegative D right rightNN)

open NonnegativeSquareRootMultiplicationLaws public

sqrtRespectsEquality :
  ∀ {R : Real.ConstructedOrderedCompleteReal}
    {D : Polar.RealDivisionAndSquareRoot R}
    (S : NonnegativeSquareRootMultiplicationLaws R D)
    {left right : Real.Real R}
    (leftNN : Real._≤_ R (Real.zero R) left)
    (rightNN : Real._≤_ R (Real.zero R) right) →
  left ≡ right →
  Polar.sqrtNonnegative D left leftNN
  ≡ Polar.sqrtNonnegative D right rightNN
sqrtRespectsEquality S {left = left} leftNN rightNN refl =
  sqrtProofIrrelevant S left leftNN rightNN

compileComplexModulusMultiplicationLaws :
  ∀ {C : Complex.ConstructedComplexPackage}
    {D : Polar.RealDivisionAndSquareRoot
      (Real.real (Complex.realPackage C))}
    {F : Polar.ComplexFieldAuthority
      (Real.real (Complex.realPackage C)) D} →
  ComplexNormSquareCompositionLaws C →
  NonnegativeSquareRootMultiplicationLaws
    (Real.real (Complex.realPackage C)) D →
  QPower.ComplexModulusMultiplicationLaws C D F
compileComplexModulusMultiplicationLaws {C} {D} {F} N S = record
  { QPower.modulusOne =
      let
        R = Real.real (Complex.realPackage C)
        oneNormNN = Polar.normSqNonnegative F (Complex.oneC {R})
      in
      trans
        (sqrtRespectsEquality S
          oneNormNN
          (zeroLeOne S)
          (normSqOne N))
        (sqrtOne S)

  ; QPower.modulusMultiply = λ left right →
      let
        R = Real.real (Complex.realPackage C)
        productNN =
          Polar.normSqNonnegative F (Complex._*C_ left right)
        leftNN = Polar.normSqNonnegative F left
        rightNN = Polar.normSqNonnegative F right
        multipliedNN = mulNonnegative S leftNN rightNN
      in
      trans
        (sqrtRespectsEquality S
          productNN
          multipliedNN
          (normSqMultiply N left right))
        (sqrtMultiply S
          (Complex.normSqC left)
          (Complex.normSqC right)
          leftNN rightNN)
  }
