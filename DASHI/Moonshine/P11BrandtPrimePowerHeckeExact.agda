module DASHI.Moonshine.P11BrandtPrimePowerHeckeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- Aristotle (Harmonic), editor of the user-supplied HeckeGeneral source whose
-- prime-power recurrence is formalized in AristotleHeckeRecurrenceCoreExact.
--
-- DASHI CONTRIBUTION
--
-- Extend the concrete characteristic-11 Brandt algebra from prime generators
-- to the first prime squares at ell=3 and ell=5.  For weight two the Hecke
-- relation is
--
--   B(ell)^2 = B(ell^2) + ell I.
--
-- The resulting matrices are
--
--   B_11(9)  = [[4,9],[6,7]],
--   B_11(25) = [[10,21],[14,17]].
--
-- Their joint eigenvalues are exactly the recurrence values
--
--   a_9  = (-1)^2 - 3 = -2,
--   a_25 = ( 1)^2 - 5 = -4,
--
-- while the constant Eisenstein/degree line has sigma_1(9)=13 and
-- sigma_1(25)=31.  This is operator-level recurrence on the actual Brandt
-- module, not merely a scalar coefficient calculation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11
import DASHI.Moonshine.P11ClassicalTwoIsogenySpectralExact as Spectral
import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact as Brandt
import DASHI.Moonshine.P11BrandtJointHeckeAlgebraExact as Joint
import DASHI.Moonshine.P11AristotleHeckeSquareCrossPollinationExact as Square

------------------------------------------------------------------------
-- Prime-square matrices forced by the weight-two recurrence.
------------------------------------------------------------------------

B11_9 : Brandt.P11BrandtMatrix
B11_9 = Brandt.brandtMatrix 4 9 6 7

B11_25 : Brandt.P11BrandtMatrix
B11_25 = Brandt.brandtMatrix 10 21 14 17

B3SquaredMatrix : Brandt.P11BrandtMatrix
B3SquaredMatrix = Joint.compose Brandt.B11_3 Brandt.B11_3

B5SquaredMatrix : Brandt.P11BrandtMatrix
B5SquaredMatrix = Joint.compose Brandt.B11_5 Brandt.B11_5

B3SquaredExact :
  B3SquaredMatrix ≡ Brandt.brandtMatrix 7 9 6 10
B3SquaredExact = refl

B5SquaredExact :
  B5SquaredMatrix ≡ Brandt.brandtMatrix 15 21 14 22
B5SquaredExact = refl

------------------------------------------------------------------------
-- Matrix-level recurrence checked on both coordinate basis vectors.
------------------------------------------------------------------------

B3SquaredEqualsB9Plus3IOnJ0 :
  Brandt.matrixAction B3SquaredMatrix Spectral.basisJ0
  ≡ Square.addPair
      (Brandt.matrixAction B11_9 Spectral.basisJ0)
      (P11.scalePair (+ 3) Spectral.basisJ0)
B3SquaredEqualsB9Plus3IOnJ0 = refl

B3SquaredEqualsB9Plus3IOnJ1 :
  Brandt.matrixAction B3SquaredMatrix Spectral.basisJ1
  ≡ Square.addPair
      (Brandt.matrixAction B11_9 Spectral.basisJ1)
      (P11.scalePair (+ 3) Spectral.basisJ1)
B3SquaredEqualsB9Plus3IOnJ1 = refl

B5SquaredEqualsB25Plus5IOnJ0 :
  Brandt.matrixAction B5SquaredMatrix Spectral.basisJ0
  ≡ Square.addPair
      (Brandt.matrixAction B11_25 Spectral.basisJ0)
      (P11.scalePair (+ 5) Spectral.basisJ0)
B5SquaredEqualsB25Plus5IOnJ0 = refl

B5SquaredEqualsB25Plus5IOnJ1 :
  Brandt.matrixAction B5SquaredMatrix Spectral.basisJ1
  ≡ Square.addPair
      (Brandt.matrixAction B11_25 Spectral.basisJ1)
      (P11.scalePair (+ 5) Spectral.basisJ1)
B5SquaredEqualsB25Plus5IOnJ1 = refl

------------------------------------------------------------------------
-- Joint spectral form of the same recurrences.
------------------------------------------------------------------------

B9ConstantEigenvalueThirteen :
  Brandt.matrixAction B11_9 P11.constantEigenvector
  ≡ P11.scalePair (+ 13) P11.constantEigenvector
B9ConstantEigenvalueThirteen = refl

B9NonconstantEigenvalueMinusTwo :
  Brandt.matrixAction B11_9 P11.nonconstantEigenvector
  ≡ P11.scalePair (-[1+ 1 ]) P11.nonconstantEigenvector
B9NonconstantEigenvalueMinusTwo = refl

B25ConstantEigenvalueThirtyOne :
  Brandt.matrixAction B11_25 P11.constantEigenvector
  ≡ P11.scalePair (+ 31) P11.constantEigenvector
B25ConstantEigenvalueThirtyOne = refl

B25NonconstantEigenvalueMinusFour :
  Brandt.matrixAction B11_25 P11.nonconstantEigenvector
  ≡ P11.scalePair (-[1+ 3 ]) P11.nonconstantEigenvector
B25NonconstantEigenvalueMinusFour = refl

------------------------------------------------------------------------
-- Automorphism-weight balance persists on the composite operators.
------------------------------------------------------------------------

B9Balanced : Brandt.balanced B11_9
B9Balanced = refl

B25Balanced : Brandt.balanced B11_25
B25Balanced = refl

record P11BrandtPrimePowerBoundary : Set where
  field
    ell3PrimeSquareOperatorConstructed : Bool
    ell3PrimeSquareOperatorConstructedIsTrue :
      ell3PrimeSquareOperatorConstructed ≡ true

    ell5PrimeSquareOperatorConstructed : Bool
    ell5PrimeSquareOperatorConstructedIsTrue :
      ell5PrimeSquareOperatorConstructed ≡ true

    operatorLevelPrimeSquareRecurrenceConstructed : Bool
    operatorLevelPrimeSquareRecurrenceConstructedIsTrue :
      operatorLevelPrimeSquareRecurrenceConstructed ≡ true

    automorphismBalancePreserved : Bool
    automorphismBalancePreservedIsTrue : automorphismBalancePreserved ≡ true

    independentPhi9Phi25ReductionConstructedHere : Bool
    independentPhi9Phi25ReductionConstructedHereIsFalse :
      independentPhi9Phi25ReductionConstructedHere ≡ false

canonicalP11BrandtPrimePowerBoundary : P11BrandtPrimePowerBoundary
canonicalP11BrandtPrimePowerBoundary =
  record
    { ell3PrimeSquareOperatorConstructed = true
    ; ell3PrimeSquareOperatorConstructedIsTrue = refl
    ; ell5PrimeSquareOperatorConstructed = true
    ; ell5PrimeSquareOperatorConstructedIsTrue = refl
    ; operatorLevelPrimeSquareRecurrenceConstructed = true
    ; operatorLevelPrimeSquareRecurrenceConstructedIsTrue = refl
    ; automorphismBalancePreserved = true
    ; automorphismBalancePreservedIsTrue = refl
    ; independentPhi9Phi25ReductionConstructedHere = false
    ; independentPhi9Phi25ReductionConstructedHereIsFalse = refl
    }
