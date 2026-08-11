module DASHI.Mathematics.Arithmetic.EllipticCurveSmallPrimeFrobeniusExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Joseph H. Silverman,
-- "The Arithmetic of Elliptic Curves", second edition.
-- DOI: 10.1007/978-0-387-09494-6.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms".
-- DOI: 10.1007/978-0-387-27226-9.
--
-- DASHI CONTRIBUTION
--
-- Extend the exact local BSD seed for E : y^2 = x^3 - x from p=5 to the
-- finite good-prime set
--
--   3, 5, 7, 11, 13, 17, 19.
--
-- Each row contains the complete fibre-count vector over x in F_p, its affine
-- and projective totals, the signed Frobenius trace a_p=p+1-#E(F_p), and an
-- explicit natural-number Hasse certificate |a_p|^2 <= 4p.
--
-- The p=5 vector is re-used from the literal 25-pair enumeration already in
-- the repository.  The other finite vectors are closed data tables whose sums,
-- trace formulae and Hasse rows reduce inside Agda.  A generic finite-field
-- enumerator remains a separate computational refinement.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Mathematics.Arithmetic.EllipticCurveF5PointEnumerationExact as F5

sumNatList : List Nat → Nat
sumNatList [] = zero
sumNatList (x ∷ xs) = x + sumNatList xs

natToRational : Nat → ℚ
natToRational zero = 0ℚ
natToRational (suc n) = 1ℚ + natToRational n

fourTimes : Nat → Nat
fourTimes n = n + n + n + n

leftLessEqualAddition : ∀ left right → left ≤ left + right
leftLessEqualAddition zero right = z≤n
leftLessEqualAddition (suc left) right =
  s≤s (leftLessEqualAddition left right)

data SignedNatural : Set where
  nonnegative : Nat → SignedNatural
  negative : Nat → SignedNatural

signedMagnitude : SignedNatural → Nat
signedMagnitude (nonnegative magnitude) = magnitude
signedMagnitude (negative magnitude) = magnitude

signedToRational : SignedNatural → ℚ
signedToRational (nonnegative magnitude) = natToRational magnitude
signedToRational (negative magnitude) = - natToRational magnitude

signedSquare : SignedNatural → Nat
signedSquare value = signedMagnitude value * signedMagnitude value

record SmallPrimeFrobeniusRow : Set where
  constructor smallPrimeFrobeniusRow
  field
    prime : Nat
    affineFibreCounts : List Nat
    affinePointCount : Nat
    affineCountChecked : sumNatList affineFibreCounts ≡ affinePointCount
    projectivePointCount : Nat
    pointAtInfinityChecked : suc affinePointCount ≡ projectivePointCount
    frobeniusTrace : SignedNatural
    traceFormulaChecked :
      signedToRational frobeniusTrace
      ≡ natToRational prime + 1ℚ - natToRational projectivePointCount
    traceSquare : Nat
    traceSquareChecked : traceSquare ≡ signedSquare frobeniusTrace
    hasseRightSide : Nat
    hasseRightSideChecked : hasseRightSide ≡ fourTimes prime
    hasseBound : traceSquare ≤ hasseRightSide

open SmallPrimeFrobeniusRow public

p3Row : SmallPrimeFrobeniusRow
p3Row = smallPrimeFrobeniusRow
  3
  (1 ∷ 1 ∷ 1 ∷ [])
  3 refl
  4 refl
  (nonnegative 0) (solve [])
  0 refl
  12 refl
  z≤n

p5Row : SmallPrimeFrobeniusRow
p5Row = smallPrimeFrobeniusRow
  5
  F5.affineFibreCounts
  7 F5.affinePointCountIsSeven
  8 refl
  (negative 2) (solve [])
  4 refl
  20 refl
  (leftLessEqualAddition 4 16)

p7Row : SmallPrimeFrobeniusRow
p7Row = smallPrimeFrobeniusRow
  7
  (1 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 2 ∷ 1 ∷ [])
  7 refl
  8 refl
  (nonnegative 0) (solve [])
  0 refl
  28 refl
  z≤n

p11Row : SmallPrimeFrobeniusRow
p11Row = smallPrimeFrobeniusRow
  11
  (1 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 2 ∷ 0 ∷ 2 ∷ 2 ∷ 1 ∷ [])
  11 refl
  12 refl
  (nonnegative 0) (solve [])
  0 refl
  44 refl
  z≤n

p13Row : SmallPrimeFrobeniusRow
p13Row = smallPrimeFrobeniusRow
  13
  (1 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ [])
  7 refl
  8 refl
  (nonnegative 6) (solve [])
  36 refl
  52 refl
  (leftLessEqualAddition 36 16)

p17Row : SmallPrimeFrobeniusRow
p17Row = smallPrimeFrobeniusRow
  17
  (1 ∷ 1 ∷ 0 ∷ 0 ∷ 2 ∷ 2 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 2 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ [])
  15 refl
  16 refl
  (nonnegative 2) (solve [])
  4 refl
  68 refl
  (leftLessEqualAddition 4 64)

p19Row : SmallPrimeFrobeniusRow
p19Row = smallPrimeFrobeniusRow
  19
  (1 ∷ 1 ∷ 2 ∷ 2 ∷ 0 ∷ 2 ∷ 2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 2 ∷ 2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ [])
  19 refl
  20 refl
  (nonnegative 0) (solve [])
  0 refl
  76 refl
  z≤n

smallPrimeRows : List SmallPrimeFrobeniusRow
smallPrimeRows =
  p3Row ∷ p5Row ∷ p7Row ∷ p11Row ∷ p13Row ∷ p17Row ∷ p19Row ∷ []

smallPrimeTraceVector : List SignedNatural
smallPrimeTraceVector =
  nonnegative 0
  ∷ negative 2
  ∷ nonnegative 0
  ∷ nonnegative 0
  ∷ nonnegative 6
  ∷ nonnegative 2
  ∷ nonnegative 0
  ∷ []

allSmallPrimeHasseBounds :
  traceSquare p3Row ≤ hasseRightSide p3Row
  × traceSquare p5Row ≤ hasseRightSide p5Row
  × traceSquare p7Row ≤ hasseRightSide p7Row
  × traceSquare p11Row ≤ hasseRightSide p11Row
  × traceSquare p13Row ≤ hasseRightSide p13Row
  × traceSquare p17Row ≤ hasseRightSide p17Row
  × traceSquare p19Row ≤ hasseRightSide p19Row
allSmallPrimeHasseBounds =
  hasseBound p3Row
  , hasseBound p5Row
  , hasseBound p7Row
  , hasseBound p11Row
  , hasseBound p13Row
  , hasseBound p17Row
  , hasseBound p19Row
