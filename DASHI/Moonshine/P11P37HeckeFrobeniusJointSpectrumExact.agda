module DASHI.Moonshine.P11P37HeckeFrobeniusJointSpectrumExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- SageMath, "Module of supersingular points" reference manual, executable
-- p=37 supersingular and T2 data; no DOI asserted for software documentation.
--
-- DASHI CONTRIBUTION
--
-- Compute a simultaneous Hecke/Frobenius spectral fingerprint at the first
-- Ogg/non-Ogg control pair where both geometric Frobenius carriers are now
-- explicit.
--
-- p=11:
--   constant       : T2,T3,T5 =  3, 4,6 ; F = +1
--   nonconstant    : T2,T3,T5 = -2,-1,1 ; F = +1
--
-- p=37:
--   constant       : T2 =  3 ; F = +1
--   Frobenius-even : T2 =  0 ; F = +1
--   Frobenius-odd  : T2 = -2 ; F = -1
--
-- Thus the same nontrivial T2 eigenvalue -2 occurs in both characteristics but
-- sits in different Frobenius parity.  The joint operator system distinguishes
-- information that T2 spectrum or positivity alone does not.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)

import DASHI.Moonshine.P11ClassicalTwoIsogenyCorrespondenceExact as P11Pair
import DASHI.Moonshine.P11BrandtPrimeGeneratorsExact as P11
import DASHI.Moonshine.P37SageSupersingularFrobeniusExact as P37Geo

------------------------------------------------------------------------
-- p=11: Frobenius is identity on both source-certified j-classes and therefore
-- on the two-dimensional arithmetic function carrier.
------------------------------------------------------------------------

p11FrobeniusVector : P11Pair.IntPair → P11Pair.IntPair
p11FrobeniusVector v = v

p11ConstantFrobeniusEven :
  p11FrobeniusVector P11Pair.constantEigenvector
  ≡ P11Pair.constantEigenvector
p11ConstantFrobeniusEven = refl

p11NonconstantFrobeniusEven :
  p11FrobeniusVector P11Pair.nonconstantEigenvector
  ≡ P11Pair.nonconstantEigenvector
p11NonconstantFrobeniusEven = refl

p11ConstantJointT2 :
  P11.matrixAction P11.B11_2 P11Pair.constantEigenvector
  ≡ P11Pair.scalePair (+ 3) P11Pair.constantEigenvector
p11ConstantJointT2 = P11.B11_2Constant

p11ConstantJointT3 :
  P11.matrixAction P11.B11_3 P11Pair.constantEigenvector
  ≡ P11Pair.scalePair (+ 4) P11Pair.constantEigenvector
p11ConstantJointT3 = P11.B11_3Constant

p11ConstantJointT5 :
  P11.matrixAction P11.B11_5 P11Pair.constantEigenvector
  ≡ P11Pair.scalePair (+ 6) P11Pair.constantEigenvector
p11ConstantJointT5 = P11.B11_5Constant

p11NonconstantJointT2 :
  P11.matrixAction P11.B11_2 P11Pair.nonconstantEigenvector
  ≡ P11Pair.scalePair (-[1+ 1 ]) P11Pair.nonconstantEigenvector
p11NonconstantJointT2 = P11.B11_2Nonconstant

p11NonconstantJointT3 :
  P11.matrixAction P11.B11_3 P11Pair.nonconstantEigenvector
  ≡ P11Pair.scalePair (-[1+ 0 ]) P11Pair.nonconstantEigenvector
p11NonconstantJointT3 = P11.B11_3Nonconstant

p11NonconstantJointT5 :
  P11.matrixAction P11.B11_5 P11Pair.nonconstantEigenvector
  ≡ P11Pair.scalePair (+ 1) P11Pair.nonconstantEigenvector
p11NonconstantJointT5 = P11.B11_5Nonconstant

------------------------------------------------------------------------
-- p=37 integer function carrier in the Sage basis [8,27a+23,10a+20].
------------------------------------------------------------------------

record P37IntTriple : Set where
  constructor intTriple
  field
    c0 c1 c2 : ℤ

open P37IntTriple public

scaleTriple : ℤ → P37IntTriple → P37IntTriple
scaleTriple scalar v =
  intTriple (scalar *ℤ c0 v) (scalar *ℤ c1 v) (scalar *ℤ c2 v)

p37T2Action : P37IntTriple → P37IntTriple
p37T2Action v =
  intTriple
    (c0 v +ℤ c1 v +ℤ c2 v)
    (c0 v +ℤ ((+ 2) *ℤ c2 v))
    (c0 v +ℤ ((+ 2) *ℤ c1 v))

p37FrobeniusAction : P37IntTriple → P37IntTriple
p37FrobeniusAction v = intTriple (c0 v) (c2 v) (c1 v)

p37ConstantMode : P37IntTriple
p37ConstantMode = intTriple (+ 1) (+ 1) (+ 1)

p37EvenNonconstantMode : P37IntTriple
p37EvenNonconstantMode = intTriple (-[1+ 1 ]) (+ 1) (+ 1)

p37OddMode : P37IntTriple
p37OddMode = intTriple (+ 0) (+ 1) (-[1+ 0 ])

p37ConstantT2Eigen :
  p37T2Action p37ConstantMode ≡ scaleTriple (+ 3) p37ConstantMode
p37ConstantT2Eigen = refl

p37ConstantFrobeniusEven :
  p37FrobeniusAction p37ConstantMode ≡ p37ConstantMode
p37ConstantFrobeniusEven = refl

p37EvenModeT2Zero :
  p37T2Action p37EvenNonconstantMode
  ≡ scaleTriple (+ 0) p37EvenNonconstantMode
p37EvenModeT2Zero = refl

p37EvenModeFrobeniusEven :
  p37FrobeniusAction p37EvenNonconstantMode ≡ p37EvenNonconstantMode
p37EvenModeFrobeniusEven = refl

p37OddModeT2MinusTwo :
  p37T2Action p37OddMode
  ≡ scaleTriple (-[1+ 1 ]) p37OddMode
p37OddModeT2MinusTwo = refl

p37OddModeFrobeniusMinusOne :
  p37FrobeniusAction p37OddMode
  ≡ scaleTriple (-[1+ 0 ]) p37OddMode
p37OddModeFrobeniusMinusOne = refl

------------------------------------------------------------------------
-- The T2=-2 eigenvalue alone does not determine Frobenius parity.
------------------------------------------------------------------------

record MinusTwoHeckeModeParity : Set where
  constructor minusTwoHeckeModeParity
  field
    characteristic : Nat
    frobeniusEigenvalue : ℤ

p11MinusTwoModeParity : MinusTwoHeckeModeParity
p11MinusTwoModeParity = minusTwoHeckeModeParity 11 (+ 1)

p37MinusTwoModeParity : MinusTwoHeckeModeParity
p37MinusTwoModeParity = minusTwoHeckeModeParity 37 (-[1+ 0 ])

p11P37MinusTwoFrobeniusParityDiffers :
  MinusTwoHeckeModeParity.frobeniusEigenvalue p11MinusTwoModeParity
  ≡ MinusTwoHeckeModeParity.frobeniusEigenvalue p37MinusTwoModeParity →
  ⊥
p11P37MinusTwoFrobeniusParityDiffers ()

record P11P37JointSpectrumBoundary : Set where
  field
    p11JointT2T3T5FrobeniusSpectrumConstructed : Bool
    p11JointT2T3T5FrobeniusSpectrumConstructedIsTrue :
      p11JointT2T3T5FrobeniusSpectrumConstructed ≡ true

    p37JointT2FrobeniusSpectrumConstructed : Bool
    p37JointT2FrobeniusSpectrumConstructedIsTrue :
      p37JointT2FrobeniusSpectrumConstructed ≡ true

    sharedMinusTwoT2ModeHasDifferentFrobeniusParity : Bool
    sharedMinusTwoT2ModeHasDifferentFrobeniusParityIsTrue :
      sharedMinusTwoT2ModeHasDifferentFrobeniusParity ≡ true

canonicalP11P37JointSpectrumBoundary : P11P37JointSpectrumBoundary
canonicalP11P37JointSpectrumBoundary = record
  { p11JointT2T3T5FrobeniusSpectrumConstructed = true
  ; p11JointT2T3T5FrobeniusSpectrumConstructedIsTrue = refl
  ; p37JointT2FrobeniusSpectrumConstructed = true
  ; p37JointT2FrobeniusSpectrumConstructedIsTrue = refl
  ; sharedMinusTwoT2ModeHasDifferentFrobeniusParity = true
  ; sharedMinusTwoT2ModeHasDifferentFrobeniusParityIsTrue = refl
  }
