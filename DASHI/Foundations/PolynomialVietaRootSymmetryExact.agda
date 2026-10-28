module DASHI.Foundations.PolynomialVietaRootSymmetryExact where

------------------------------------------------------------------------
-- FINITE POLYNOMIAL ROOT SYMMETRY
-- Mathematical roots: Viete (1591); Fundamental Theorem of Algebra context.
-- Repository-owned finite rational formulas, not a proof of complex FTA.
-- Reuses the exact existing S3 permutations, rational ring, Cayley--Dickson
-- complex algebra. Roots and COEFFICIENT SLOTS are not interchangeable.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Mathematics.Algebra.CayleyDicksonRationalComplexQuaternionExact as C

record ThreeRoots : Set where
  constructor roots
  field
    firstRoot secondRoot thirdRoot : ℚ
open ThreeRoots public

-- This is the exact three-root S3 action. It is not a coefficient-slot swap.
permuteRoots : Perm.TriPermutation → ThreeRoots → ThreeRoots
permuteRoots Perm.permIdentity r = r
permuteRoots Perm.permRotate (roots a b c) = roots b c a
permuteRoots Perm.permRotate2 (roots a b c) = roots c a b
permuteRoots Perm.permSwapLowMid (roots a b c) = roots b a c
permuteRoots Perm.permSwapLowHigh (roots a b c) = roots c b a
permuteRoots Perm.permSwapMidHigh (roots a b c) = roots a c b

rootSum : ThreeRoots → ℚ
rootSum (roots a b c) = a + b + c

rootPairSum : ThreeRoots → ℚ
rootPairSum (roots a b c) = a * b + b * c + a * c

rootProduct : ThreeRoots → ℚ
rootProduct (roots a b c) = a * b * c

rootSumInvariant :
  (p : Perm.TriPermutation) (r : ThreeRoots) →
  rootSum (permuteRoots p r) ≡ rootSum r
rootSumInvariant Perm.permIdentity r = refl
rootSumInvariant Perm.permRotate (roots a b c) = Ring.solve-∀ a b c
rootSumInvariant Perm.permRotate2 (roots a b c) = Ring.solve-∀ a b c
rootSumInvariant Perm.permSwapLowMid (roots a b c) = Ring.solve-∀ a b c
rootSumInvariant Perm.permSwapLowHigh (roots a b c) = Ring.solve-∀ a b c
rootSumInvariant Perm.permSwapMidHigh (roots a b c) = Ring.solve-∀ a b c

rootPairSumInvariant :
  (p : Perm.TriPermutation) (r : ThreeRoots) →
  rootPairSum (permuteRoots p r) ≡ rootPairSum r
rootPairSumInvariant Perm.permIdentity r = refl
rootPairSumInvariant Perm.permRotate (roots a b c) = Ring.solve-∀ a b c
rootPairSumInvariant Perm.permRotate2 (roots a b c) = Ring.solve-∀ a b c
rootPairSumInvariant Perm.permSwapLowMid (roots a b c) = Ring.solve-∀ a b c
rootPairSumInvariant Perm.permSwapLowHigh (roots a b c) = Ring.solve-∀ a b c
rootPairSumInvariant Perm.permSwapMidHigh (roots a b c) = Ring.solve-∀ a b c

rootProductInvariant :
  (p : Perm.TriPermutation) (r : ThreeRoots) →
  rootProduct (permuteRoots p r) ≡ rootProduct r
rootProductInvariant Perm.permIdentity r = refl
rootProductInvariant Perm.permRotate (roots a b c) = Ring.solve-∀ a b c
rootProductInvariant Perm.permRotate2 (roots a b c) = Ring.solve-∀ a b c
rootProductInvariant Perm.permSwapLowMid (roots a b c) = Ring.solve-∀ a b c
rootProductInvariant Perm.permSwapLowHigh (roots a b c) = Ring.solve-∀ a b c
rootProductInvariant Perm.permSwapMidHigh (roots a b c) = Ring.solve-∀ a b c

-- Monic cubic with the three elementary symmetric coefficients.
evaluateMonicCubic : ThreeRoots → ℚ → ℚ
evaluateMonicCubic r x =
  x * x * x - rootSum r * (x * x)
  + rootPairSum r * x - rootProduct r

evaluateFactoredCubic : ThreeRoots → ℚ → ℚ
evaluateFactoredCubic (roots a b c) x =
  (x - a) * (x - b) * (x - c)

cubicVietaIdentity :
  (r : ThreeRoots) (x : ℚ) →
  evaluateMonicCubic r x ≡ evaluateFactoredCubic r x
cubicVietaIdentity (roots a b c) x = Ring.solve-∀ a b c x

coefficientInvariantUnderRootPermutation :
  (p : Perm.TriPermutation) (r : ThreeRoots) (x : ℚ) →
  evaluateMonicCubic (permuteRoots p r) x ≡ evaluateMonicCubic r x
coefficientInvariantUnderRootPermutation p r x
  rewrite rootSumInvariant p r
        | rootPairSumInvariant p r
        | rootProductInvariant p r = refl

firstRootIsZero :
  (r : ThreeRoots) →
  evaluateFactoredCubic r (firstRoot r) ≡ 0ℚ
firstRootIsZero (roots a b c) = Ring.solve-∀ a b c

secondRootIsZero :
  (r : ThreeRoots) →
  evaluateFactoredCubic r (secondRoot r) ≡ 0ℚ
secondRootIsZero (roots a b c) = Ring.solve-∀ a b c

thirdRootIsZero :
  (r : ThreeRoots) →
  evaluateFactoredCubic r (thirdRoot r) ≡ 0ℚ
thirdRootIsZero (roots a b c) = Ring.solve-∀ a b c

------------------------------------------------------------------------
-- x²+1=0 has the distinct rational-complex witnesses ±i.
-- This proves a concrete case, not algebraic closure of C.
------------------------------------------------------------------------

imaginaryUnit : C.RationalComplex
imaginaryUnit = C.complex 0ℚ 1ℚ

conjugateImaginary : C.RationalComplex
conjugateImaginary = C.conjugateC imaginaryUnit

squarePlusOne : C.RationalComplex → C.RationalComplex
squarePlusOne z = C._+c_ (C._*c_ z z) C.oneC

imaginaryUnitSolvesX2PlusOne :
  squarePlusOne imaginaryUnit ≡ C.zeroC
imaginaryUnitSolvesX2PlusOne = refl

negativeImaginarySolvesX2PlusOne :
  squarePlusOne conjugateImaginary ≡ C.zeroC
negativeImaginarySolvesX2PlusOne = refl
