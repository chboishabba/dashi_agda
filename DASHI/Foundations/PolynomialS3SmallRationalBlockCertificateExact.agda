module DASHI.Foundations.PolynomialS3SmallRationalBlockCertificateExact where

-- EXACT native 1,2,3-size S3 conjugation orbit blocks.
-- Literal S3 parity 2-block and natural 3-point standard 3-block.
-- 2x2 determinant=-2; 3x3 determinant=3. Two-sided scaled
-- integer inverse certificates avoid division before passage to Q.
-- Each source orbit is ACTUAL existing 27-code conjugacy, not a
-- same-number link. Classical rational S3 representations;
-- SOURCE-WRITTEN / KERNEL PENDING / no ESD or Monster claim.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos; negsuc)
open import Data.Integer.Base using (_+_; _*_)
import Base369 as Base
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.PolynomialS3RegularRationalBlockCertificateExact as Block

data Pair : Set where
  pair0 pair1 : Pair

data Three : Set where
  axis0 axis1 axis2 : Three

basis2 : Pair → Pair → Int
basis2 pair0 pair0 = pos 1
basis2 pair0 pair1 = pos 1
basis2 pair1 pair0 = pos 1
basis2 pair1 pair1 = negsuc 0

scaledInverse2 : Pair → Pair → Int
scaledInverse2 pair0 pair0 = pos 1
scaledInverse2 pair0 pair1 = pos 1
scaledInverse2 pair1 pair0 = pos 1
scaledInverse2 pair1 pair1 = negsuc 0

basis3 : Three → Three → Int
basis3 axis0 axis0 = pos 1
basis3 axis0 axis1 = pos 1
basis3 axis0 axis2 = pos 0
basis3 axis1 axis0 = pos 1
basis3 axis1 axis1 = pos 0
basis3 axis1 axis2 = pos 1
basis3 axis2 axis0 = pos 1
basis3 axis2 axis1 = negsuc 0
basis3 axis2 axis2 = negsuc 0

scaledInverse3 : Three → Three → Int
scaledInverse3 axis0 axis0 = pos 1
scaledInverse3 axis0 axis1 = pos 1
scaledInverse3 axis0 axis2 = pos 1
scaledInverse3 axis1 axis0 = pos 2
scaledInverse3 axis1 axis1 = negsuc 0
scaledInverse3 axis1 axis2 = negsuc 0
scaledInverse3 axis2 axis0 = negsuc 0
scaledInverse3 axis2 axis1 = pos 2
scaledInverse3 axis2 axis2 = negsuc 0

deltaTwo : Pair → Pair → Int
deltaTwo pair0 pair0 = pos 1
deltaTwo pair0 pair1 = pos 0
deltaTwo pair1 pair0 = pos 0
deltaTwo pair1 pair1 = pos 1

deltaThree : Three → Three → Int
deltaThree axis0 axis0 = pos 1
deltaThree axis0 axis1 = pos 0
deltaThree axis0 axis2 = pos 0
deltaThree axis1 axis0 = pos 0
deltaThree axis1 axis1 = pos 1
deltaThree axis1 axis2 = pos 0
deltaThree axis2 axis0 = pos 0
deltaThree axis2 axis1 = pos 0
deltaThree axis2 axis2 = pos 1

dotTwo : (A B : Pair → Pair → Int) → Pair → Pair → Int
dotTwo A B i j =
  A i pair0 * B pair0 j + A i pair1 * B pair1 j

dotThree : (A B : Three → Three → Int) → Three → Three → Int
dotThree A B i j =
  A i axis0 * B axis0 j + A i axis1 * B axis1 j
  + A i axis2 * B axis2 j

basis2ScaledInverse2 : (i j : Pair) → dotTwo basis2 scaledInverse2 i j ≡ pos 2 * deltaTwo i j
basis2ScaledInverse2 pair0 pair0 = refl
basis2ScaledInverse2 pair0 pair1 = refl
basis2ScaledInverse2 pair1 pair0 = refl
basis2ScaledInverse2 pair1 pair1 = refl

inverse2ScaledBasis2 : (i j : Pair) → dotTwo scaledInverse2 basis2 i j ≡ pos 2 * deltaTwo i j
inverse2ScaledBasis2 pair0 pair0 = refl
inverse2ScaledBasis2 pair0 pair1 = refl
inverse2ScaledBasis2 pair1 pair0 = refl
inverse2ScaledBasis2 pair1 pair1 = refl

basis3ScaledInverse3 : (i j : Three) → dotThree basis3 scaledInverse3 i j ≡ pos 3 * deltaThree i j
basis3ScaledInverse3 axis0 axis0 = refl
basis3ScaledInverse3 axis0 axis1 = refl
basis3ScaledInverse3 axis0 axis2 = refl
basis3ScaledInverse3 axis1 axis0 = refl
basis3ScaledInverse3 axis1 axis1 = refl
basis3ScaledInverse3 axis1 axis2 = refl
basis3ScaledInverse3 axis2 axis0 = refl
basis3ScaledInverse3 axis2 axis1 = refl
basis3ScaledInverse3 axis2 axis2 = refl

inverse3ScaledBasis3 : (i j : Three) → dotThree scaledInverse3 basis3 i j ≡ pos 3 * deltaThree i j
inverse3ScaledBasis3 axis0 axis0 = refl
inverse3ScaledBasis3 axis0 axis1 = refl
inverse3ScaledBasis3 axis0 axis2 = refl
inverse3ScaledBasis3 axis1 axis0 = refl
inverse3ScaledBasis3 axis1 axis1 = refl
inverse3ScaledBasis3 axis1 axis2 = refl
inverse3ScaledBasis3 axis2 axis0 = refl
inverse3ScaledBasis3 axis2 axis1 = refl
inverse3ScaledBasis3 axis2 axis2 = refl

flipPair : Perm.TriPermutation → Pair → Pair
flipPair Perm.permIdentity pair0 = pair0
flipPair Perm.permIdentity pair1 = pair1
flipPair Perm.permRotate pair0 = pair0
flipPair Perm.permRotate pair1 = pair1
flipPair Perm.permRotate2 pair0 = pair0
flipPair Perm.permRotate2 pair1 = pair1
flipPair Perm.permSwapLowMid pair0 = pair1
flipPair Perm.permSwapLowMid pair1 = pair0
flipPair Perm.permSwapLowHigh pair0 = pair1
flipPair Perm.permSwapLowHigh pair1 = pair0
flipPair Perm.permSwapMidHigh pair0 = pair1
flipPair Perm.permSwapMidHigh pair1 = pair0

fromThree : Three → Base.TriTruth
fromThree axis0 = Base.tri-low
fromThree axis1 = Base.tri-mid
fromThree axis2 = Base.tri-high

toThree : Base.TriTruth → Three
toThree Base.tri-low = axis0
toThree Base.tri-mid = axis1
toThree Base.tri-high = axis2

leftInversePoint : Perm.TriPermutation → Three → Three
leftInversePoint p i =
  toThree (Perm.applyPermutation (Perm.inversePermutation p) (fromThree i))

twoBlockAction : Perm.TriPermutation → Pair → Pair → Int
twoBlockAction p pair0 pair0 = pos 1
twoBlockAction p pair0 pair1 = pos 0
twoBlockAction p pair1 pair0 = pos 0
twoBlockAction p pair1 pair1 = Block.signInt p

threeBlockAction : Perm.TriPermutation → Three → Three → Int
threeBlockAction p axis0 axis0 = pos 1
threeBlockAction p axis0 axis1 = pos 0
threeBlockAction p axis0 axis2 = pos 0
threeBlockAction p axis1 axis0 = pos 0
threeBlockAction p axis1 axis1 = Block.rho p lowIndex lowIndex
threeBlockAction p axis1 axis2 = Block.rho p lowIndex highIndex
threeBlockAction p axis2 axis0 = pos 0
threeBlockAction p axis2 axis1 = Block.rho p highIndex lowIndex
threeBlockAction p axis2 axis2 = Block.rho p highIndex highIndex

twoBlockIntertwines :
  (p : Perm.TriPermutation) (i j : Pair) →
  basis2 (flipPair p i) j ≡ dotTwo basis2 (twoBlockAction p) i j
twoBlockIntertwines Perm.permIdentity pair0 pair0 = refl
twoBlockIntertwines Perm.permIdentity pair0 pair1 = refl
twoBlockIntertwines Perm.permIdentity pair1 pair0 = refl
twoBlockIntertwines Perm.permIdentity pair1 pair1 = refl
twoBlockIntertwines Perm.permRotate pair0 pair0 = refl
twoBlockIntertwines Perm.permRotate pair0 pair1 = refl
twoBlockIntertwines Perm.permRotate pair1 pair0 = refl
twoBlockIntertwines Perm.permRotate pair1 pair1 = refl
twoBlockIntertwines Perm.permRotate2 pair0 pair0 = refl
twoBlockIntertwines Perm.permRotate2 pair0 pair1 = refl
twoBlockIntertwines Perm.permRotate2 pair1 pair0 = refl
twoBlockIntertwines Perm.permRotate2 pair1 pair1 = refl
twoBlockIntertwines Perm.permSwapLowMid pair0 pair0 = refl
twoBlockIntertwines Perm.permSwapLowMid pair0 pair1 = refl
twoBlockIntertwines Perm.permSwapLowMid pair1 pair0 = refl
twoBlockIntertwines Perm.permSwapLowMid pair1 pair1 = refl
twoBlockIntertwines Perm.permSwapLowHigh pair0 pair0 = refl
twoBlockIntertwines Perm.permSwapLowHigh pair0 pair1 = refl
twoBlockIntertwines Perm.permSwapLowHigh pair1 pair0 = refl
twoBlockIntertwines Perm.permSwapLowHigh pair1 pair1 = refl
twoBlockIntertwines Perm.permSwapMidHigh pair0 pair0 = refl
twoBlockIntertwines Perm.permSwapMidHigh pair0 pair1 = refl
twoBlockIntertwines Perm.permSwapMidHigh pair1 pair0 = refl
twoBlockIntertwines Perm.permSwapMidHigh pair1 pair1 = refl

threeBlockIntertwines :
  (p : Perm.TriPermutation) (i j : Three) →
  basis3 (leftInversePoint p i) j ≡ dotThree basis3 (threeBlockAction p) i j
threeBlockIntertwines Perm.permIdentity axis0 axis0 = refl
threeBlockIntertwines Perm.permIdentity axis0 axis1 = refl
threeBlockIntertwines Perm.permIdentity axis0 axis2 = refl
threeBlockIntertwines Perm.permIdentity axis1 axis0 = refl
threeBlockIntertwines Perm.permIdentity axis1 axis1 = refl
threeBlockIntertwines Perm.permIdentity axis1 axis2 = refl
threeBlockIntertwines Perm.permIdentity axis2 axis0 = refl
threeBlockIntertwines Perm.permIdentity axis2 axis1 = refl
threeBlockIntertwines Perm.permIdentity axis2 axis2 = refl
threeBlockIntertwines Perm.permRotate axis0 axis0 = refl
threeBlockIntertwines Perm.permRotate axis0 axis1 = refl
threeBlockIntertwines Perm.permRotate axis0 axis2 = refl
threeBlockIntertwines Perm.permRotate axis1 axis0 = refl
threeBlockIntertwines Perm.permRotate axis1 axis1 = refl
threeBlockIntertwines Perm.permRotate axis1 axis2 = refl
threeBlockIntertwines Perm.permRotate axis2 axis0 = refl
threeBlockIntertwines Perm.permRotate axis2 axis1 = refl
threeBlockIntertwines Perm.permRotate axis2 axis2 = refl
threeBlockIntertwines Perm.permRotate2 axis0 axis0 = refl
threeBlockIntertwines Perm.permRotate2 axis0 axis1 = refl
threeBlockIntertwines Perm.permRotate2 axis0 axis2 = refl
threeBlockIntertwines Perm.permRotate2 axis1 axis0 = refl
threeBlockIntertwines Perm.permRotate2 axis1 axis1 = refl
threeBlockIntertwines Perm.permRotate2 axis1 axis2 = refl
threeBlockIntertwines Perm.permRotate2 axis2 axis0 = refl
threeBlockIntertwines Perm.permRotate2 axis2 axis1 = refl
threeBlockIntertwines Perm.permRotate2 axis2 axis2 = refl
threeBlockIntertwines Perm.permSwapLowMid axis0 axis0 = refl
threeBlockIntertwines Perm.permSwapLowMid axis0 axis1 = refl
threeBlockIntertwines Perm.permSwapLowMid axis0 axis2 = refl
threeBlockIntertwines Perm.permSwapLowMid axis1 axis0 = refl
threeBlockIntertwines Perm.permSwapLowMid axis1 axis1 = refl
threeBlockIntertwines Perm.permSwapLowMid axis1 axis2 = refl
threeBlockIntertwines Perm.permSwapLowMid axis2 axis0 = refl
threeBlockIntertwines Perm.permSwapLowMid axis2 axis1 = refl
threeBlockIntertwines Perm.permSwapLowMid axis2 axis2 = refl
threeBlockIntertwines Perm.permSwapLowHigh axis0 axis0 = refl
threeBlockIntertwines Perm.permSwapLowHigh axis0 axis1 = refl
threeBlockIntertwines Perm.permSwapLowHigh axis0 axis2 = refl
threeBlockIntertwines Perm.permSwapLowHigh axis1 axis0 = refl
threeBlockIntertwines Perm.permSwapLowHigh axis1 axis1 = refl
threeBlockIntertwines Perm.permSwapLowHigh axis1 axis2 = refl
threeBlockIntertwines Perm.permSwapLowHigh axis2 axis0 = refl
threeBlockIntertwines Perm.permSwapLowHigh axis2 axis1 = refl
threeBlockIntertwines Perm.permSwapLowHigh axis2 axis2 = refl
threeBlockIntertwines Perm.permSwapMidHigh axis0 axis0 = refl
threeBlockIntertwines Perm.permSwapMidHigh axis0 axis1 = refl
threeBlockIntertwines Perm.permSwapMidHigh axis0 axis2 = refl
threeBlockIntertwines Perm.permSwapMidHigh axis1 axis0 = refl
threeBlockIntertwines Perm.permSwapMidHigh axis1 axis1 = refl
threeBlockIntertwines Perm.permSwapMidHigh axis1 axis2 = refl
threeBlockIntertwines Perm.permSwapMidHigh axis2 axis0 = refl
threeBlockIntertwines Perm.permSwapMidHigh axis2 axis1 = refl
threeBlockIntertwines Perm.permSwapMidHigh axis2 axis2 = refl

-- Native orbit 2 is the two nontrivial 3-cycles.
nativeTwoCode : Pair → Tower.LevelTwoCode
nativeTwoCode pair0 = Perm.permutationCode Perm.permRotate
nativeTwoCode pair1 = Perm.permutationCode Perm.permRotate2

nativeTwoAction :
  (p : Perm.TriPermutation) (i : Pair) →
  Perm.conjugateCode p (nativeTwoCode i) ≡
  nativeTwoCode (flipPair p i)
nativeTwoAction Perm.permIdentity pair0 = refl
nativeTwoAction Perm.permIdentity pair1 = refl
nativeTwoAction Perm.permRotate pair0 = refl
nativeTwoAction Perm.permRotate pair1 = refl
nativeTwoAction Perm.permRotate2 pair0 = refl
nativeTwoAction Perm.permRotate2 pair1 = refl
nativeTwoAction Perm.permSwapLowMid pair0 = refl
nativeTwoAction Perm.permSwapLowMid pair1 = refl
nativeTwoAction Perm.permSwapLowHigh pair0 = refl
nativeTwoAction Perm.permSwapLowHigh pair1 = refl
nativeTwoAction Perm.permSwapMidHigh pair0 = refl
nativeTwoAction Perm.permSwapMidHigh pair1 = refl

data ThreeFamily : Set where
  constantFamily transpositionFamily : ThreeFamily

nativeThreeCode : ThreeFamily → Three → Tower.LevelTwoCode
nativeThreeCode constantFamily axis0 = (Base.tri-low , (Base.tri-low , Base.tri-low))
nativeThreeCode constantFamily axis1 = (Base.tri-mid , (Base.tri-mid , Base.tri-mid))
nativeThreeCode constantFamily axis2 = (Base.tri-high , (Base.tri-high , Base.tri-high))
nativeThreeCode transpositionFamily axis0 = (Base.tri-low , (Base.tri-high , Base.tri-mid))
nativeThreeCode transpositionFamily axis1 = (Base.tri-high , (Base.tri-mid , Base.tri-low))
nativeThreeCode transpositionFamily axis2 = (Base.tri-mid , (Base.tri-low , Base.tri-high))

nativeThreeAction :
  (p : Perm.TriPermutation) (family : ThreeFamily) (i : Three) →
  Perm.conjugateCode p (nativeThreeCode family i) ≡
  nativeThreeCode family
    (toThree (Perm.applyPermutation p (fromThree i)))
nativeThreeAction Perm.permIdentity constantFamily axis0 = refl
nativeThreeAction Perm.permIdentity constantFamily axis1 = refl
nativeThreeAction Perm.permIdentity constantFamily axis2 = refl
nativeThreeAction Perm.permIdentity transpositionFamily axis0 = refl
nativeThreeAction Perm.permIdentity transpositionFamily axis1 = refl
nativeThreeAction Perm.permIdentity transpositionFamily axis2 = refl
nativeThreeAction Perm.permRotate constantFamily axis0 = refl
nativeThreeAction Perm.permRotate constantFamily axis1 = refl
nativeThreeAction Perm.permRotate constantFamily axis2 = refl
nativeThreeAction Perm.permRotate transpositionFamily axis0 = refl
nativeThreeAction Perm.permRotate transpositionFamily axis1 = refl
nativeThreeAction Perm.permRotate transpositionFamily axis2 = refl
nativeThreeAction Perm.permRotate2 constantFamily axis0 = refl
nativeThreeAction Perm.permRotate2 constantFamily axis1 = refl
nativeThreeAction Perm.permRotate2 constantFamily axis2 = refl
nativeThreeAction Perm.permRotate2 transpositionFamily axis0 = refl
nativeThreeAction Perm.permRotate2 transpositionFamily axis1 = refl
nativeThreeAction Perm.permRotate2 transpositionFamily axis2 = refl
nativeThreeAction Perm.permSwapLowMid constantFamily axis0 = refl
nativeThreeAction Perm.permSwapLowMid constantFamily axis1 = refl
nativeThreeAction Perm.permSwapLowMid constantFamily axis2 = refl
nativeThreeAction Perm.permSwapLowMid transpositionFamily axis0 = refl
nativeThreeAction Perm.permSwapLowMid transpositionFamily axis1 = refl
nativeThreeAction Perm.permSwapLowMid transpositionFamily axis2 = refl
nativeThreeAction Perm.permSwapLowHigh constantFamily axis0 = refl
nativeThreeAction Perm.permSwapLowHigh constantFamily axis1 = refl
nativeThreeAction Perm.permSwapLowHigh constantFamily axis2 = refl
nativeThreeAction Perm.permSwapLowHigh transpositionFamily axis0 = refl
nativeThreeAction Perm.permSwapLowHigh transpositionFamily axis1 = refl
nativeThreeAction Perm.permSwapLowHigh transpositionFamily axis2 = refl
nativeThreeAction Perm.permSwapMidHigh constantFamily axis0 = refl
nativeThreeAction Perm.permSwapMidHigh constantFamily axis1 = refl
nativeThreeAction Perm.permSwapMidHigh constantFamily axis2 = refl
nativeThreeAction Perm.permSwapMidHigh transpositionFamily axis0 = refl
nativeThreeAction Perm.permSwapMidHigh transpositionFamily axis1 = refl
nativeThreeAction Perm.permSwapMidHigh transpositionFamily axis2 = refl

nativeOneCode : Tower.LevelTwoCode
nativeOneCode = Perm.permutationCode Perm.permIdentity

nativeOneFixed :
  (p : Perm.TriPermutation) →
  Perm.conjugateCode p nativeOneCode ≡ nativeOneCode
nativeOneFixed Perm.permIdentity = refl
nativeOneFixed Perm.permRotate = refl
nativeOneFixed Perm.permRotate2 = refl
nativeOneFixed Perm.permSwapLowMid = refl
nativeOneFixed Perm.permSwapLowHigh = refl
nativeOneFixed Perm.permSwapMidHigh = refl

-- This module plus the regular six-block owner covers all seven
-- orbit shapes 1+2+3+3+6+6+6; typed global assembly remains O40.
