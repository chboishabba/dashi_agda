module DASHI.Foundations.PolynomialS3RationalBlockFieldIsomorphismExact where

-- RATIONAL FORWARD/BACKWARD FIELD COORDINATES FOR SOURCE-CERTIFIED
-- 2-, 3- AND 6-ELEMENT S3 PERMUTATION ORBITS.
--
-- Source integer matrices carry exact 2/3/54-scaled two-sided
-- inverses. Here those identities are lifted into Q via the already
-- imported DASHI rational RingSolver (original Vieta owner pattern).
-- Each block has pointwise inverse in both directions and an
-- equivariant S3-coordinate action. Their actual 27-code
-- glue is the separate original seven-orbit block assembly owner.
--
-- Classical S3 representation, Serre (1977); implementation #1414.
-- Kernel typechecking PENDING. This proves nothing about generic
-- quintic Galois groups, wild Hatcher exteriors or Monster 3B.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Int using (Int; pos)
open import Data.Rational.Base using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.PolynomialS3SmallRationalBlockCertificateExact as Small
import DASHI.Foundations.PolynomialS3RegularRationalBlockCertificateExact as Big

asRational : Int → ℚ
asRational z = z / 1


Field2 : Set
Field2 = Small.Pair → ℚ

dotRational2 :
  (M : Small.Pair → Small.Pair → Int)
  (f : Field2) → Small.Pair → ℚ
dotRational2 M f i =
  asRational (M i Small.pair0) * f Small.pair0
    + asRational (M i Small.pair1) * f Small.pair1

fromCoordinates2 : Field2 → Field2
fromCoordinates2 f i = dotRational2 Small.basis2 f i

toCoordinates2 : Field2 → Field2
toCoordinates2 f i =
  dotRational2 Small.scaledInverse2 f i * (pos 1 / 2)

fromToCoordinates2 :
  (f : Field2) (i : Small.Pair) →
  fromCoordinates2 (toCoordinates2 f) i ≡ f i
fromToCoordinates2 f Small.pair0 = Ring.solve-∀ f Small.pair0 f Small.pair1
fromToCoordinates2 f Small.pair1 = Ring.solve-∀ f Small.pair0 f Small.pair1

toFromCoordinates2 :
  (f : Field2) (i : Small.Pair) →
  toCoordinates2 (fromCoordinates2 f) i ≡ f i
toFromCoordinates2 f Small.pair0 = Ring.solve-∀ f Small.pair0 f Small.pair1
toFromCoordinates2 f Small.pair1 = Ring.solve-∀ f Small.pair0 f Small.pair1

sourceAction2 :
  Perm.TriPermutation → Field2 → Field2
sourceAction2 p f i = f (Small.flipPair p i)

coordinateAction2 :
  Perm.TriPermutation → Field2 → Field2
coordinateAction2 p f i =
  dotRational2 (Small.twoBlockAction p) f i

toCoordinates2Intertwines :
  (p : Perm.TriPermutation) (f : Field2) (i : Small.Pair) →
  toCoordinates2 (sourceAction2 p f) i ≡
  coordinateAction2 p (toCoordinates2 f) i
toCoordinates2Intertwines Perm.permIdentity f Small.pair0 = Ring.solve-∀ f Small.pair0 f Small.pair1
toCoordinates2Intertwines Perm.permIdentity f Small.pair1 = Ring.solve-∀ f Small.pair0 f Small.pair1
toCoordinates2Intertwines Perm.permRotate f Small.pair0 = Ring.solve-∀ f Small.pair0 f Small.pair1
toCoordinates2Intertwines Perm.permRotate f Small.pair1 = Ring.solve-∀ f Small.pair0 f Small.pair1
toCoordinates2Intertwines Perm.permRotate2 f Small.pair0 = Ring.solve-∀ f Small.pair0 f Small.pair1
toCoordinates2Intertwines Perm.permRotate2 f Small.pair1 = Ring.solve-∀ f Small.pair0 f Small.pair1
toCoordinates2Intertwines Perm.permSwapLowMid f Small.pair0 = Ring.solve-∀ f Small.pair0 f Small.pair1
toCoordinates2Intertwines Perm.permSwapLowMid f Small.pair1 = Ring.solve-∀ f Small.pair0 f Small.pair1
toCoordinates2Intertwines Perm.permSwapLowHigh f Small.pair0 = Ring.solve-∀ f Small.pair0 f Small.pair1
toCoordinates2Intertwines Perm.permSwapLowHigh f Small.pair1 = Ring.solve-∀ f Small.pair0 f Small.pair1
toCoordinates2Intertwines Perm.permSwapMidHigh f Small.pair0 = Ring.solve-∀ f Small.pair0 f Small.pair1
toCoordinates2Intertwines Perm.permSwapMidHigh f Small.pair1 = Ring.solve-∀ f Small.pair0 f Small.pair1

Field3 : Set
Field3 = Small.Three → ℚ

dotRational3 :
  (M : Small.Three → Small.Three → Int)
  (f : Field3) → Small.Three → ℚ
dotRational3 M f i =
  asRational (M i Small.axis0) * f Small.axis0
    + asRational (M i Small.axis1) * f Small.axis1
    + asRational (M i Small.axis2) * f Small.axis2

fromCoordinates3 : Field3 → Field3
fromCoordinates3 f i = dotRational3 Small.basis3 f i

toCoordinates3 : Field3 → Field3
toCoordinates3 f i =
  dotRational3 Small.scaledInverse3 f i * (pos 1 / 3)

fromToCoordinates3 :
  (f : Field3) (i : Small.Three) →
  fromCoordinates3 (toCoordinates3 f) i ≡ f i
fromToCoordinates3 f Small.axis0 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
fromToCoordinates3 f Small.axis1 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
fromToCoordinates3 f Small.axis2 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2

toFromCoordinates3 :
  (f : Field3) (i : Small.Three) →
  toCoordinates3 (fromCoordinates3 f) i ≡ f i
toFromCoordinates3 f Small.axis0 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toFromCoordinates3 f Small.axis1 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toFromCoordinates3 f Small.axis2 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2

sourceAction3 :
  Perm.TriPermutation → Field3 → Field3
sourceAction3 p f i = f (Small.leftInversePoint p i)

coordinateAction3 :
  Perm.TriPermutation → Field3 → Field3
coordinateAction3 p f i =
  dotRational3 (Small.threeBlockAction p) f i

toCoordinates3Intertwines :
  (p : Perm.TriPermutation) (f : Field3) (i : Small.Three) →
  toCoordinates3 (sourceAction3 p f) i ≡
  coordinateAction3 p (toCoordinates3 f) i
toCoordinates3Intertwines Perm.permIdentity f Small.axis0 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permIdentity f Small.axis1 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permIdentity f Small.axis2 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permRotate f Small.axis0 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permRotate f Small.axis1 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permRotate f Small.axis2 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permRotate2 f Small.axis0 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permRotate2 f Small.axis1 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permRotate2 f Small.axis2 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permSwapLowMid f Small.axis0 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permSwapLowMid f Small.axis1 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permSwapLowMid f Small.axis2 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis0 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis1 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis2 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis0 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis1 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2
toCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis2 = Ring.solve-∀ f Small.axis0 f Small.axis1 f Small.axis2

Field6 : Set
Field6 = Big.Six → ℚ

dotRational6 :
  (M : Big.Six → Big.Six → Int)
  (f : Field6) → Big.Six → ℚ
dotRational6 M f i =
  asRational (M i Big.slot0) * f Big.slot0
    + asRational (M i Big.slot1) * f Big.slot1
    + asRational (M i Big.slot2) * f Big.slot2
    + asRational (M i Big.slot3) * f Big.slot3
    + asRational (M i Big.slot4) * f Big.slot4
    + asRational (M i Big.slot5) * f Big.slot5

fromCoordinates6 : Field6 → Field6
fromCoordinates6 f i = dotRational6 Big.basis6 f i

toCoordinates6 : Field6 → Field6
toCoordinates6 f i =
  dotRational6 Big.scaledInverse6 f i * (pos 1 / 54)

fromToCoordinates6 :
  (f : Field6) (i : Big.Six) →
  fromCoordinates6 (toCoordinates6 f) i ≡ f i
fromToCoordinates6 f Big.slot0 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
fromToCoordinates6 f Big.slot1 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
fromToCoordinates6 f Big.slot2 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
fromToCoordinates6 f Big.slot3 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
fromToCoordinates6 f Big.slot4 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
fromToCoordinates6 f Big.slot5 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5

toFromCoordinates6 :
  (f : Field6) (i : Big.Six) →
  toCoordinates6 (fromCoordinates6 f) i ≡ f i
toFromCoordinates6 f Big.slot0 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toFromCoordinates6 f Big.slot1 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toFromCoordinates6 f Big.slot2 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toFromCoordinates6 f Big.slot3 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toFromCoordinates6 f Big.slot4 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toFromCoordinates6 f Big.slot5 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5

sourceAction6 :
  Perm.TriPermutation → Field6 → Field6
sourceAction6 p f i = f (Big.leftInverseRow p i)

coordinateAction6 :
  Perm.TriPermutation → Field6 → Field6
coordinateAction6 p f i =
  dotRational6 (Big.blockAction p) f i

toCoordinates6Intertwines :
  (p : Perm.TriPermutation) (f : Field6) (i : Big.Six) →
  toCoordinates6 (sourceAction6 p f) i ≡
  coordinateAction6 p (toCoordinates6 f) i
toCoordinates6Intertwines Perm.permIdentity f Big.slot0 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permIdentity f Big.slot1 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permIdentity f Big.slot2 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permIdentity f Big.slot3 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permIdentity f Big.slot4 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permIdentity f Big.slot5 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate f Big.slot0 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate f Big.slot1 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate f Big.slot2 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate f Big.slot3 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate f Big.slot4 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate f Big.slot5 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate2 f Big.slot0 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate2 f Big.slot1 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate2 f Big.slot2 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate2 f Big.slot3 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate2 f Big.slot4 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permRotate2 f Big.slot5 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot0 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot1 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot2 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot3 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot4 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot5 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot0 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot1 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot2 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot3 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot4 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot5 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot0 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot1 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot2 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot3 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot4 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot5 = Ring.solve-∀ f Big.slot0 f Big.slot1 f Big.slot2 f Big.slot3 f Big.slot4 f Big.slot5

-- The three rational S3-equivariant block isomorphisms above
-- combine only through the actual native G-set seven-orbit chart.
-- This source isolates coefficients and block operations so the
-- global 27-dimensional rational field isomorphism can import them
-- WITHOUT creating a parallel owner or re-proving finite S3 tables.
