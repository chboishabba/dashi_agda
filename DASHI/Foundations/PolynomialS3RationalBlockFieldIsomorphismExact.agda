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
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
import DASHI.Foundations.PolynomialS3SmallRationalBlockCertificateExact as Small
import DASHI.Foundations.PolynomialS3RegularRationalBlockCertificateExact as Big

asRational : Int → ℚ
asRational z = z / 1


Field2 : Set
Field2 = Small.Pair → ℚ

-- Reflection uses quantified genuine rational variables.
scalarField2 : ℚ → ℚ → Field2
scalarField2 x0 x1 Small.pair0 = x0
scalarField2 x0 x1 Small.pair1 = x1

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

-- Scalar identities, instantiated with original field coordinates.
fromToCoordinates2ScalarBasePair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (toCoordinates2 (scalarField2 x0 x1)) Small.pair0 ≡
  (scalarField2 x0 x1) Small.pair0
fromToCoordinates2ScalarBasePair0 = Ring.solve-∀

fromToCoordinates2ScalarBasePair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (toCoordinates2 (scalarField2 x0 x1)) Small.pair1 ≡
  (scalarField2 x0 x1) Small.pair1
fromToCoordinates2ScalarBasePair1 = Ring.solve-∀

fromToCoordinates2 :
  (f : Field2) (i : Small.Pair) →
  fromCoordinates2 (toCoordinates2 f) i ≡ f i
fromToCoordinates2 f Small.pair0 = fromToCoordinates2ScalarBasePair0 (f Small.pair0) (f Small.pair1)
fromToCoordinates2 f Small.pair1 = fromToCoordinates2ScalarBasePair1 (f Small.pair0) (f Small.pair1)

-- Scalar identities, instantiated with original field coordinates.
toFromCoordinates2ScalarBasePair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0 ≡
  (scalarField2 x0 x1) Small.pair0
toFromCoordinates2ScalarBasePair0 = Ring.solve-∀

toFromCoordinates2ScalarBasePair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1 ≡
  (scalarField2 x0 x1) Small.pair1
toFromCoordinates2ScalarBasePair1 = Ring.solve-∀

toFromCoordinates2 :
  (f : Field2) (i : Small.Pair) →
  toCoordinates2 (fromCoordinates2 f) i ≡ f i
toFromCoordinates2 f Small.pair0 = toFromCoordinates2ScalarBasePair0 (f Small.pair0) (f Small.pair1)
toFromCoordinates2 f Small.pair1 = toFromCoordinates2ScalarBasePair1 (f Small.pair0) (f Small.pair1)

sourceAction2 :
  Perm.TriPermutation → Field2 → Field2
sourceAction2 p f i = f (Small.flipPair p i)

coordinateAction2 :
  Perm.TriPermutation → Field2 → Field2
coordinateAction2 p f i =
  dotRational2 (Small.twoBlockAction p) f i

-- Scalar identities, instantiated with original field coordinates.
toCoordinates2IntertwinesScalarPermIdentityPair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permIdentity (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permIdentity (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2IntertwinesScalarPermIdentityPair0 = Ring.solve-∀

toCoordinates2IntertwinesScalarPermIdentityPair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permIdentity (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permIdentity (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2IntertwinesScalarPermIdentityPair1 = Ring.solve-∀

toCoordinates2IntertwinesScalarPermRotatePair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permRotate (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permRotate (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2IntertwinesScalarPermRotatePair0 = Ring.solve-∀

toCoordinates2IntertwinesScalarPermRotatePair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permRotate (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permRotate (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2IntertwinesScalarPermRotatePair1 = Ring.solve-∀

toCoordinates2IntertwinesScalarPermRotate2Pair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permRotate2 (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permRotate2 (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2IntertwinesScalarPermRotate2Pair0 = Ring.solve-∀

toCoordinates2IntertwinesScalarPermRotate2Pair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permRotate2 (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permRotate2 (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2IntertwinesScalarPermRotate2Pair1 = Ring.solve-∀

toCoordinates2IntertwinesScalarPermSwapLowMidPair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapLowMid (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permSwapLowMid (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2IntertwinesScalarPermSwapLowMidPair0 = Ring.solve-∀

toCoordinates2IntertwinesScalarPermSwapLowMidPair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapLowMid (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permSwapLowMid (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2IntertwinesScalarPermSwapLowMidPair1 = Ring.solve-∀

toCoordinates2IntertwinesScalarPermSwapLowHighPair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapLowHigh (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permSwapLowHigh (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2IntertwinesScalarPermSwapLowHighPair0 = Ring.solve-∀

toCoordinates2IntertwinesScalarPermSwapLowHighPair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapLowHigh (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permSwapLowHigh (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2IntertwinesScalarPermSwapLowHighPair1 = Ring.solve-∀

toCoordinates2IntertwinesScalarPermSwapMidHighPair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapMidHigh (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permSwapMidHigh (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2IntertwinesScalarPermSwapMidHighPair0 = Ring.solve-∀

toCoordinates2IntertwinesScalarPermSwapMidHighPair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapMidHigh (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permSwapMidHigh (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2IntertwinesScalarPermSwapMidHighPair1 = Ring.solve-∀

toCoordinates2Intertwines :
  (p : Perm.TriPermutation) (f : Field2) (i : Small.Pair) →
  toCoordinates2 (sourceAction2 p f) i ≡
  coordinateAction2 p (toCoordinates2 f) i
toCoordinates2Intertwines Perm.permIdentity f Small.pair0 = toCoordinates2IntertwinesScalarPermIdentityPair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permIdentity f Small.pair1 = toCoordinates2IntertwinesScalarPermIdentityPair1 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permRotate f Small.pair0 = toCoordinates2IntertwinesScalarPermRotatePair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permRotate f Small.pair1 = toCoordinates2IntertwinesScalarPermRotatePair1 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permRotate2 f Small.pair0 = toCoordinates2IntertwinesScalarPermRotate2Pair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permRotate2 f Small.pair1 = toCoordinates2IntertwinesScalarPermRotate2Pair1 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapLowMid f Small.pair0 = toCoordinates2IntertwinesScalarPermSwapLowMidPair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapLowMid f Small.pair1 = toCoordinates2IntertwinesScalarPermSwapLowMidPair1 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapLowHigh f Small.pair0 = toCoordinates2IntertwinesScalarPermSwapLowHighPair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapLowHigh f Small.pair1 = toCoordinates2IntertwinesScalarPermSwapLowHighPair1 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapMidHigh f Small.pair0 = toCoordinates2IntertwinesScalarPermSwapMidHighPair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapMidHigh f Small.pair1 = toCoordinates2IntertwinesScalarPermSwapMidHighPair1 (f Small.pair0) (f Small.pair1)

Field3 : Set
Field3 = Small.Three → ℚ

-- Reflection uses quantified genuine rational variables.
scalarField3 : ℚ → ℚ → ℚ → Field3
scalarField3 x0 x1 x2 Small.axis0 = x0
scalarField3 x0 x1 x2 Small.axis1 = x1
scalarField3 x0 x1 x2 Small.axis2 = x2

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

-- Scalar identities, instantiated with original field coordinates.
fromToCoordinates3ScalarBaseAxis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0 ≡
  (scalarField3 x0 x1 x2) Small.axis0
fromToCoordinates3ScalarBaseAxis0 = Ring.solve-∀

fromToCoordinates3ScalarBaseAxis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1 ≡
  (scalarField3 x0 x1 x2) Small.axis1
fromToCoordinates3ScalarBaseAxis1 = Ring.solve-∀

fromToCoordinates3ScalarBaseAxis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2 ≡
  (scalarField3 x0 x1 x2) Small.axis2
fromToCoordinates3ScalarBaseAxis2 = Ring.solve-∀

fromToCoordinates3 :
  (f : Field3) (i : Small.Three) →
  fromCoordinates3 (toCoordinates3 f) i ≡ f i
fromToCoordinates3 f Small.axis0 = fromToCoordinates3ScalarBaseAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromToCoordinates3 f Small.axis1 = fromToCoordinates3ScalarBaseAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromToCoordinates3 f Small.axis2 = fromToCoordinates3ScalarBaseAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)

-- Scalar identities, instantiated with original field coordinates.
toFromCoordinates3ScalarBaseAxis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0 ≡
  (scalarField3 x0 x1 x2) Small.axis0
toFromCoordinates3ScalarBaseAxis0 = Ring.solve-∀

toFromCoordinates3ScalarBaseAxis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1 ≡
  (scalarField3 x0 x1 x2) Small.axis1
toFromCoordinates3ScalarBaseAxis1 = Ring.solve-∀

toFromCoordinates3ScalarBaseAxis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2 ≡
  (scalarField3 x0 x1 x2) Small.axis2
toFromCoordinates3ScalarBaseAxis2 = Ring.solve-∀

toFromCoordinates3 :
  (f : Field3) (i : Small.Three) →
  toCoordinates3 (fromCoordinates3 f) i ≡ f i
toFromCoordinates3 f Small.axis0 = toFromCoordinates3ScalarBaseAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toFromCoordinates3 f Small.axis1 = toFromCoordinates3ScalarBaseAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toFromCoordinates3 f Small.axis2 = toFromCoordinates3ScalarBaseAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)

sourceAction3 :
  Perm.TriPermutation → Field3 → Field3
sourceAction3 p f i = f (Small.leftInversePoint p i)

coordinateAction3 :
  Perm.TriPermutation → Field3 → Field3
coordinateAction3 p f i =
  dotRational3 (Small.threeBlockAction p) f i

-- Scalar identities, instantiated with original field coordinates.
toCoordinates3IntertwinesScalarPermIdentityAxis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permIdentity (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3IntertwinesScalarPermIdentityAxis0 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermIdentityAxis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permIdentity (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3IntertwinesScalarPermIdentityAxis1 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermIdentityAxis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permIdentity (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3IntertwinesScalarPermIdentityAxis2 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermRotateAxis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permRotate (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3IntertwinesScalarPermRotateAxis0 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermRotateAxis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permRotate (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3IntertwinesScalarPermRotateAxis1 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermRotateAxis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permRotate (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3IntertwinesScalarPermRotateAxis2 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermRotate2Axis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permRotate2 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3IntertwinesScalarPermRotate2Axis0 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermRotate2Axis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permRotate2 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3IntertwinesScalarPermRotate2Axis1 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermRotate2Axis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permRotate2 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3IntertwinesScalarPermRotate2Axis2 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermSwapLowMidAxis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permSwapLowMid (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3IntertwinesScalarPermSwapLowMidAxis0 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermSwapLowMidAxis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permSwapLowMid (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3IntertwinesScalarPermSwapLowMidAxis1 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermSwapLowMidAxis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permSwapLowMid (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3IntertwinesScalarPermSwapLowMidAxis2 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermSwapLowHighAxis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permSwapLowHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3IntertwinesScalarPermSwapLowHighAxis0 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermSwapLowHighAxis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permSwapLowHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3IntertwinesScalarPermSwapLowHighAxis1 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermSwapLowHighAxis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permSwapLowHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3IntertwinesScalarPermSwapLowHighAxis2 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermSwapMidHighAxis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permSwapMidHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3IntertwinesScalarPermSwapMidHighAxis0 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermSwapMidHighAxis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permSwapMidHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3IntertwinesScalarPermSwapMidHighAxis1 = Ring.solve-∀

toCoordinates3IntertwinesScalarPermSwapMidHighAxis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permSwapMidHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3IntertwinesScalarPermSwapMidHighAxis2 = Ring.solve-∀

toCoordinates3Intertwines :
  (p : Perm.TriPermutation) (f : Field3) (i : Small.Three) →
  toCoordinates3 (sourceAction3 p f) i ≡
  coordinateAction3 p (toCoordinates3 f) i
toCoordinates3Intertwines Perm.permIdentity f Small.axis0 = toCoordinates3IntertwinesScalarPermIdentityAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permIdentity f Small.axis1 = toCoordinates3IntertwinesScalarPermIdentityAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permIdentity f Small.axis2 = toCoordinates3IntertwinesScalarPermIdentityAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate f Small.axis0 = toCoordinates3IntertwinesScalarPermRotateAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate f Small.axis1 = toCoordinates3IntertwinesScalarPermRotateAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate f Small.axis2 = toCoordinates3IntertwinesScalarPermRotateAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate2 f Small.axis0 = toCoordinates3IntertwinesScalarPermRotate2Axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate2 f Small.axis1 = toCoordinates3IntertwinesScalarPermRotate2Axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate2 f Small.axis2 = toCoordinates3IntertwinesScalarPermRotate2Axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowMid f Small.axis0 = toCoordinates3IntertwinesScalarPermSwapLowMidAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowMid f Small.axis1 = toCoordinates3IntertwinesScalarPermSwapLowMidAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowMid f Small.axis2 = toCoordinates3IntertwinesScalarPermSwapLowMidAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis0 = toCoordinates3IntertwinesScalarPermSwapLowHighAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis1 = toCoordinates3IntertwinesScalarPermSwapLowHighAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis2 = toCoordinates3IntertwinesScalarPermSwapLowHighAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis0 = toCoordinates3IntertwinesScalarPermSwapMidHighAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis1 = toCoordinates3IntertwinesScalarPermSwapMidHighAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis2 = toCoordinates3IntertwinesScalarPermSwapMidHighAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)

Field6 : Set
Field6 = Big.Six → ℚ

-- Reflection uses quantified genuine rational variables.
scalarField6 : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → Field6
scalarField6 x0 x1 x2 x3 x4 x5 Big.slot0 = x0
scalarField6 x0 x1 x2 x3 x4 x5 Big.slot1 = x1
scalarField6 x0 x1 x2 x3 x4 x5 Big.slot2 = x2
scalarField6 x0 x1 x2 x3 x4 x5 Big.slot3 = x3
scalarField6 x0 x1 x2 x3 x4 x5 Big.slot4 = x4
scalarField6 x0 x1 x2 x3 x4 x5 Big.slot5 = x5

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

-- Scalar identities, instantiated with original field coordinates.
fromToCoordinates6ScalarBaseSlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot0
fromToCoordinates6ScalarBaseSlot0 = Ring.solve-∀

fromToCoordinates6ScalarBaseSlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot1
fromToCoordinates6ScalarBaseSlot1 = Ring.solve-∀

fromToCoordinates6ScalarBaseSlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot2
fromToCoordinates6ScalarBaseSlot2 = Ring.solve-∀

fromToCoordinates6ScalarBaseSlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot3
fromToCoordinates6ScalarBaseSlot3 = Ring.solve-∀

fromToCoordinates6ScalarBaseSlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot4
fromToCoordinates6ScalarBaseSlot4 = Ring.solve-∀

fromToCoordinates6ScalarBaseSlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot5
fromToCoordinates6ScalarBaseSlot5 = Ring.solve-∀

fromToCoordinates6 :
  (f : Field6) (i : Big.Six) →
  fromCoordinates6 (toCoordinates6 f) i ≡ f i
fromToCoordinates6 f Big.slot0 = fromToCoordinates6ScalarBaseSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromToCoordinates6 f Big.slot1 = fromToCoordinates6ScalarBaseSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromToCoordinates6 f Big.slot2 = fromToCoordinates6ScalarBaseSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromToCoordinates6 f Big.slot3 = fromToCoordinates6ScalarBaseSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromToCoordinates6 f Big.slot4 = fromToCoordinates6ScalarBaseSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromToCoordinates6 f Big.slot5 = fromToCoordinates6ScalarBaseSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)

-- Scalar identities, instantiated with original field coordinates.
toFromCoordinates6ScalarBaseSlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot0
toFromCoordinates6ScalarBaseSlot0 = Ring.solve-∀

toFromCoordinates6ScalarBaseSlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot1
toFromCoordinates6ScalarBaseSlot1 = Ring.solve-∀

toFromCoordinates6ScalarBaseSlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot2
toFromCoordinates6ScalarBaseSlot2 = Ring.solve-∀

toFromCoordinates6ScalarBaseSlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot3
toFromCoordinates6ScalarBaseSlot3 = Ring.solve-∀

toFromCoordinates6ScalarBaseSlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot4
toFromCoordinates6ScalarBaseSlot4 = Ring.solve-∀

toFromCoordinates6ScalarBaseSlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot5
toFromCoordinates6ScalarBaseSlot5 = Ring.solve-∀

toFromCoordinates6 :
  (f : Field6) (i : Big.Six) →
  toCoordinates6 (fromCoordinates6 f) i ≡ f i
toFromCoordinates6 f Big.slot0 = toFromCoordinates6ScalarBaseSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toFromCoordinates6 f Big.slot1 = toFromCoordinates6ScalarBaseSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toFromCoordinates6 f Big.slot2 = toFromCoordinates6ScalarBaseSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toFromCoordinates6 f Big.slot3 = toFromCoordinates6ScalarBaseSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toFromCoordinates6 f Big.slot4 = toFromCoordinates6ScalarBaseSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toFromCoordinates6 f Big.slot5 = toFromCoordinates6ScalarBaseSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)

sourceAction6 :
  Perm.TriPermutation → Field6 → Field6
sourceAction6 p f i = f (Big.leftInverseRow p i)

coordinateAction6 :
  Perm.TriPermutation → Field6 → Field6
coordinateAction6 p f i =
  dotRational6 (Big.blockAction p) f i

-- Scalar identities, instantiated with original field coordinates.
toCoordinates6IntertwinesScalarPermIdentitySlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6IntertwinesScalarPermIdentitySlot0 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermIdentitySlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6IntertwinesScalarPermIdentitySlot1 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermIdentitySlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6IntertwinesScalarPermIdentitySlot2 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermIdentitySlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6IntertwinesScalarPermIdentitySlot3 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermIdentitySlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6IntertwinesScalarPermIdentitySlot4 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermIdentitySlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6IntertwinesScalarPermIdentitySlot5 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotateSlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6IntertwinesScalarPermRotateSlot0 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotateSlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6IntertwinesScalarPermRotateSlot1 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotateSlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6IntertwinesScalarPermRotateSlot2 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotateSlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6IntertwinesScalarPermRotateSlot3 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotateSlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6IntertwinesScalarPermRotateSlot4 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotateSlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6IntertwinesScalarPermRotateSlot5 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotate2Slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6IntertwinesScalarPermRotate2Slot0 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotate2Slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6IntertwinesScalarPermRotate2Slot1 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotate2Slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6IntertwinesScalarPermRotate2Slot2 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotate2Slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6IntertwinesScalarPermRotate2Slot3 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotate2Slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6IntertwinesScalarPermRotate2Slot4 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermRotate2Slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6IntertwinesScalarPermRotate2Slot5 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowMidSlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6IntertwinesScalarPermSwapLowMidSlot0 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowMidSlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6IntertwinesScalarPermSwapLowMidSlot1 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowMidSlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6IntertwinesScalarPermSwapLowMidSlot2 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowMidSlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6IntertwinesScalarPermSwapLowMidSlot3 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowMidSlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6IntertwinesScalarPermSwapLowMidSlot4 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowMidSlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6IntertwinesScalarPermSwapLowMidSlot5 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowHighSlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6IntertwinesScalarPermSwapLowHighSlot0 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowHighSlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6IntertwinesScalarPermSwapLowHighSlot1 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowHighSlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6IntertwinesScalarPermSwapLowHighSlot2 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowHighSlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6IntertwinesScalarPermSwapLowHighSlot3 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowHighSlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6IntertwinesScalarPermSwapLowHighSlot4 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapLowHighSlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6IntertwinesScalarPermSwapLowHighSlot5 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapMidHighSlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6IntertwinesScalarPermSwapMidHighSlot0 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapMidHighSlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6IntertwinesScalarPermSwapMidHighSlot1 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapMidHighSlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6IntertwinesScalarPermSwapMidHighSlot2 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapMidHighSlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6IntertwinesScalarPermSwapMidHighSlot3 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapMidHighSlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6IntertwinesScalarPermSwapMidHighSlot4 = Ring.solve-∀

toCoordinates6IntertwinesScalarPermSwapMidHighSlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6IntertwinesScalarPermSwapMidHighSlot5 = Ring.solve-∀

toCoordinates6Intertwines :
  (p : Perm.TriPermutation) (f : Field6) (i : Big.Six) →
  toCoordinates6 (sourceAction6 p f) i ≡
  coordinateAction6 p (toCoordinates6 f) i
toCoordinates6Intertwines Perm.permIdentity f Big.slot0 = toCoordinates6IntertwinesScalarPermIdentitySlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permIdentity f Big.slot1 = toCoordinates6IntertwinesScalarPermIdentitySlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permIdentity f Big.slot2 = toCoordinates6IntertwinesScalarPermIdentitySlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permIdentity f Big.slot3 = toCoordinates6IntertwinesScalarPermIdentitySlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permIdentity f Big.slot4 = toCoordinates6IntertwinesScalarPermIdentitySlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permIdentity f Big.slot5 = toCoordinates6IntertwinesScalarPermIdentitySlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot0 = toCoordinates6IntertwinesScalarPermRotateSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot1 = toCoordinates6IntertwinesScalarPermRotateSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot2 = toCoordinates6IntertwinesScalarPermRotateSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot3 = toCoordinates6IntertwinesScalarPermRotateSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot4 = toCoordinates6IntertwinesScalarPermRotateSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot5 = toCoordinates6IntertwinesScalarPermRotateSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot0 = toCoordinates6IntertwinesScalarPermRotate2Slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot1 = toCoordinates6IntertwinesScalarPermRotate2Slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot2 = toCoordinates6IntertwinesScalarPermRotate2Slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot3 = toCoordinates6IntertwinesScalarPermRotate2Slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot4 = toCoordinates6IntertwinesScalarPermRotate2Slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot5 = toCoordinates6IntertwinesScalarPermRotate2Slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot0 = toCoordinates6IntertwinesScalarPermSwapLowMidSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot1 = toCoordinates6IntertwinesScalarPermSwapLowMidSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot2 = toCoordinates6IntertwinesScalarPermSwapLowMidSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot3 = toCoordinates6IntertwinesScalarPermSwapLowMidSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot4 = toCoordinates6IntertwinesScalarPermSwapLowMidSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot5 = toCoordinates6IntertwinesScalarPermSwapLowMidSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot0 = toCoordinates6IntertwinesScalarPermSwapLowHighSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot1 = toCoordinates6IntertwinesScalarPermSwapLowHighSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot2 = toCoordinates6IntertwinesScalarPermSwapLowHighSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot3 = toCoordinates6IntertwinesScalarPermSwapLowHighSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot4 = toCoordinates6IntertwinesScalarPermSwapLowHighSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot5 = toCoordinates6IntertwinesScalarPermSwapLowHighSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot0 = toCoordinates6IntertwinesScalarPermSwapMidHighSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot1 = toCoordinates6IntertwinesScalarPermSwapMidHighSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot2 = toCoordinates6IntertwinesScalarPermSwapMidHighSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot3 = toCoordinates6IntertwinesScalarPermSwapMidHighSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot4 = toCoordinates6IntertwinesScalarPermSwapMidHighSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot5 = toCoordinates6IntertwinesScalarPermSwapMidHighSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)

-- The three rational S3-equivariant block isomorphisms above
-- combine only through the actual native G-set seven-orbit chart.
-- This source isolates coefficients and block operations so the
-- global 27-dimensional rational field isomorphism can import them
-- WITHOUT creating a parallel owner or re-proving finite S3 tables.

------------------------------------------------------------------------
-- Rational linearity and inverse-direction S3 equivariance.
-- Reuse the same Ring.solve variable-list machinery already owning polynomial
-- Vieta invariants; this is no new algebraic axiom.
------------------------------------------------------------------------

plusField2 : Field2 → Field2 → Field2
plusField2 f g i = f i + g i

-- Scalar identities, instantiated with original field coordinates.
toCoordinates2AdditiveScalarBasePair0 :
  (x0 x1 y0 y1 : ℚ) →
  toCoordinates2 (plusField2 (scalarField2 x0 x1) (scalarField2 y0 y1)) Small.pair0 ≡
  plusField2 (toCoordinates2 (scalarField2 x0 x1)) (toCoordinates2 (scalarField2 y0 y1)) Small.pair0
toCoordinates2AdditiveScalarBasePair0 = Ring.solve-∀

toCoordinates2AdditiveScalarBasePair1 :
  (x0 x1 y0 y1 : ℚ) →
  toCoordinates2 (plusField2 (scalarField2 x0 x1) (scalarField2 y0 y1)) Small.pair1 ≡
  plusField2 (toCoordinates2 (scalarField2 x0 x1)) (toCoordinates2 (scalarField2 y0 y1)) Small.pair1
toCoordinates2AdditiveScalarBasePair1 = Ring.solve-∀

toCoordinates2Additive :
  (f g : Field2) (i : Small.Pair) →
  toCoordinates2 (plusField2 f g) i ≡
  plusField2 (toCoordinates2 f) (toCoordinates2 g) i
toCoordinates2Additive f g Small.pair0 = toCoordinates2AdditiveScalarBasePair0 (f Small.pair0) (f Small.pair1) (g Small.pair0) (g Small.pair1)
toCoordinates2Additive f g Small.pair1 = toCoordinates2AdditiveScalarBasePair1 (f Small.pair0) (f Small.pair1) (g Small.pair0) (g Small.pair1)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates2AdditiveScalarBasePair0 :
  (x0 x1 y0 y1 : ℚ) →
  fromCoordinates2 (plusField2 (scalarField2 x0 x1) (scalarField2 y0 y1)) Small.pair0 ≡
  plusField2 (fromCoordinates2 (scalarField2 x0 x1)) (fromCoordinates2 (scalarField2 y0 y1)) Small.pair0
fromCoordinates2AdditiveScalarBasePair0 = Ring.solve-∀

fromCoordinates2AdditiveScalarBasePair1 :
  (x0 x1 y0 y1 : ℚ) →
  fromCoordinates2 (plusField2 (scalarField2 x0 x1) (scalarField2 y0 y1)) Small.pair1 ≡
  plusField2 (fromCoordinates2 (scalarField2 x0 x1)) (fromCoordinates2 (scalarField2 y0 y1)) Small.pair1
fromCoordinates2AdditiveScalarBasePair1 = Ring.solve-∀

fromCoordinates2Additive :
  (f g : Field2) (i : Small.Pair) →
  fromCoordinates2 (plusField2 f g) i ≡
  plusField2 (fromCoordinates2 f) (fromCoordinates2 g) i
fromCoordinates2Additive f g Small.pair0 = fromCoordinates2AdditiveScalarBasePair0 (f Small.pair0) (f Small.pair1) (g Small.pair0) (g Small.pair1)
fromCoordinates2Additive f g Small.pair1 = fromCoordinates2AdditiveScalarBasePair1 (f Small.pair0) (f Small.pair1) (g Small.pair0) (g Small.pair1)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates2IntertwinesScalarPermIdentityPair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permIdentity (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permIdentity (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2IntertwinesScalarPermIdentityPair0 = Ring.solve-∀

fromCoordinates2IntertwinesScalarPermIdentityPair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permIdentity (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permIdentity (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2IntertwinesScalarPermIdentityPair1 = Ring.solve-∀

fromCoordinates2IntertwinesScalarPermRotatePair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permRotate (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permRotate (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2IntertwinesScalarPermRotatePair0 = Ring.solve-∀

fromCoordinates2IntertwinesScalarPermRotatePair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permRotate (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permRotate (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2IntertwinesScalarPermRotatePair1 = Ring.solve-∀

fromCoordinates2IntertwinesScalarPermRotate2Pair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permRotate2 (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permRotate2 (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2IntertwinesScalarPermRotate2Pair0 = Ring.solve-∀

fromCoordinates2IntertwinesScalarPermRotate2Pair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permRotate2 (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permRotate2 (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2IntertwinesScalarPermRotate2Pair1 = Ring.solve-∀

fromCoordinates2IntertwinesScalarPermSwapLowMidPair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapLowMid (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permSwapLowMid (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2IntertwinesScalarPermSwapLowMidPair0 = Ring.solve-∀

fromCoordinates2IntertwinesScalarPermSwapLowMidPair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapLowMid (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permSwapLowMid (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2IntertwinesScalarPermSwapLowMidPair1 = Ring.solve-∀

fromCoordinates2IntertwinesScalarPermSwapLowHighPair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapLowHigh (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permSwapLowHigh (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2IntertwinesScalarPermSwapLowHighPair0 = Ring.solve-∀

fromCoordinates2IntertwinesScalarPermSwapLowHighPair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapLowHigh (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permSwapLowHigh (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2IntertwinesScalarPermSwapLowHighPair1 = Ring.solve-∀

fromCoordinates2IntertwinesScalarPermSwapMidHighPair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapMidHigh (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permSwapMidHigh (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2IntertwinesScalarPermSwapMidHighPair0 = Ring.solve-∀

fromCoordinates2IntertwinesScalarPermSwapMidHighPair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapMidHigh (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permSwapMidHigh (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2IntertwinesScalarPermSwapMidHighPair1 = Ring.solve-∀

fromCoordinates2Intertwines :
  (p : Perm.TriPermutation) (f : Field2) (i : Small.Pair) →
  fromCoordinates2 (coordinateAction2 p f) i ≡
  sourceAction2 p (fromCoordinates2 f) i
fromCoordinates2Intertwines Perm.permIdentity f Small.pair0 = fromCoordinates2IntertwinesScalarPermIdentityPair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permIdentity f Small.pair1 = fromCoordinates2IntertwinesScalarPermIdentityPair1 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permRotate f Small.pair0 = fromCoordinates2IntertwinesScalarPermRotatePair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permRotate f Small.pair1 = fromCoordinates2IntertwinesScalarPermRotatePair1 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permRotate2 f Small.pair0 = fromCoordinates2IntertwinesScalarPermRotate2Pair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permRotate2 f Small.pair1 = fromCoordinates2IntertwinesScalarPermRotate2Pair1 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapLowMid f Small.pair0 = fromCoordinates2IntertwinesScalarPermSwapLowMidPair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapLowMid f Small.pair1 = fromCoordinates2IntertwinesScalarPermSwapLowMidPair1 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapLowHigh f Small.pair0 = fromCoordinates2IntertwinesScalarPermSwapLowHighPair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapLowHigh f Small.pair1 = fromCoordinates2IntertwinesScalarPermSwapLowHighPair1 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapMidHigh f Small.pair0 = fromCoordinates2IntertwinesScalarPermSwapMidHighPair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapMidHigh f Small.pair1 = fromCoordinates2IntertwinesScalarPermSwapMidHighPair1 (f Small.pair0) (f Small.pair1)

plusField3 : Field3 → Field3 → Field3
plusField3 f g i = f i + g i

-- Scalar identities, instantiated with original field coordinates.
toCoordinates3AdditiveScalarBaseAxis0 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  toCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis0 ≡
  plusField3 (toCoordinates3 (scalarField3 x0 x1 x2)) (toCoordinates3 (scalarField3 y0 y1 y2)) Small.axis0
toCoordinates3AdditiveScalarBaseAxis0 = Ring.solve-∀

toCoordinates3AdditiveScalarBaseAxis1 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  toCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis1 ≡
  plusField3 (toCoordinates3 (scalarField3 x0 x1 x2)) (toCoordinates3 (scalarField3 y0 y1 y2)) Small.axis1
toCoordinates3AdditiveScalarBaseAxis1 = Ring.solve-∀

toCoordinates3AdditiveScalarBaseAxis2 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  toCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis2 ≡
  plusField3 (toCoordinates3 (scalarField3 x0 x1 x2)) (toCoordinates3 (scalarField3 y0 y1 y2)) Small.axis2
toCoordinates3AdditiveScalarBaseAxis2 = Ring.solve-∀

toCoordinates3Additive :
  (f g : Field3) (i : Small.Three) →
  toCoordinates3 (plusField3 f g) i ≡
  plusField3 (toCoordinates3 f) (toCoordinates3 g) i
toCoordinates3Additive f g Small.axis0 = toCoordinates3AdditiveScalarBaseAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)
toCoordinates3Additive f g Small.axis1 = toCoordinates3AdditiveScalarBaseAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)
toCoordinates3Additive f g Small.axis2 = toCoordinates3AdditiveScalarBaseAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates3AdditiveScalarBaseAxis0 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  fromCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis0 ≡
  plusField3 (fromCoordinates3 (scalarField3 x0 x1 x2)) (fromCoordinates3 (scalarField3 y0 y1 y2)) Small.axis0
fromCoordinates3AdditiveScalarBaseAxis0 = Ring.solve-∀

fromCoordinates3AdditiveScalarBaseAxis1 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  fromCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis1 ≡
  plusField3 (fromCoordinates3 (scalarField3 x0 x1 x2)) (fromCoordinates3 (scalarField3 y0 y1 y2)) Small.axis1
fromCoordinates3AdditiveScalarBaseAxis1 = Ring.solve-∀

fromCoordinates3AdditiveScalarBaseAxis2 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  fromCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis2 ≡
  plusField3 (fromCoordinates3 (scalarField3 x0 x1 x2)) (fromCoordinates3 (scalarField3 y0 y1 y2)) Small.axis2
fromCoordinates3AdditiveScalarBaseAxis2 = Ring.solve-∀

fromCoordinates3Additive :
  (f g : Field3) (i : Small.Three) →
  fromCoordinates3 (plusField3 f g) i ≡
  plusField3 (fromCoordinates3 f) (fromCoordinates3 g) i
fromCoordinates3Additive f g Small.axis0 = fromCoordinates3AdditiveScalarBaseAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)
fromCoordinates3Additive f g Small.axis1 = fromCoordinates3AdditiveScalarBaseAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)
fromCoordinates3Additive f g Small.axis2 = fromCoordinates3AdditiveScalarBaseAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates3IntertwinesScalarPermIdentityAxis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permIdentity (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3IntertwinesScalarPermIdentityAxis0 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermIdentityAxis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permIdentity (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3IntertwinesScalarPermIdentityAxis1 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermIdentityAxis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permIdentity (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3IntertwinesScalarPermIdentityAxis2 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermRotateAxis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permRotate (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3IntertwinesScalarPermRotateAxis0 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermRotateAxis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permRotate (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3IntertwinesScalarPermRotateAxis1 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermRotateAxis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permRotate (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3IntertwinesScalarPermRotateAxis2 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermRotate2Axis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permRotate2 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3IntertwinesScalarPermRotate2Axis0 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermRotate2Axis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permRotate2 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3IntertwinesScalarPermRotate2Axis1 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermRotate2Axis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permRotate2 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3IntertwinesScalarPermRotate2Axis2 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermSwapLowMidAxis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permSwapLowMid (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3IntertwinesScalarPermSwapLowMidAxis0 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermSwapLowMidAxis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permSwapLowMid (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3IntertwinesScalarPermSwapLowMidAxis1 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermSwapLowMidAxis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permSwapLowMid (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3IntertwinesScalarPermSwapLowMidAxis2 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermSwapLowHighAxis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permSwapLowHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3IntertwinesScalarPermSwapLowHighAxis0 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermSwapLowHighAxis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permSwapLowHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3IntertwinesScalarPermSwapLowHighAxis1 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermSwapLowHighAxis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permSwapLowHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3IntertwinesScalarPermSwapLowHighAxis2 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermSwapMidHighAxis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permSwapMidHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3IntertwinesScalarPermSwapMidHighAxis0 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermSwapMidHighAxis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permSwapMidHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3IntertwinesScalarPermSwapMidHighAxis1 = Ring.solve-∀

fromCoordinates3IntertwinesScalarPermSwapMidHighAxis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permSwapMidHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3IntertwinesScalarPermSwapMidHighAxis2 = Ring.solve-∀

fromCoordinates3Intertwines :
  (p : Perm.TriPermutation) (f : Field3) (i : Small.Three) →
  fromCoordinates3 (coordinateAction3 p f) i ≡
  sourceAction3 p (fromCoordinates3 f) i
fromCoordinates3Intertwines Perm.permIdentity f Small.axis0 = fromCoordinates3IntertwinesScalarPermIdentityAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permIdentity f Small.axis1 = fromCoordinates3IntertwinesScalarPermIdentityAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permIdentity f Small.axis2 = fromCoordinates3IntertwinesScalarPermIdentityAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate f Small.axis0 = fromCoordinates3IntertwinesScalarPermRotateAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate f Small.axis1 = fromCoordinates3IntertwinesScalarPermRotateAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate f Small.axis2 = fromCoordinates3IntertwinesScalarPermRotateAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate2 f Small.axis0 = fromCoordinates3IntertwinesScalarPermRotate2Axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate2 f Small.axis1 = fromCoordinates3IntertwinesScalarPermRotate2Axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate2 f Small.axis2 = fromCoordinates3IntertwinesScalarPermRotate2Axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowMid f Small.axis0 = fromCoordinates3IntertwinesScalarPermSwapLowMidAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowMid f Small.axis1 = fromCoordinates3IntertwinesScalarPermSwapLowMidAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowMid f Small.axis2 = fromCoordinates3IntertwinesScalarPermSwapLowMidAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis0 = fromCoordinates3IntertwinesScalarPermSwapLowHighAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis1 = fromCoordinates3IntertwinesScalarPermSwapLowHighAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis2 = fromCoordinates3IntertwinesScalarPermSwapLowHighAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis0 = fromCoordinates3IntertwinesScalarPermSwapMidHighAxis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis1 = fromCoordinates3IntertwinesScalarPermSwapMidHighAxis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis2 = fromCoordinates3IntertwinesScalarPermSwapMidHighAxis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)

plusField6 : Field6 → Field6 → Field6
plusField6 f g i = f i + g i

-- Scalar identities, instantiated with original field coordinates.
toCoordinates6AdditiveScalarBaseSlot0 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot0 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot0
toCoordinates6AdditiveScalarBaseSlot0 = Ring.solve-∀

toCoordinates6AdditiveScalarBaseSlot1 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot1 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot1
toCoordinates6AdditiveScalarBaseSlot1 = Ring.solve-∀

toCoordinates6AdditiveScalarBaseSlot2 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot2 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot2
toCoordinates6AdditiveScalarBaseSlot2 = Ring.solve-∀

toCoordinates6AdditiveScalarBaseSlot3 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot3 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot3
toCoordinates6AdditiveScalarBaseSlot3 = Ring.solve-∀

toCoordinates6AdditiveScalarBaseSlot4 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot4 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot4
toCoordinates6AdditiveScalarBaseSlot4 = Ring.solve-∀

toCoordinates6AdditiveScalarBaseSlot5 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot5 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot5
toCoordinates6AdditiveScalarBaseSlot5 = Ring.solve-∀

toCoordinates6Additive :
  (f g : Field6) (i : Big.Six) →
  toCoordinates6 (plusField6 f g) i ≡
  plusField6 (toCoordinates6 f) (toCoordinates6 g) i
toCoordinates6Additive f g Big.slot0 = toCoordinates6AdditiveScalarBaseSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
toCoordinates6Additive f g Big.slot1 = toCoordinates6AdditiveScalarBaseSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
toCoordinates6Additive f g Big.slot2 = toCoordinates6AdditiveScalarBaseSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
toCoordinates6Additive f g Big.slot3 = toCoordinates6AdditiveScalarBaseSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
toCoordinates6Additive f g Big.slot4 = toCoordinates6AdditiveScalarBaseSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
toCoordinates6Additive f g Big.slot5 = toCoordinates6AdditiveScalarBaseSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates6AdditiveScalarBaseSlot0 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot0 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot0
fromCoordinates6AdditiveScalarBaseSlot0 = Ring.solve-∀

fromCoordinates6AdditiveScalarBaseSlot1 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot1 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot1
fromCoordinates6AdditiveScalarBaseSlot1 = Ring.solve-∀

fromCoordinates6AdditiveScalarBaseSlot2 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot2 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot2
fromCoordinates6AdditiveScalarBaseSlot2 = Ring.solve-∀

fromCoordinates6AdditiveScalarBaseSlot3 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot3 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot3
fromCoordinates6AdditiveScalarBaseSlot3 = Ring.solve-∀

fromCoordinates6AdditiveScalarBaseSlot4 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot4 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot4
fromCoordinates6AdditiveScalarBaseSlot4 = Ring.solve-∀

fromCoordinates6AdditiveScalarBaseSlot5 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot5 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot5
fromCoordinates6AdditiveScalarBaseSlot5 = Ring.solve-∀

fromCoordinates6Additive :
  (f g : Field6) (i : Big.Six) →
  fromCoordinates6 (plusField6 f g) i ≡
  plusField6 (fromCoordinates6 f) (fromCoordinates6 g) i
fromCoordinates6Additive f g Big.slot0 = fromCoordinates6AdditiveScalarBaseSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
fromCoordinates6Additive f g Big.slot1 = fromCoordinates6AdditiveScalarBaseSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
fromCoordinates6Additive f g Big.slot2 = fromCoordinates6AdditiveScalarBaseSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
fromCoordinates6Additive f g Big.slot3 = fromCoordinates6AdditiveScalarBaseSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
fromCoordinates6Additive f g Big.slot4 = fromCoordinates6AdditiveScalarBaseSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
fromCoordinates6Additive f g Big.slot5 = fromCoordinates6AdditiveScalarBaseSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates6IntertwinesScalarPermIdentitySlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6IntertwinesScalarPermIdentitySlot0 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermIdentitySlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6IntertwinesScalarPermIdentitySlot1 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermIdentitySlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6IntertwinesScalarPermIdentitySlot2 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermIdentitySlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6IntertwinesScalarPermIdentitySlot3 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermIdentitySlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6IntertwinesScalarPermIdentitySlot4 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermIdentitySlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6IntertwinesScalarPermIdentitySlot5 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotateSlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6IntertwinesScalarPermRotateSlot0 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotateSlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6IntertwinesScalarPermRotateSlot1 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotateSlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6IntertwinesScalarPermRotateSlot2 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotateSlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6IntertwinesScalarPermRotateSlot3 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotateSlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6IntertwinesScalarPermRotateSlot4 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotateSlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6IntertwinesScalarPermRotateSlot5 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotate2Slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6IntertwinesScalarPermRotate2Slot0 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotate2Slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6IntertwinesScalarPermRotate2Slot1 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotate2Slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6IntertwinesScalarPermRotate2Slot2 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotate2Slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6IntertwinesScalarPermRotate2Slot3 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotate2Slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6IntertwinesScalarPermRotate2Slot4 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermRotate2Slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6IntertwinesScalarPermRotate2Slot5 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowMidSlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6IntertwinesScalarPermSwapLowMidSlot0 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowMidSlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6IntertwinesScalarPermSwapLowMidSlot1 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowMidSlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6IntertwinesScalarPermSwapLowMidSlot2 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowMidSlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6IntertwinesScalarPermSwapLowMidSlot3 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowMidSlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6IntertwinesScalarPermSwapLowMidSlot4 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowMidSlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6IntertwinesScalarPermSwapLowMidSlot5 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowHighSlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6IntertwinesScalarPermSwapLowHighSlot0 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowHighSlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6IntertwinesScalarPermSwapLowHighSlot1 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowHighSlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6IntertwinesScalarPermSwapLowHighSlot2 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowHighSlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6IntertwinesScalarPermSwapLowHighSlot3 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowHighSlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6IntertwinesScalarPermSwapLowHighSlot4 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapLowHighSlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6IntertwinesScalarPermSwapLowHighSlot5 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapMidHighSlot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6IntertwinesScalarPermSwapMidHighSlot0 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapMidHighSlot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6IntertwinesScalarPermSwapMidHighSlot1 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapMidHighSlot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6IntertwinesScalarPermSwapMidHighSlot2 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapMidHighSlot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6IntertwinesScalarPermSwapMidHighSlot3 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapMidHighSlot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6IntertwinesScalarPermSwapMidHighSlot4 = Ring.solve-∀

fromCoordinates6IntertwinesScalarPermSwapMidHighSlot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6IntertwinesScalarPermSwapMidHighSlot5 = Ring.solve-∀

fromCoordinates6Intertwines :
  (p : Perm.TriPermutation) (f : Field6) (i : Big.Six) →
  fromCoordinates6 (coordinateAction6 p f) i ≡
  sourceAction6 p (fromCoordinates6 f) i
fromCoordinates6Intertwines Perm.permIdentity f Big.slot0 = fromCoordinates6IntertwinesScalarPermIdentitySlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permIdentity f Big.slot1 = fromCoordinates6IntertwinesScalarPermIdentitySlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permIdentity f Big.slot2 = fromCoordinates6IntertwinesScalarPermIdentitySlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permIdentity f Big.slot3 = fromCoordinates6IntertwinesScalarPermIdentitySlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permIdentity f Big.slot4 = fromCoordinates6IntertwinesScalarPermIdentitySlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permIdentity f Big.slot5 = fromCoordinates6IntertwinesScalarPermIdentitySlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot0 = fromCoordinates6IntertwinesScalarPermRotateSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot1 = fromCoordinates6IntertwinesScalarPermRotateSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot2 = fromCoordinates6IntertwinesScalarPermRotateSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot3 = fromCoordinates6IntertwinesScalarPermRotateSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot4 = fromCoordinates6IntertwinesScalarPermRotateSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot5 = fromCoordinates6IntertwinesScalarPermRotateSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot0 = fromCoordinates6IntertwinesScalarPermRotate2Slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot1 = fromCoordinates6IntertwinesScalarPermRotate2Slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot2 = fromCoordinates6IntertwinesScalarPermRotate2Slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot3 = fromCoordinates6IntertwinesScalarPermRotate2Slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot4 = fromCoordinates6IntertwinesScalarPermRotate2Slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot5 = fromCoordinates6IntertwinesScalarPermRotate2Slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot0 = fromCoordinates6IntertwinesScalarPermSwapLowMidSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot1 = fromCoordinates6IntertwinesScalarPermSwapLowMidSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot2 = fromCoordinates6IntertwinesScalarPermSwapLowMidSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot3 = fromCoordinates6IntertwinesScalarPermSwapLowMidSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot4 = fromCoordinates6IntertwinesScalarPermSwapLowMidSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot5 = fromCoordinates6IntertwinesScalarPermSwapLowMidSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot0 = fromCoordinates6IntertwinesScalarPermSwapLowHighSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot1 = fromCoordinates6IntertwinesScalarPermSwapLowHighSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot2 = fromCoordinates6IntertwinesScalarPermSwapLowHighSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot3 = fromCoordinates6IntertwinesScalarPermSwapLowHighSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot4 = fromCoordinates6IntertwinesScalarPermSwapLowHighSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot5 = fromCoordinates6IntertwinesScalarPermSwapLowHighSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot0 = fromCoordinates6IntertwinesScalarPermSwapMidHighSlot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot1 = fromCoordinates6IntertwinesScalarPermSwapMidHighSlot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot2 = fromCoordinates6IntertwinesScalarPermSwapMidHighSlot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot3 = fromCoordinates6IntertwinesScalarPermSwapMidHighSlot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot4 = fromCoordinates6IntertwinesScalarPermSwapMidHighSlot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot5 = fromCoordinates6IntertwinesScalarPermSwapMidHighSlot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
