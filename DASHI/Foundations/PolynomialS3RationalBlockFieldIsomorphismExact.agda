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
fromToCoordinates2_scalar_base_pair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (toCoordinates2 (scalarField2 x0 x1)) Small.pair0 ≡
  (scalarField2 x0 x1) Small.pair0
fromToCoordinates2_scalar_base_pair0 = Ring.solve-∀

fromToCoordinates2_scalar_base_pair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (toCoordinates2 (scalarField2 x0 x1)) Small.pair1 ≡
  (scalarField2 x0 x1) Small.pair1
fromToCoordinates2_scalar_base_pair1 = Ring.solve-∀

fromToCoordinates2 :
  (f : Field2) (i : Small.Pair) →
  fromCoordinates2 (toCoordinates2 f) i ≡ f i
fromToCoordinates2 f Small.pair0 = fromToCoordinates2_scalar_base_pair0 (f Small.pair0) (f Small.pair1)
fromToCoordinates2 f Small.pair1 = fromToCoordinates2_scalar_base_pair1 (f Small.pair0) (f Small.pair1)

-- Scalar identities, instantiated with original field coordinates.
toFromCoordinates2_scalar_base_pair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0 ≡
  (scalarField2 x0 x1) Small.pair0
toFromCoordinates2_scalar_base_pair0 = Ring.solve-∀

toFromCoordinates2_scalar_base_pair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1 ≡
  (scalarField2 x0 x1) Small.pair1
toFromCoordinates2_scalar_base_pair1 = Ring.solve-∀

toFromCoordinates2 :
  (f : Field2) (i : Small.Pair) →
  toCoordinates2 (fromCoordinates2 f) i ≡ f i
toFromCoordinates2 f Small.pair0 = toFromCoordinates2_scalar_base_pair0 (f Small.pair0) (f Small.pair1)
toFromCoordinates2 f Small.pair1 = toFromCoordinates2_scalar_base_pair1 (f Small.pair0) (f Small.pair1)

sourceAction2 :
  Perm.TriPermutation → Field2 → Field2
sourceAction2 p f i = f (Small.flipPair p i)

coordinateAction2 :
  Perm.TriPermutation → Field2 → Field2
coordinateAction2 p f i =
  dotRational2 (Small.twoBlockAction p) f i

-- Scalar identities, instantiated with original field coordinates.
toCoordinates2Intertwines_scalar_permIdentity_pair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permIdentity (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permIdentity (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2Intertwines_scalar_permIdentity_pair0 = Ring.solve-∀

toCoordinates2Intertwines_scalar_permIdentity_pair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permIdentity (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permIdentity (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2Intertwines_scalar_permIdentity_pair1 = Ring.solve-∀

toCoordinates2Intertwines_scalar_permRotate_pair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permRotate (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permRotate (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2Intertwines_scalar_permRotate_pair0 = Ring.solve-∀

toCoordinates2Intertwines_scalar_permRotate_pair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permRotate (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permRotate (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2Intertwines_scalar_permRotate_pair1 = Ring.solve-∀

toCoordinates2Intertwines_scalar_permRotate2_pair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permRotate2 (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permRotate2 (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2Intertwines_scalar_permRotate2_pair0 = Ring.solve-∀

toCoordinates2Intertwines_scalar_permRotate2_pair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permRotate2 (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permRotate2 (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2Intertwines_scalar_permRotate2_pair1 = Ring.solve-∀

toCoordinates2Intertwines_scalar_permSwapLowMid_pair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapLowMid (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permSwapLowMid (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2Intertwines_scalar_permSwapLowMid_pair0 = Ring.solve-∀

toCoordinates2Intertwines_scalar_permSwapLowMid_pair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapLowMid (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permSwapLowMid (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2Intertwines_scalar_permSwapLowMid_pair1 = Ring.solve-∀

toCoordinates2Intertwines_scalar_permSwapLowHigh_pair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapLowHigh (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permSwapLowHigh (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2Intertwines_scalar_permSwapLowHigh_pair0 = Ring.solve-∀

toCoordinates2Intertwines_scalar_permSwapLowHigh_pair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapLowHigh (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permSwapLowHigh (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2Intertwines_scalar_permSwapLowHigh_pair1 = Ring.solve-∀

toCoordinates2Intertwines_scalar_permSwapMidHigh_pair0 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapMidHigh (scalarField2 x0 x1)) Small.pair0 ≡
  coordinateAction2 Perm.permSwapMidHigh (toCoordinates2 (scalarField2 x0 x1)) Small.pair0
toCoordinates2Intertwines_scalar_permSwapMidHigh_pair0 = Ring.solve-∀

toCoordinates2Intertwines_scalar_permSwapMidHigh_pair1 :
  (x0 x1 : ℚ) →
  toCoordinates2 (sourceAction2 Perm.permSwapMidHigh (scalarField2 x0 x1)) Small.pair1 ≡
  coordinateAction2 Perm.permSwapMidHigh (toCoordinates2 (scalarField2 x0 x1)) Small.pair1
toCoordinates2Intertwines_scalar_permSwapMidHigh_pair1 = Ring.solve-∀

toCoordinates2Intertwines :
  (p : Perm.TriPermutation) (f : Field2) (i : Small.Pair) →
  toCoordinates2 (sourceAction2 p f) i ≡
  coordinateAction2 p (toCoordinates2 f) i
toCoordinates2Intertwines Perm.permIdentity f Small.pair0 = toCoordinates2Intertwines_scalar_permIdentity_pair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permIdentity f Small.pair1 = toCoordinates2Intertwines_scalar_permIdentity_pair1 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permRotate f Small.pair0 = toCoordinates2Intertwines_scalar_permRotate_pair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permRotate f Small.pair1 = toCoordinates2Intertwines_scalar_permRotate_pair1 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permRotate2 f Small.pair0 = toCoordinates2Intertwines_scalar_permRotate2_pair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permRotate2 f Small.pair1 = toCoordinates2Intertwines_scalar_permRotate2_pair1 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapLowMid f Small.pair0 = toCoordinates2Intertwines_scalar_permSwapLowMid_pair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapLowMid f Small.pair1 = toCoordinates2Intertwines_scalar_permSwapLowMid_pair1 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapLowHigh f Small.pair0 = toCoordinates2Intertwines_scalar_permSwapLowHigh_pair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapLowHigh f Small.pair1 = toCoordinates2Intertwines_scalar_permSwapLowHigh_pair1 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapMidHigh f Small.pair0 = toCoordinates2Intertwines_scalar_permSwapMidHigh_pair0 (f Small.pair0) (f Small.pair1)
toCoordinates2Intertwines Perm.permSwapMidHigh f Small.pair1 = toCoordinates2Intertwines_scalar_permSwapMidHigh_pair1 (f Small.pair0) (f Small.pair1)

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
fromToCoordinates3_scalar_base_axis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0 ≡
  (scalarField3 x0 x1 x2) Small.axis0
fromToCoordinates3_scalar_base_axis0 = Ring.solve-∀

fromToCoordinates3_scalar_base_axis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1 ≡
  (scalarField3 x0 x1 x2) Small.axis1
fromToCoordinates3_scalar_base_axis1 = Ring.solve-∀

fromToCoordinates3_scalar_base_axis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2 ≡
  (scalarField3 x0 x1 x2) Small.axis2
fromToCoordinates3_scalar_base_axis2 = Ring.solve-∀

fromToCoordinates3 :
  (f : Field3) (i : Small.Three) →
  fromCoordinates3 (toCoordinates3 f) i ≡ f i
fromToCoordinates3 f Small.axis0 = fromToCoordinates3_scalar_base_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromToCoordinates3 f Small.axis1 = fromToCoordinates3_scalar_base_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromToCoordinates3 f Small.axis2 = fromToCoordinates3_scalar_base_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)

-- Scalar identities, instantiated with original field coordinates.
toFromCoordinates3_scalar_base_axis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0 ≡
  (scalarField3 x0 x1 x2) Small.axis0
toFromCoordinates3_scalar_base_axis0 = Ring.solve-∀

toFromCoordinates3_scalar_base_axis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1 ≡
  (scalarField3 x0 x1 x2) Small.axis1
toFromCoordinates3_scalar_base_axis1 = Ring.solve-∀

toFromCoordinates3_scalar_base_axis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2 ≡
  (scalarField3 x0 x1 x2) Small.axis2
toFromCoordinates3_scalar_base_axis2 = Ring.solve-∀

toFromCoordinates3 :
  (f : Field3) (i : Small.Three) →
  toCoordinates3 (fromCoordinates3 f) i ≡ f i
toFromCoordinates3 f Small.axis0 = toFromCoordinates3_scalar_base_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toFromCoordinates3 f Small.axis1 = toFromCoordinates3_scalar_base_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toFromCoordinates3 f Small.axis2 = toFromCoordinates3_scalar_base_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)

sourceAction3 :
  Perm.TriPermutation → Field3 → Field3
sourceAction3 p f i = f (Small.leftInversePoint p i)

coordinateAction3 :
  Perm.TriPermutation → Field3 → Field3
coordinateAction3 p f i =
  dotRational3 (Small.threeBlockAction p) f i

-- Scalar identities, instantiated with original field coordinates.
toCoordinates3Intertwines_scalar_permIdentity_axis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permIdentity (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3Intertwines_scalar_permIdentity_axis0 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permIdentity_axis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permIdentity (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3Intertwines_scalar_permIdentity_axis1 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permIdentity_axis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permIdentity (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3Intertwines_scalar_permIdentity_axis2 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permRotate_axis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permRotate (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3Intertwines_scalar_permRotate_axis0 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permRotate_axis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permRotate (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3Intertwines_scalar_permRotate_axis1 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permRotate_axis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permRotate (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3Intertwines_scalar_permRotate_axis2 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permRotate2_axis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permRotate2 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3Intertwines_scalar_permRotate2_axis0 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permRotate2_axis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permRotate2 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3Intertwines_scalar_permRotate2_axis1 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permRotate2_axis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permRotate2 (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3Intertwines_scalar_permRotate2_axis2 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permSwapLowMid_axis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permSwapLowMid (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3Intertwines_scalar_permSwapLowMid_axis0 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permSwapLowMid_axis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permSwapLowMid (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3Intertwines_scalar_permSwapLowMid_axis1 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permSwapLowMid_axis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permSwapLowMid (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3Intertwines_scalar_permSwapLowMid_axis2 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permSwapLowHigh_axis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permSwapLowHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3Intertwines_scalar_permSwapLowHigh_axis0 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permSwapLowHigh_axis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permSwapLowHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3Intertwines_scalar_permSwapLowHigh_axis1 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permSwapLowHigh_axis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permSwapLowHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3Intertwines_scalar_permSwapLowHigh_axis2 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permSwapMidHigh_axis0 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis0 ≡
  coordinateAction3 Perm.permSwapMidHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
toCoordinates3Intertwines_scalar_permSwapMidHigh_axis0 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permSwapMidHigh_axis1 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis1 ≡
  coordinateAction3 Perm.permSwapMidHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
toCoordinates3Intertwines_scalar_permSwapMidHigh_axis1 = Ring.solve-∀

toCoordinates3Intertwines_scalar_permSwapMidHigh_axis2 :
  (x0 x1 x2 : ℚ) →
  toCoordinates3 (sourceAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis2 ≡
  coordinateAction3 Perm.permSwapMidHigh (toCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
toCoordinates3Intertwines_scalar_permSwapMidHigh_axis2 = Ring.solve-∀

toCoordinates3Intertwines :
  (p : Perm.TriPermutation) (f : Field3) (i : Small.Three) →
  toCoordinates3 (sourceAction3 p f) i ≡
  coordinateAction3 p (toCoordinates3 f) i
toCoordinates3Intertwines Perm.permIdentity f Small.axis0 = toCoordinates3Intertwines_scalar_permIdentity_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permIdentity f Small.axis1 = toCoordinates3Intertwines_scalar_permIdentity_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permIdentity f Small.axis2 = toCoordinates3Intertwines_scalar_permIdentity_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate f Small.axis0 = toCoordinates3Intertwines_scalar_permRotate_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate f Small.axis1 = toCoordinates3Intertwines_scalar_permRotate_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate f Small.axis2 = toCoordinates3Intertwines_scalar_permRotate_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate2 f Small.axis0 = toCoordinates3Intertwines_scalar_permRotate2_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate2 f Small.axis1 = toCoordinates3Intertwines_scalar_permRotate2_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permRotate2 f Small.axis2 = toCoordinates3Intertwines_scalar_permRotate2_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowMid f Small.axis0 = toCoordinates3Intertwines_scalar_permSwapLowMid_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowMid f Small.axis1 = toCoordinates3Intertwines_scalar_permSwapLowMid_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowMid f Small.axis2 = toCoordinates3Intertwines_scalar_permSwapLowMid_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis0 = toCoordinates3Intertwines_scalar_permSwapLowHigh_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis1 = toCoordinates3Intertwines_scalar_permSwapLowHigh_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis2 = toCoordinates3Intertwines_scalar_permSwapLowHigh_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis0 = toCoordinates3Intertwines_scalar_permSwapMidHigh_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis1 = toCoordinates3Intertwines_scalar_permSwapMidHigh_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
toCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis2 = toCoordinates3Intertwines_scalar_permSwapMidHigh_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)

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
fromToCoordinates6_scalar_base_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot0
fromToCoordinates6_scalar_base_slot0 = Ring.solve-∀

fromToCoordinates6_scalar_base_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot1
fromToCoordinates6_scalar_base_slot1 = Ring.solve-∀

fromToCoordinates6_scalar_base_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot2
fromToCoordinates6_scalar_base_slot2 = Ring.solve-∀

fromToCoordinates6_scalar_base_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot3
fromToCoordinates6_scalar_base_slot3 = Ring.solve-∀

fromToCoordinates6_scalar_base_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot4
fromToCoordinates6_scalar_base_slot4 = Ring.solve-∀

fromToCoordinates6_scalar_base_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot5
fromToCoordinates6_scalar_base_slot5 = Ring.solve-∀

fromToCoordinates6 :
  (f : Field6) (i : Big.Six) →
  fromCoordinates6 (toCoordinates6 f) i ≡ f i
fromToCoordinates6 f Big.slot0 = fromToCoordinates6_scalar_base_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromToCoordinates6 f Big.slot1 = fromToCoordinates6_scalar_base_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromToCoordinates6 f Big.slot2 = fromToCoordinates6_scalar_base_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromToCoordinates6 f Big.slot3 = fromToCoordinates6_scalar_base_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromToCoordinates6 f Big.slot4 = fromToCoordinates6_scalar_base_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromToCoordinates6 f Big.slot5 = fromToCoordinates6_scalar_base_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)

-- Scalar identities, instantiated with original field coordinates.
toFromCoordinates6_scalar_base_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot0
toFromCoordinates6_scalar_base_slot0 = Ring.solve-∀

toFromCoordinates6_scalar_base_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot1
toFromCoordinates6_scalar_base_slot1 = Ring.solve-∀

toFromCoordinates6_scalar_base_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot2
toFromCoordinates6_scalar_base_slot2 = Ring.solve-∀

toFromCoordinates6_scalar_base_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot3
toFromCoordinates6_scalar_base_slot3 = Ring.solve-∀

toFromCoordinates6_scalar_base_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot4
toFromCoordinates6_scalar_base_slot4 = Ring.solve-∀

toFromCoordinates6_scalar_base_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  (scalarField6 x0 x1 x2 x3 x4 x5) Big.slot5
toFromCoordinates6_scalar_base_slot5 = Ring.solve-∀

toFromCoordinates6 :
  (f : Field6) (i : Big.Six) →
  toCoordinates6 (fromCoordinates6 f) i ≡ f i
toFromCoordinates6 f Big.slot0 = toFromCoordinates6_scalar_base_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toFromCoordinates6 f Big.slot1 = toFromCoordinates6_scalar_base_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toFromCoordinates6 f Big.slot2 = toFromCoordinates6_scalar_base_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toFromCoordinates6 f Big.slot3 = toFromCoordinates6_scalar_base_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toFromCoordinates6 f Big.slot4 = toFromCoordinates6_scalar_base_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toFromCoordinates6 f Big.slot5 = toFromCoordinates6_scalar_base_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)

sourceAction6 :
  Perm.TriPermutation → Field6 → Field6
sourceAction6 p f i = f (Big.leftInverseRow p i)

coordinateAction6 :
  Perm.TriPermutation → Field6 → Field6
coordinateAction6 p f i =
  dotRational6 (Big.blockAction p) f i

-- Scalar identities, instantiated with original field coordinates.
toCoordinates6Intertwines_scalar_permIdentity_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6Intertwines_scalar_permIdentity_slot0 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permIdentity_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6Intertwines_scalar_permIdentity_slot1 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permIdentity_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6Intertwines_scalar_permIdentity_slot2 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permIdentity_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6Intertwines_scalar_permIdentity_slot3 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permIdentity_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6Intertwines_scalar_permIdentity_slot4 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permIdentity_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permIdentity (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6Intertwines_scalar_permIdentity_slot5 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6Intertwines_scalar_permRotate_slot0 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6Intertwines_scalar_permRotate_slot1 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6Intertwines_scalar_permRotate_slot2 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6Intertwines_scalar_permRotate_slot3 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6Intertwines_scalar_permRotate_slot4 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permRotate (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6Intertwines_scalar_permRotate_slot5 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate2_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6Intertwines_scalar_permRotate2_slot0 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate2_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6Intertwines_scalar_permRotate2_slot1 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate2_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6Intertwines_scalar_permRotate2_slot2 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate2_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6Intertwines_scalar_permRotate2_slot3 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate2_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6Intertwines_scalar_permRotate2_slot4 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permRotate2_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permRotate2 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6Intertwines_scalar_permRotate2_slot5 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowMid_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6Intertwines_scalar_permSwapLowMid_slot0 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowMid_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6Intertwines_scalar_permSwapLowMid_slot1 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowMid_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6Intertwines_scalar_permSwapLowMid_slot2 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowMid_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6Intertwines_scalar_permSwapLowMid_slot3 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowMid_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6Intertwines_scalar_permSwapLowMid_slot4 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowMid_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permSwapLowMid (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6Intertwines_scalar_permSwapLowMid_slot5 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowHigh_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6Intertwines_scalar_permSwapLowHigh_slot0 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowHigh_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6Intertwines_scalar_permSwapLowHigh_slot1 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowHigh_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6Intertwines_scalar_permSwapLowHigh_slot2 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowHigh_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6Intertwines_scalar_permSwapLowHigh_slot3 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowHigh_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6Intertwines_scalar_permSwapLowHigh_slot4 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapLowHigh_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permSwapLowHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6Intertwines_scalar_permSwapLowHigh_slot5 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapMidHigh_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
toCoordinates6Intertwines_scalar_permSwapMidHigh_slot0 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapMidHigh_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
toCoordinates6Intertwines_scalar_permSwapMidHigh_slot1 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapMidHigh_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
toCoordinates6Intertwines_scalar_permSwapMidHigh_slot2 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapMidHigh_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
toCoordinates6Intertwines_scalar_permSwapMidHigh_slot3 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapMidHigh_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
toCoordinates6Intertwines_scalar_permSwapMidHigh_slot4 = Ring.solve-∀

toCoordinates6Intertwines_scalar_permSwapMidHigh_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  toCoordinates6 (sourceAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  coordinateAction6 Perm.permSwapMidHigh (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
toCoordinates6Intertwines_scalar_permSwapMidHigh_slot5 = Ring.solve-∀

toCoordinates6Intertwines :
  (p : Perm.TriPermutation) (f : Field6) (i : Big.Six) →
  toCoordinates6 (sourceAction6 p f) i ≡
  coordinateAction6 p (toCoordinates6 f) i
toCoordinates6Intertwines Perm.permIdentity f Big.slot0 = toCoordinates6Intertwines_scalar_permIdentity_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permIdentity f Big.slot1 = toCoordinates6Intertwines_scalar_permIdentity_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permIdentity f Big.slot2 = toCoordinates6Intertwines_scalar_permIdentity_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permIdentity f Big.slot3 = toCoordinates6Intertwines_scalar_permIdentity_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permIdentity f Big.slot4 = toCoordinates6Intertwines_scalar_permIdentity_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permIdentity f Big.slot5 = toCoordinates6Intertwines_scalar_permIdentity_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot0 = toCoordinates6Intertwines_scalar_permRotate_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot1 = toCoordinates6Intertwines_scalar_permRotate_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot2 = toCoordinates6Intertwines_scalar_permRotate_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot3 = toCoordinates6Intertwines_scalar_permRotate_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot4 = toCoordinates6Intertwines_scalar_permRotate_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate f Big.slot5 = toCoordinates6Intertwines_scalar_permRotate_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot0 = toCoordinates6Intertwines_scalar_permRotate2_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot1 = toCoordinates6Intertwines_scalar_permRotate2_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot2 = toCoordinates6Intertwines_scalar_permRotate2_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot3 = toCoordinates6Intertwines_scalar_permRotate2_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot4 = toCoordinates6Intertwines_scalar_permRotate2_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permRotate2 f Big.slot5 = toCoordinates6Intertwines_scalar_permRotate2_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot0 = toCoordinates6Intertwines_scalar_permSwapLowMid_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot1 = toCoordinates6Intertwines_scalar_permSwapLowMid_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot2 = toCoordinates6Intertwines_scalar_permSwapLowMid_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot3 = toCoordinates6Intertwines_scalar_permSwapLowMid_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot4 = toCoordinates6Intertwines_scalar_permSwapLowMid_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowMid f Big.slot5 = toCoordinates6Intertwines_scalar_permSwapLowMid_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot0 = toCoordinates6Intertwines_scalar_permSwapLowHigh_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot1 = toCoordinates6Intertwines_scalar_permSwapLowHigh_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot2 = toCoordinates6Intertwines_scalar_permSwapLowHigh_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot3 = toCoordinates6Intertwines_scalar_permSwapLowHigh_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot4 = toCoordinates6Intertwines_scalar_permSwapLowHigh_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot5 = toCoordinates6Intertwines_scalar_permSwapLowHigh_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot0 = toCoordinates6Intertwines_scalar_permSwapMidHigh_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot1 = toCoordinates6Intertwines_scalar_permSwapMidHigh_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot2 = toCoordinates6Intertwines_scalar_permSwapMidHigh_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot3 = toCoordinates6Intertwines_scalar_permSwapMidHigh_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot4 = toCoordinates6Intertwines_scalar_permSwapMidHigh_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
toCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot5 = toCoordinates6Intertwines_scalar_permSwapMidHigh_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)

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
toCoordinates2Additive_scalar_base_pair0 :
  (x0 x1 y0 y1 : ℚ) →
  toCoordinates2 (plusField2 (scalarField2 x0 x1) (scalarField2 y0 y1)) Small.pair0 ≡
  plusField2 (toCoordinates2 (scalarField2 x0 x1)) (toCoordinates2 (scalarField2 y0 y1)) Small.pair0
toCoordinates2Additive_scalar_base_pair0 = Ring.solve-∀

toCoordinates2Additive_scalar_base_pair1 :
  (x0 x1 y0 y1 : ℚ) →
  toCoordinates2 (plusField2 (scalarField2 x0 x1) (scalarField2 y0 y1)) Small.pair1 ≡
  plusField2 (toCoordinates2 (scalarField2 x0 x1)) (toCoordinates2 (scalarField2 y0 y1)) Small.pair1
toCoordinates2Additive_scalar_base_pair1 = Ring.solve-∀

toCoordinates2Additive :
  (f g : Field2) (i : Small.Pair) →
  toCoordinates2 (plusField2 f g) i ≡
  plusField2 (toCoordinates2 f) (toCoordinates2 g) i
toCoordinates2Additive f g Small.pair0 = toCoordinates2Additive_scalar_base_pair0 (f Small.pair0) (f Small.pair1) (g Small.pair0) (g Small.pair1)
toCoordinates2Additive f g Small.pair1 = toCoordinates2Additive_scalar_base_pair1 (f Small.pair0) (f Small.pair1) (g Small.pair0) (g Small.pair1)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates2Additive_scalar_base_pair0 :
  (x0 x1 y0 y1 : ℚ) →
  fromCoordinates2 (plusField2 (scalarField2 x0 x1) (scalarField2 y0 y1)) Small.pair0 ≡
  plusField2 (fromCoordinates2 (scalarField2 x0 x1)) (fromCoordinates2 (scalarField2 y0 y1)) Small.pair0
fromCoordinates2Additive_scalar_base_pair0 = Ring.solve-∀

fromCoordinates2Additive_scalar_base_pair1 :
  (x0 x1 y0 y1 : ℚ) →
  fromCoordinates2 (plusField2 (scalarField2 x0 x1) (scalarField2 y0 y1)) Small.pair1 ≡
  plusField2 (fromCoordinates2 (scalarField2 x0 x1)) (fromCoordinates2 (scalarField2 y0 y1)) Small.pair1
fromCoordinates2Additive_scalar_base_pair1 = Ring.solve-∀

fromCoordinates2Additive :
  (f g : Field2) (i : Small.Pair) →
  fromCoordinates2 (plusField2 f g) i ≡
  plusField2 (fromCoordinates2 f) (fromCoordinates2 g) i
fromCoordinates2Additive f g Small.pair0 = fromCoordinates2Additive_scalar_base_pair0 (f Small.pair0) (f Small.pair1) (g Small.pair0) (g Small.pair1)
fromCoordinates2Additive f g Small.pair1 = fromCoordinates2Additive_scalar_base_pair1 (f Small.pair0) (f Small.pair1) (g Small.pair0) (g Small.pair1)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates2Intertwines_scalar_permIdentity_pair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permIdentity (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permIdentity (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2Intertwines_scalar_permIdentity_pair0 = Ring.solve-∀

fromCoordinates2Intertwines_scalar_permIdentity_pair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permIdentity (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permIdentity (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2Intertwines_scalar_permIdentity_pair1 = Ring.solve-∀

fromCoordinates2Intertwines_scalar_permRotate_pair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permRotate (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permRotate (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2Intertwines_scalar_permRotate_pair0 = Ring.solve-∀

fromCoordinates2Intertwines_scalar_permRotate_pair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permRotate (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permRotate (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2Intertwines_scalar_permRotate_pair1 = Ring.solve-∀

fromCoordinates2Intertwines_scalar_permRotate2_pair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permRotate2 (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permRotate2 (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2Intertwines_scalar_permRotate2_pair0 = Ring.solve-∀

fromCoordinates2Intertwines_scalar_permRotate2_pair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permRotate2 (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permRotate2 (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2Intertwines_scalar_permRotate2_pair1 = Ring.solve-∀

fromCoordinates2Intertwines_scalar_permSwapLowMid_pair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapLowMid (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permSwapLowMid (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2Intertwines_scalar_permSwapLowMid_pair0 = Ring.solve-∀

fromCoordinates2Intertwines_scalar_permSwapLowMid_pair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapLowMid (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permSwapLowMid (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2Intertwines_scalar_permSwapLowMid_pair1 = Ring.solve-∀

fromCoordinates2Intertwines_scalar_permSwapLowHigh_pair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapLowHigh (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permSwapLowHigh (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2Intertwines_scalar_permSwapLowHigh_pair0 = Ring.solve-∀

fromCoordinates2Intertwines_scalar_permSwapLowHigh_pair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapLowHigh (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permSwapLowHigh (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2Intertwines_scalar_permSwapLowHigh_pair1 = Ring.solve-∀

fromCoordinates2Intertwines_scalar_permSwapMidHigh_pair0 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapMidHigh (scalarField2 x0 x1)) Small.pair0 ≡
  sourceAction2 Perm.permSwapMidHigh (fromCoordinates2 (scalarField2 x0 x1)) Small.pair0
fromCoordinates2Intertwines_scalar_permSwapMidHigh_pair0 = Ring.solve-∀

fromCoordinates2Intertwines_scalar_permSwapMidHigh_pair1 :
  (x0 x1 : ℚ) →
  fromCoordinates2 (coordinateAction2 Perm.permSwapMidHigh (scalarField2 x0 x1)) Small.pair1 ≡
  sourceAction2 Perm.permSwapMidHigh (fromCoordinates2 (scalarField2 x0 x1)) Small.pair1
fromCoordinates2Intertwines_scalar_permSwapMidHigh_pair1 = Ring.solve-∀

fromCoordinates2Intertwines :
  (p : Perm.TriPermutation) (f : Field2) (i : Small.Pair) →
  fromCoordinates2 (coordinateAction2 p f) i ≡
  sourceAction2 p (fromCoordinates2 f) i
fromCoordinates2Intertwines Perm.permIdentity f Small.pair0 = fromCoordinates2Intertwines_scalar_permIdentity_pair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permIdentity f Small.pair1 = fromCoordinates2Intertwines_scalar_permIdentity_pair1 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permRotate f Small.pair0 = fromCoordinates2Intertwines_scalar_permRotate_pair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permRotate f Small.pair1 = fromCoordinates2Intertwines_scalar_permRotate_pair1 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permRotate2 f Small.pair0 = fromCoordinates2Intertwines_scalar_permRotate2_pair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permRotate2 f Small.pair1 = fromCoordinates2Intertwines_scalar_permRotate2_pair1 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapLowMid f Small.pair0 = fromCoordinates2Intertwines_scalar_permSwapLowMid_pair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapLowMid f Small.pair1 = fromCoordinates2Intertwines_scalar_permSwapLowMid_pair1 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapLowHigh f Small.pair0 = fromCoordinates2Intertwines_scalar_permSwapLowHigh_pair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapLowHigh f Small.pair1 = fromCoordinates2Intertwines_scalar_permSwapLowHigh_pair1 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapMidHigh f Small.pair0 = fromCoordinates2Intertwines_scalar_permSwapMidHigh_pair0 (f Small.pair0) (f Small.pair1)
fromCoordinates2Intertwines Perm.permSwapMidHigh f Small.pair1 = fromCoordinates2Intertwines_scalar_permSwapMidHigh_pair1 (f Small.pair0) (f Small.pair1)

plusField3 : Field3 → Field3 → Field3
plusField3 f g i = f i + g i

-- Scalar identities, instantiated with original field coordinates.
toCoordinates3Additive_scalar_base_axis0 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  toCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis0 ≡
  plusField3 (toCoordinates3 (scalarField3 x0 x1 x2)) (toCoordinates3 (scalarField3 y0 y1 y2)) Small.axis0
toCoordinates3Additive_scalar_base_axis0 = Ring.solve-∀

toCoordinates3Additive_scalar_base_axis1 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  toCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis1 ≡
  plusField3 (toCoordinates3 (scalarField3 x0 x1 x2)) (toCoordinates3 (scalarField3 y0 y1 y2)) Small.axis1
toCoordinates3Additive_scalar_base_axis1 = Ring.solve-∀

toCoordinates3Additive_scalar_base_axis2 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  toCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis2 ≡
  plusField3 (toCoordinates3 (scalarField3 x0 x1 x2)) (toCoordinates3 (scalarField3 y0 y1 y2)) Small.axis2
toCoordinates3Additive_scalar_base_axis2 = Ring.solve-∀

toCoordinates3Additive :
  (f g : Field3) (i : Small.Three) →
  toCoordinates3 (plusField3 f g) i ≡
  plusField3 (toCoordinates3 f) (toCoordinates3 g) i
toCoordinates3Additive f g Small.axis0 = toCoordinates3Additive_scalar_base_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)
toCoordinates3Additive f g Small.axis1 = toCoordinates3Additive_scalar_base_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)
toCoordinates3Additive f g Small.axis2 = toCoordinates3Additive_scalar_base_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates3Additive_scalar_base_axis0 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  fromCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis0 ≡
  plusField3 (fromCoordinates3 (scalarField3 x0 x1 x2)) (fromCoordinates3 (scalarField3 y0 y1 y2)) Small.axis0
fromCoordinates3Additive_scalar_base_axis0 = Ring.solve-∀

fromCoordinates3Additive_scalar_base_axis1 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  fromCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis1 ≡
  plusField3 (fromCoordinates3 (scalarField3 x0 x1 x2)) (fromCoordinates3 (scalarField3 y0 y1 y2)) Small.axis1
fromCoordinates3Additive_scalar_base_axis1 = Ring.solve-∀

fromCoordinates3Additive_scalar_base_axis2 :
  (x0 x1 x2 y0 y1 y2 : ℚ) →
  fromCoordinates3 (plusField3 (scalarField3 x0 x1 x2) (scalarField3 y0 y1 y2)) Small.axis2 ≡
  plusField3 (fromCoordinates3 (scalarField3 x0 x1 x2)) (fromCoordinates3 (scalarField3 y0 y1 y2)) Small.axis2
fromCoordinates3Additive_scalar_base_axis2 = Ring.solve-∀

fromCoordinates3Additive :
  (f g : Field3) (i : Small.Three) →
  fromCoordinates3 (plusField3 f g) i ≡
  plusField3 (fromCoordinates3 f) (fromCoordinates3 g) i
fromCoordinates3Additive f g Small.axis0 = fromCoordinates3Additive_scalar_base_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)
fromCoordinates3Additive f g Small.axis1 = fromCoordinates3Additive_scalar_base_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)
fromCoordinates3Additive f g Small.axis2 = fromCoordinates3Additive_scalar_base_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2) (g Small.axis0) (g Small.axis1) (g Small.axis2)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates3Intertwines_scalar_permIdentity_axis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permIdentity (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3Intertwines_scalar_permIdentity_axis0 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permIdentity_axis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permIdentity (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3Intertwines_scalar_permIdentity_axis1 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permIdentity_axis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permIdentity (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permIdentity (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3Intertwines_scalar_permIdentity_axis2 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permRotate_axis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permRotate (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3Intertwines_scalar_permRotate_axis0 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permRotate_axis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permRotate (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3Intertwines_scalar_permRotate_axis1 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permRotate_axis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permRotate (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3Intertwines_scalar_permRotate_axis2 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permRotate2_axis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permRotate2 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3Intertwines_scalar_permRotate2_axis0 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permRotate2_axis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permRotate2 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3Intertwines_scalar_permRotate2_axis1 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permRotate2_axis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permRotate2 (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permRotate2 (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3Intertwines_scalar_permRotate2_axis2 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permSwapLowMid_axis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permSwapLowMid (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3Intertwines_scalar_permSwapLowMid_axis0 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permSwapLowMid_axis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permSwapLowMid (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3Intertwines_scalar_permSwapLowMid_axis1 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permSwapLowMid_axis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowMid (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permSwapLowMid (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3Intertwines_scalar_permSwapLowMid_axis2 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permSwapLowHigh_axis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permSwapLowHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3Intertwines_scalar_permSwapLowHigh_axis0 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permSwapLowHigh_axis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permSwapLowHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3Intertwines_scalar_permSwapLowHigh_axis1 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permSwapLowHigh_axis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapLowHigh (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permSwapLowHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3Intertwines_scalar_permSwapLowHigh_axis2 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permSwapMidHigh_axis0 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis0 ≡
  sourceAction3 Perm.permSwapMidHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis0
fromCoordinates3Intertwines_scalar_permSwapMidHigh_axis0 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permSwapMidHigh_axis1 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis1 ≡
  sourceAction3 Perm.permSwapMidHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis1
fromCoordinates3Intertwines_scalar_permSwapMidHigh_axis1 = Ring.solve-∀

fromCoordinates3Intertwines_scalar_permSwapMidHigh_axis2 :
  (x0 x1 x2 : ℚ) →
  fromCoordinates3 (coordinateAction3 Perm.permSwapMidHigh (scalarField3 x0 x1 x2)) Small.axis2 ≡
  sourceAction3 Perm.permSwapMidHigh (fromCoordinates3 (scalarField3 x0 x1 x2)) Small.axis2
fromCoordinates3Intertwines_scalar_permSwapMidHigh_axis2 = Ring.solve-∀

fromCoordinates3Intertwines :
  (p : Perm.TriPermutation) (f : Field3) (i : Small.Three) →
  fromCoordinates3 (coordinateAction3 p f) i ≡
  sourceAction3 p (fromCoordinates3 f) i
fromCoordinates3Intertwines Perm.permIdentity f Small.axis0 = fromCoordinates3Intertwines_scalar_permIdentity_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permIdentity f Small.axis1 = fromCoordinates3Intertwines_scalar_permIdentity_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permIdentity f Small.axis2 = fromCoordinates3Intertwines_scalar_permIdentity_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate f Small.axis0 = fromCoordinates3Intertwines_scalar_permRotate_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate f Small.axis1 = fromCoordinates3Intertwines_scalar_permRotate_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate f Small.axis2 = fromCoordinates3Intertwines_scalar_permRotate_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate2 f Small.axis0 = fromCoordinates3Intertwines_scalar_permRotate2_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate2 f Small.axis1 = fromCoordinates3Intertwines_scalar_permRotate2_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permRotate2 f Small.axis2 = fromCoordinates3Intertwines_scalar_permRotate2_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowMid f Small.axis0 = fromCoordinates3Intertwines_scalar_permSwapLowMid_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowMid f Small.axis1 = fromCoordinates3Intertwines_scalar_permSwapLowMid_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowMid f Small.axis2 = fromCoordinates3Intertwines_scalar_permSwapLowMid_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis0 = fromCoordinates3Intertwines_scalar_permSwapLowHigh_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis1 = fromCoordinates3Intertwines_scalar_permSwapLowHigh_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapLowHigh f Small.axis2 = fromCoordinates3Intertwines_scalar_permSwapLowHigh_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis0 = fromCoordinates3Intertwines_scalar_permSwapMidHigh_axis0 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis1 = fromCoordinates3Intertwines_scalar_permSwapMidHigh_axis1 (f Small.axis0) (f Small.axis1) (f Small.axis2)
fromCoordinates3Intertwines Perm.permSwapMidHigh f Small.axis2 = fromCoordinates3Intertwines_scalar_permSwapMidHigh_axis2 (f Small.axis0) (f Small.axis1) (f Small.axis2)

plusField6 : Field6 → Field6 → Field6
plusField6 f g i = f i + g i

-- Scalar identities, instantiated with original field coordinates.
toCoordinates6Additive_scalar_base_slot0 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot0 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot0
toCoordinates6Additive_scalar_base_slot0 = Ring.solve-∀

toCoordinates6Additive_scalar_base_slot1 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot1 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot1
toCoordinates6Additive_scalar_base_slot1 = Ring.solve-∀

toCoordinates6Additive_scalar_base_slot2 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot2 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot2
toCoordinates6Additive_scalar_base_slot2 = Ring.solve-∀

toCoordinates6Additive_scalar_base_slot3 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot3 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot3
toCoordinates6Additive_scalar_base_slot3 = Ring.solve-∀

toCoordinates6Additive_scalar_base_slot4 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot4 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot4
toCoordinates6Additive_scalar_base_slot4 = Ring.solve-∀

toCoordinates6Additive_scalar_base_slot5 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  toCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot5 ≡
  plusField6 (toCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (toCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot5
toCoordinates6Additive_scalar_base_slot5 = Ring.solve-∀

toCoordinates6Additive :
  (f g : Field6) (i : Big.Six) →
  toCoordinates6 (plusField6 f g) i ≡
  plusField6 (toCoordinates6 f) (toCoordinates6 g) i
toCoordinates6Additive f g Big.slot0 = toCoordinates6Additive_scalar_base_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
toCoordinates6Additive f g Big.slot1 = toCoordinates6Additive_scalar_base_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
toCoordinates6Additive f g Big.slot2 = toCoordinates6Additive_scalar_base_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
toCoordinates6Additive f g Big.slot3 = toCoordinates6Additive_scalar_base_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
toCoordinates6Additive f g Big.slot4 = toCoordinates6Additive_scalar_base_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
toCoordinates6Additive f g Big.slot5 = toCoordinates6Additive_scalar_base_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates6Additive_scalar_base_slot0 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot0 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot0
fromCoordinates6Additive_scalar_base_slot0 = Ring.solve-∀

fromCoordinates6Additive_scalar_base_slot1 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot1 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot1
fromCoordinates6Additive_scalar_base_slot1 = Ring.solve-∀

fromCoordinates6Additive_scalar_base_slot2 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot2 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot2
fromCoordinates6Additive_scalar_base_slot2 = Ring.solve-∀

fromCoordinates6Additive_scalar_base_slot3 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot3 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot3
fromCoordinates6Additive_scalar_base_slot3 = Ring.solve-∀

fromCoordinates6Additive_scalar_base_slot4 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot4 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot4
fromCoordinates6Additive_scalar_base_slot4 = Ring.solve-∀

fromCoordinates6Additive_scalar_base_slot5 :
  (x0 x1 x2 x3 x4 x5 y0 y1 y2 y3 y4 y5 : ℚ) →
  fromCoordinates6 (plusField6 (scalarField6 x0 x1 x2 x3 x4 x5) (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot5 ≡
  plusField6 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) (fromCoordinates6 (scalarField6 y0 y1 y2 y3 y4 y5)) Big.slot5
fromCoordinates6Additive_scalar_base_slot5 = Ring.solve-∀

fromCoordinates6Additive :
  (f g : Field6) (i : Big.Six) →
  fromCoordinates6 (plusField6 f g) i ≡
  plusField6 (fromCoordinates6 f) (fromCoordinates6 g) i
fromCoordinates6Additive f g Big.slot0 = fromCoordinates6Additive_scalar_base_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
fromCoordinates6Additive f g Big.slot1 = fromCoordinates6Additive_scalar_base_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
fromCoordinates6Additive f g Big.slot2 = fromCoordinates6Additive_scalar_base_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
fromCoordinates6Additive f g Big.slot3 = fromCoordinates6Additive_scalar_base_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
fromCoordinates6Additive f g Big.slot4 = fromCoordinates6Additive_scalar_base_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)
fromCoordinates6Additive f g Big.slot5 = fromCoordinates6Additive_scalar_base_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5) (g Big.slot0) (g Big.slot1) (g Big.slot2) (g Big.slot3) (g Big.slot4) (g Big.slot5)

-- Scalar identities, instantiated with original field coordinates.
fromCoordinates6Intertwines_scalar_permIdentity_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6Intertwines_scalar_permIdentity_slot0 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permIdentity_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6Intertwines_scalar_permIdentity_slot1 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permIdentity_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6Intertwines_scalar_permIdentity_slot2 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permIdentity_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6Intertwines_scalar_permIdentity_slot3 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permIdentity_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6Intertwines_scalar_permIdentity_slot4 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permIdentity_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permIdentity (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permIdentity (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6Intertwines_scalar_permIdentity_slot5 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6Intertwines_scalar_permRotate_slot0 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6Intertwines_scalar_permRotate_slot1 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6Intertwines_scalar_permRotate_slot2 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6Intertwines_scalar_permRotate_slot3 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6Intertwines_scalar_permRotate_slot4 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permRotate (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6Intertwines_scalar_permRotate_slot5 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate2_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6Intertwines_scalar_permRotate2_slot0 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate2_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6Intertwines_scalar_permRotate2_slot1 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate2_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6Intertwines_scalar_permRotate2_slot2 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate2_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6Intertwines_scalar_permRotate2_slot3 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate2_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6Intertwines_scalar_permRotate2_slot4 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permRotate2_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permRotate2 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permRotate2 (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6Intertwines_scalar_permRotate2_slot5 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowMid_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6Intertwines_scalar_permSwapLowMid_slot0 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowMid_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6Intertwines_scalar_permSwapLowMid_slot1 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowMid_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6Intertwines_scalar_permSwapLowMid_slot2 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowMid_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6Intertwines_scalar_permSwapLowMid_slot3 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowMid_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6Intertwines_scalar_permSwapLowMid_slot4 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowMid_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowMid (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permSwapLowMid (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6Intertwines_scalar_permSwapLowMid_slot5 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot0 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot1 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot2 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot3 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot4 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapLowHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permSwapLowHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot5 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot0 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot0
fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot0 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot1 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot1
fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot1 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot2 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot2
fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot2 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot3 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot3
fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot3 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot4 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot4
fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot4 = Ring.solve-∀

fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot5 :
  (x0 x1 x2 x3 x4 x5 : ℚ) →
  fromCoordinates6 (coordinateAction6 Perm.permSwapMidHigh (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5 ≡
  sourceAction6 Perm.permSwapMidHigh (fromCoordinates6 (scalarField6 x0 x1 x2 x3 x4 x5)) Big.slot5
fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot5 = Ring.solve-∀

fromCoordinates6Intertwines :
  (p : Perm.TriPermutation) (f : Field6) (i : Big.Six) →
  fromCoordinates6 (coordinateAction6 p f) i ≡
  sourceAction6 p (fromCoordinates6 f) i
fromCoordinates6Intertwines Perm.permIdentity f Big.slot0 = fromCoordinates6Intertwines_scalar_permIdentity_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permIdentity f Big.slot1 = fromCoordinates6Intertwines_scalar_permIdentity_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permIdentity f Big.slot2 = fromCoordinates6Intertwines_scalar_permIdentity_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permIdentity f Big.slot3 = fromCoordinates6Intertwines_scalar_permIdentity_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permIdentity f Big.slot4 = fromCoordinates6Intertwines_scalar_permIdentity_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permIdentity f Big.slot5 = fromCoordinates6Intertwines_scalar_permIdentity_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot0 = fromCoordinates6Intertwines_scalar_permRotate_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot1 = fromCoordinates6Intertwines_scalar_permRotate_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot2 = fromCoordinates6Intertwines_scalar_permRotate_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot3 = fromCoordinates6Intertwines_scalar_permRotate_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot4 = fromCoordinates6Intertwines_scalar_permRotate_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate f Big.slot5 = fromCoordinates6Intertwines_scalar_permRotate_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot0 = fromCoordinates6Intertwines_scalar_permRotate2_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot1 = fromCoordinates6Intertwines_scalar_permRotate2_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot2 = fromCoordinates6Intertwines_scalar_permRotate2_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot3 = fromCoordinates6Intertwines_scalar_permRotate2_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot4 = fromCoordinates6Intertwines_scalar_permRotate2_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permRotate2 f Big.slot5 = fromCoordinates6Intertwines_scalar_permRotate2_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot0 = fromCoordinates6Intertwines_scalar_permSwapLowMid_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot1 = fromCoordinates6Intertwines_scalar_permSwapLowMid_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot2 = fromCoordinates6Intertwines_scalar_permSwapLowMid_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot3 = fromCoordinates6Intertwines_scalar_permSwapLowMid_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot4 = fromCoordinates6Intertwines_scalar_permSwapLowMid_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowMid f Big.slot5 = fromCoordinates6Intertwines_scalar_permSwapLowMid_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot0 = fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot1 = fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot2 = fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot3 = fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot4 = fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapLowHigh f Big.slot5 = fromCoordinates6Intertwines_scalar_permSwapLowHigh_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot0 = fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot0 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot1 = fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot1 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot2 = fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot2 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot3 = fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot3 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot4 = fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot4 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
fromCoordinates6Intertwines Perm.permSwapMidHigh f Big.slot5 = fromCoordinates6Intertwines_scalar_permSwapMidHigh_slot5 (f Big.slot0) (f Big.slot1) (f Big.slot2) (f Big.slot3) (f Big.slot4) (f Big.slot5)
