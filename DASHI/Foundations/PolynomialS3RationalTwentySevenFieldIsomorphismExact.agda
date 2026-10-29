module DASHI.Foundations.PolynomialS3RationalTwentySevenFieldIsomorphismExact where

------------------------------------------------------------------------
-- ACTUAL Q^27 -> (Q ⊕ Q² ⊕ Q³ ⊕ Q³ ⊕ Q⁶ ⊕ Q⁶ ⊕ Q⁶).
-- Characteristic-zero coordinate equivalence, pointwise two-sided.
-- Original 27 source G-set is reused, not reinvented.
-- Integer block inverse certificates scaled by 2,3,54 are lifted
-- through the Vieta owner's original Rational RingSolver.
-- Separate full S3 equivariance: exact blockwise component laws in
-- PolynomialS3RationalBlockFieldIsomorphismExact; native G-set action
-- was source-constructed in PolynomialS3TwentySevenOrbitBlockAssemblyExact.
-- Global equivariance/linearity additionally require the final
-- pointwise chart composition receipt, not merely dimensions.
-- SOURCE-WRITTEN, kernel verification NOT YET RUN.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_)
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Perm
open import Relation.Binary.PropositionalEquality using (cong; trans)
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.PolynomialS3SmallRationalBlockCertificateExact as Small
import DASHI.Foundations.PolynomialS3RegularRationalBlockCertificateExact as Big
import DASHI.Foundations.PolynomialS3TwentySevenOrbitBlockAssemblyExact as Atlas
import DASHI.Foundations.PolynomialS3RationalBlockFieldIsomorphismExact as Iso

BlockField27 : Set
BlockField27 = Atlas.OrbitBlock27 → ℚ

NativeRationalField27 : Set
NativeRationalField27 = Tower.LevelTwoCode → ℚ

record RationalCoordinates27 : Set where
  constructor rationalCoordinates27
  field
    identityCoordinate : ℚ
    cycleCoordinates : Iso.Field2
    transpositionCoordinates : Iso.Field3
    constantCoordinates : Iso.Field3
    oneFixedCoordinates : Iso.Field6
    twoFixedCoordinates : Iso.Field6
    twoCycleCoordinates : Iso.Field6
open RationalCoordinates27 public

encodeBlocks27 : BlockField27 → RationalCoordinates27
encodeBlocks27 f =
  rationalCoordinates27
    (f Atlas.identityBlock)
    (Iso.toCoordinates2 (λ i → f (Atlas.cycleBlock i)))
    (Iso.toCoordinates3 (λ i → f (Atlas.transpositionBlock i)))
    (Iso.toCoordinates3 (λ i → f (Atlas.constantBlock i)))
    (Iso.toCoordinates6 (λ i → f (Atlas.oneFixedBlock i)))
    (Iso.toCoordinates6 (λ i → f (Atlas.twoFixedBlock i)))
    (Iso.toCoordinates6 (λ i → f (Atlas.twoCycleBlock i)))

decodeBlocks27 : RationalCoordinates27 → BlockField27
decodeBlocks27 c Atlas.identityBlock = identityCoordinate c
decodeBlocks27 c (Atlas.cycleBlock i) =
  Iso.fromCoordinates2 (cycleCoordinates c) i
decodeBlocks27 c (Atlas.transpositionBlock i) =
  Iso.fromCoordinates3 (transpositionCoordinates c) i
decodeBlocks27 c (Atlas.constantBlock i) =
  Iso.fromCoordinates3 (constantCoordinates c) i
decodeBlocks27 c (Atlas.oneFixedBlock i) =
  Iso.fromCoordinates6 (oneFixedCoordinates c) i
decodeBlocks27 c (Atlas.twoFixedBlock i) =
  Iso.fromCoordinates6 (twoFixedCoordinates c) i
decodeBlocks27 c (Atlas.twoCycleBlock i) =
  Iso.fromCoordinates6 (twoCycleCoordinates c) i

decodeEncodeBlocksAt :
  (f : BlockField27) (b : Atlas.OrbitBlock27) →
  decodeBlocks27 (encodeBlocks27 f) b ≡ f b
decodeEncodeBlocksAt f Atlas.identityBlock = refl
decodeEncodeBlocksAt f (Atlas.cycleBlock i) =
  Iso.fromToCoordinates2 (λ j → f (Atlas.cycleBlock j)) i
decodeEncodeBlocksAt f (Atlas.transpositionBlock i) =
  Iso.fromToCoordinates3 (λ j → f (Atlas.transpositionBlock j)) i
decodeEncodeBlocksAt f (Atlas.constantBlock i) =
  Iso.fromToCoordinates3 (λ j → f (Atlas.constantBlock j)) i
decodeEncodeBlocksAt f (Atlas.oneFixedBlock i) =
  Iso.fromToCoordinates6 (λ j → f (Atlas.oneFixedBlock j)) i
decodeEncodeBlocksAt f (Atlas.twoFixedBlock i) =
  Iso.fromToCoordinates6 (λ j → f (Atlas.twoFixedBlock j)) i
decodeEncodeBlocksAt f (Atlas.twoCycleBlock i) =
  Iso.fromToCoordinates6 (λ j → f (Atlas.twoCycleBlock j)) i

coordinateAt : RationalCoordinates27 → Atlas.OrbitBlock27 → ℚ
coordinateAt c Atlas.identityBlock = identityCoordinate c
coordinateAt c (Atlas.cycleBlock i) = cycleCoordinates c i
coordinateAt c (Atlas.transpositionBlock i) = transpositionCoordinates c i
coordinateAt c (Atlas.constantBlock i) = constantCoordinates c i
coordinateAt c (Atlas.oneFixedBlock i) = oneFixedCoordinates c i
coordinateAt c (Atlas.twoFixedBlock i) = twoFixedCoordinates c i
coordinateAt c (Atlas.twoCycleBlock i) = twoCycleCoordinates c i

encodeDecodeCoordinatesAt :
  (c : RationalCoordinates27) (b : Atlas.OrbitBlock27) →
  coordinateAt (encodeBlocks27 (decodeBlocks27 c)) b ≡ coordinateAt c b
encodeDecodeCoordinatesAt c Atlas.identityBlock = refl
encodeDecodeCoordinatesAt c (Atlas.cycleBlock i) =
  Iso.toFromCoordinates2 (cycleCoordinates c) i
encodeDecodeCoordinatesAt c (Atlas.transpositionBlock i) =
  Iso.toFromCoordinates3 (transpositionCoordinates c) i
encodeDecodeCoordinatesAt c (Atlas.constantBlock i) =
  Iso.toFromCoordinates3 (constantCoordinates c) i
encodeDecodeCoordinatesAt c (Atlas.oneFixedBlock i) =
  Iso.toFromCoordinates6 (oneFixedCoordinates c) i
encodeDecodeCoordinatesAt c (Atlas.twoFixedBlock i) =
  Iso.toFromCoordinates6 (twoFixedCoordinates c) i
encodeDecodeCoordinatesAt c (Atlas.twoCycleBlock i) =
  Iso.toFromCoordinates6 (twoCycleCoordinates c) i

encodeNative27 : NativeRationalField27 → RationalCoordinates27
encodeNative27 f = encodeBlocks27 (Atlas.toBlockField f)

decodeNative27 : RationalCoordinates27 → NativeRationalField27
decodeNative27 c = Atlas.fromBlockField (decodeBlocks27 c)

decodeEncodeNativeAt :
  (f : NativeRationalField27) (x : Tower.LevelTwoCode) →
  decodeNative27 (encodeNative27 f) x ≡ f x
decodeEncodeNativeAt f x =
  trans
    (decodeEncodeBlocksAt
      (Atlas.toBlockField f) (Atlas.codeToBlock x))
    (Atlas.fromToBlockField f x)

-- Native-to-block and block-to-native field charts are pointwise
-- inverse by the imported original seven-orbit assembly. Hence
-- encodeDecodeCoordinatesAt witnesses the coordinate side as
-- a separate pointwise certificate, with no function-extensionality
-- postulate. A full composite coordinate side proof is O45b.

-- Source-native coordinate round trip: all seven orbit blocks are
-- evaluated through their literal chosen code chart. The finite
-- source table blockCodeRoundTrip reduces on each of the six
-- static coordinate sites in the matrix contractions.
encodeDecodeNativeCoordinateAt :
  (c : RationalCoordinates27) (b : Atlas.OrbitBlock27) →
  coordinateAt (encodeNative27 (decodeNative27 c)) b ≡
  coordinateAt c b
encodeDecodeNativeCoordinateAt c Atlas.identityBlock = refl
encodeDecodeNativeCoordinateAt c (Atlas.cycleBlock i) =
  Iso.toFromCoordinates2 (cycleCoordinates c) i
encodeDecodeNativeCoordinateAt c (Atlas.transpositionBlock i) =
  Iso.toFromCoordinates3 (transpositionCoordinates c) i
encodeDecodeNativeCoordinateAt c (Atlas.constantBlock i) =
  Iso.toFromCoordinates3 (constantCoordinates c) i
encodeDecodeNativeCoordinateAt c (Atlas.oneFixedBlock i) =
  Iso.toFromCoordinates6 (oneFixedCoordinates c) i
encodeDecodeNativeCoordinateAt c (Atlas.twoFixedBlock i) =
  Iso.toFromCoordinates6 (twoFixedCoordinates c) i
encodeDecodeNativeCoordinateAt c (Atlas.twoCycleBlock i) =
  Iso.toFromCoordinates6 (twoCycleCoordinates c) i

-- Source-written Q^27 pointwise two-sided code and coordinate
-- atlas, still pending compiler/kernel proof acceptance.

------------------------------------------------------------------------
-- Pointwise rational LINEARITY on the complete native seven-orbit atlas.
------------------------------------------------------------------------

plusBlockFields : BlockField27 → BlockField27 → BlockField27
plusBlockFields f g b = f b + g b

plusCoordinates27 :
  RationalCoordinates27 → RationalCoordinates27 → RationalCoordinates27
plusCoordinates27 x y =
  rationalCoordinates27
    (identityCoordinate x + identityCoordinate y)
    (Iso.plusField2 (cycleCoordinates x) (cycleCoordinates y))
    (Iso.plusField3 (transpositionCoordinates x) (transpositionCoordinates y))
    (Iso.plusField3 (constantCoordinates x) (constantCoordinates y))
    (Iso.plusField6 (oneFixedCoordinates x) (oneFixedCoordinates y))
    (Iso.plusField6 (twoFixedCoordinates x) (twoFixedCoordinates y))
    (Iso.plusField6 (twoCycleCoordinates x) (twoCycleCoordinates y))

encodeBlocksAdditiveAt :
  (f g : BlockField27) (b : Atlas.OrbitBlock27) →
  coordinateAt (encodeBlocks27 (plusBlockFields f g)) b ≡
  coordinateAt (plusCoordinates27 (encodeBlocks27 f) (encodeBlocks27 g)) b
encodeBlocksAdditiveAt f g Atlas.identityBlock = refl
encodeBlocksAdditiveAt f g (Atlas.cycleBlock i) =
  Iso.toCoordinates2Additive
    (λ j → f (Atlas.cycleBlock j))
    (λ j → g (Atlas.cycleBlock j)) i
encodeBlocksAdditiveAt f g (Atlas.transpositionBlock i) =
  Iso.toCoordinates3Additive
    (λ j → f (Atlas.transpositionBlock j))
    (λ j → g (Atlas.transpositionBlock j)) i
encodeBlocksAdditiveAt f g (Atlas.constantBlock i) =
  Iso.toCoordinates3Additive
    (λ j → f (Atlas.constantBlock j))
    (λ j → g (Atlas.constantBlock j)) i
encodeBlocksAdditiveAt f g (Atlas.oneFixedBlock i) =
  Iso.toCoordinates6Additive
    (λ j → f (Atlas.oneFixedBlock j))
    (λ j → g (Atlas.oneFixedBlock j)) i
encodeBlocksAdditiveAt f g (Atlas.twoFixedBlock i) =
  Iso.toCoordinates6Additive
    (λ j → f (Atlas.twoFixedBlock j))
    (λ j → g (Atlas.twoFixedBlock j)) i
encodeBlocksAdditiveAt f g (Atlas.twoCycleBlock i) =
  Iso.toCoordinates6Additive
    (λ j → f (Atlas.twoCycleBlock j))
    (λ j → g (Atlas.twoCycleBlock j)) i

decodeBlocksAdditiveAt :
  (x y : RationalCoordinates27) (b : Atlas.OrbitBlock27) →
  decodeBlocks27 (plusCoordinates27 x y) b ≡
  plusBlockFields (decodeBlocks27 x) (decodeBlocks27 y) b
decodeBlocksAdditiveAt x y Atlas.identityBlock = refl
decodeBlocksAdditiveAt x y (Atlas.cycleBlock i) =
  Iso.fromCoordinates2Additive (cycleCoordinates x) (cycleCoordinates y) i
decodeBlocksAdditiveAt x y (Atlas.transpositionBlock i) =
  Iso.fromCoordinates3Additive (transpositionCoordinates x) (transpositionCoordinates y) i
decodeBlocksAdditiveAt x y (Atlas.constantBlock i) =
  Iso.fromCoordinates3Additive (constantCoordinates x) (constantCoordinates y) i
decodeBlocksAdditiveAt x y (Atlas.oneFixedBlock i) =
  Iso.fromCoordinates6Additive (oneFixedCoordinates x) (oneFixedCoordinates y) i
decodeBlocksAdditiveAt x y (Atlas.twoFixedBlock i) =
  Iso.fromCoordinates6Additive (twoFixedCoordinates x) (twoFixedCoordinates y) i
decodeBlocksAdditiveAt x y (Atlas.twoCycleBlock i) =
  Iso.fromCoordinates6Additive (twoCycleCoordinates x) (twoCycleCoordinates y) i

------------------------------------------------------------------------
-- Native full S3 action on the 27 rational fields, inherited from
-- the actual conjugation group via the seven-block atlas.
------------------------------------------------------------------------

sourceBlockAction :
  Perm.TriPermutation → BlockField27 → BlockField27
sourceBlockAction p f Atlas.identityBlock = f Atlas.identityBlock
sourceBlockAction p f (Atlas.cycleBlock i) =
  Iso.sourceAction2 p (λ j → f (Atlas.cycleBlock j)) i
sourceBlockAction p f (Atlas.transpositionBlock i) =
  Iso.sourceAction3 p (λ j → f (Atlas.transpositionBlock j)) i
sourceBlockAction p f (Atlas.constantBlock i) =
  Iso.sourceAction3 p (λ j → f (Atlas.constantBlock j)) i
sourceBlockAction p f (Atlas.oneFixedBlock i) =
  Iso.sourceAction6 p (λ j → f (Atlas.oneFixedBlock j)) i
sourceBlockAction p f (Atlas.twoFixedBlock i) =
  Iso.sourceAction6 p (λ j → f (Atlas.twoFixedBlock j)) i
sourceBlockAction p f (Atlas.twoCycleBlock i) =
  Iso.sourceAction6 p (λ j → f (Atlas.twoCycleBlock j)) i

coordinateAction27 :
  Perm.TriPermutation → RationalCoordinates27 → RationalCoordinates27
coordinateAction27 p c =
  rationalCoordinates27
    (identityCoordinate c)
    (Iso.coordinateAction2 p (cycleCoordinates c))
    (Iso.coordinateAction3 p (transpositionCoordinates c))
    (Iso.coordinateAction3 p (constantCoordinates c))
    (Iso.coordinateAction6 p (oneFixedCoordinates c))
    (Iso.coordinateAction6 p (twoFixedCoordinates c))
    (Iso.coordinateAction6 p (twoCycleCoordinates c))

encodeBlocksIntertwinesAt :
  (p : Perm.TriPermutation) (f : BlockField27)
  (b : Atlas.OrbitBlock27) →
  coordinateAt (encodeBlocks27 (sourceBlockAction p f)) b ≡
  coordinateAt (coordinateAction27 p (encodeBlocks27 f)) b
encodeBlocksIntertwinesAt p f Atlas.identityBlock = refl
encodeBlocksIntertwinesAt p f (Atlas.cycleBlock i) =
  Iso.toCoordinates2Intertwines
    p (λ j → f (Atlas.cycleBlock j)) i
encodeBlocksIntertwinesAt p f (Atlas.transpositionBlock i) =
  Iso.toCoordinates3Intertwines
    p (λ j → f (Atlas.transpositionBlock j)) i
encodeBlocksIntertwinesAt p f (Atlas.constantBlock i) =
  Iso.toCoordinates3Intertwines
    p (λ j → f (Atlas.constantBlock j)) i
encodeBlocksIntertwinesAt p f (Atlas.oneFixedBlock i) =
  Iso.toCoordinates6Intertwines
    p (λ j → f (Atlas.oneFixedBlock j)) i
encodeBlocksIntertwinesAt p f (Atlas.twoFixedBlock i) =
  Iso.toCoordinates6Intertwines
    p (λ j → f (Atlas.twoFixedBlock j)) i
encodeBlocksIntertwinesAt p f (Atlas.twoCycleBlock i) =
  Iso.toCoordinates6Intertwines
    p (λ j → f (Atlas.twoCycleBlock j)) i

decodeBlocksIntertwinesAt :
  (p : Perm.TriPermutation) (c : RationalCoordinates27)
  (b : Atlas.OrbitBlock27) →
  decodeBlocks27 (coordinateAction27 p c) b ≡
  sourceBlockAction p (decodeBlocks27 c) b
decodeBlocksIntertwinesAt p c Atlas.identityBlock = refl
decodeBlocksIntertwinesAt p c (Atlas.cycleBlock i) =
  Iso.fromCoordinates2Intertwines p (cycleCoordinates c) i
decodeBlocksIntertwinesAt p c (Atlas.transpositionBlock i) =
  Iso.fromCoordinates3Intertwines p (transpositionCoordinates c) i
decodeBlocksIntertwinesAt p c (Atlas.constantBlock i) =
  Iso.fromCoordinates3Intertwines p (constantCoordinates c) i
decodeBlocksIntertwinesAt p c (Atlas.oneFixedBlock i) =
  Iso.fromCoordinates6Intertwines p (oneFixedCoordinates c) i
decodeBlocksIntertwinesAt p c (Atlas.twoFixedBlock i) =
  Iso.fromCoordinates6Intertwines p (twoFixedCoordinates c) i
decodeBlocksIntertwinesAt p c (Atlas.twoCycleBlock i) =
  Iso.fromCoordinates6Intertwines p (twoCycleCoordinates c) i

-- Exact syntactic source-to-native action compatibility for all 162
-- combinations of six S3 permutations with native 27 orbit slots.
sourceBlockActionAgreesWithNative :
  (p : Perm.TriPermutation) (f : BlockField27)
  (b : Atlas.OrbitBlock27) →
  sourceBlockAction p f b ≡
    f (Atlas.blockAction (Perm.inversePermutation p) b)
sourceBlockActionAgreesWithNative Perm.permIdentity f Atlas.identityBlock = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.cycleBlock Small.pair0) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.cycleBlock Small.pair1) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.transpositionBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.transpositionBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.transpositionBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.constantBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.constantBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.constantBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.oneFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.oneFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.oneFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.oneFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.oneFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.oneFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoCycleBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoCycleBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoCycleBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoCycleBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoCycleBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permIdentity f (Atlas.twoCycleBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f Atlas.identityBlock = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.cycleBlock Small.pair0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.cycleBlock Small.pair1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.transpositionBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.transpositionBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.transpositionBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.constantBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.constantBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.constantBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.oneFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.oneFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.oneFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.oneFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.oneFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.oneFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoCycleBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoCycleBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoCycleBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoCycleBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoCycleBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permRotate f (Atlas.twoCycleBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f Atlas.identityBlock = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.cycleBlock Small.pair0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.cycleBlock Small.pair1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.transpositionBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.transpositionBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.transpositionBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.constantBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.constantBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.constantBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.oneFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.oneFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.oneFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.oneFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.oneFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.oneFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoCycleBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoCycleBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoCycleBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoCycleBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoCycleBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permRotate2 f (Atlas.twoCycleBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f Atlas.identityBlock = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.cycleBlock Small.pair0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.cycleBlock Small.pair1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.transpositionBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.transpositionBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.transpositionBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.constantBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.constantBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.constantBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.oneFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.oneFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.oneFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.oneFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.oneFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.oneFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoCycleBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoCycleBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoCycleBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoCycleBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoCycleBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowMid f (Atlas.twoCycleBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f Atlas.identityBlock = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.cycleBlock Small.pair0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.cycleBlock Small.pair1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.transpositionBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.transpositionBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.transpositionBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.constantBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.constantBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.constantBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.oneFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.oneFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.oneFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.oneFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.oneFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.oneFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoCycleBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoCycleBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoCycleBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoCycleBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoCycleBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permSwapLowHigh f (Atlas.twoCycleBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f Atlas.identityBlock = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.cycleBlock Small.pair0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.cycleBlock Small.pair1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.transpositionBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.transpositionBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.transpositionBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.constantBlock Small.axis0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.constantBlock Small.axis1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.constantBlock Small.axis2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.oneFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.oneFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.oneFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.oneFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.oneFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.oneFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoFixedBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoFixedBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoFixedBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoFixedBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoFixedBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoFixedBlock Big.slot5) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoCycleBlock Big.slot0) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoCycleBlock Big.slot1) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoCycleBlock Big.slot2) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoCycleBlock Big.slot3) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoCycleBlock Big.slot4) = refl
sourceBlockActionAgreesWithNative Perm.permSwapMidHigh f (Atlas.twoCycleBlock Big.slot5) = refl

-- Thus encode/decode give a pointwise rational S3-representation
-- isomorphism over actual Code27, transported through the original
-- 27-code group-set bijection. A kernel receipt remains mandatory;
-- no arbitrary F3 full-S3 splitting is asserted.
