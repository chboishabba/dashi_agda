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
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.PolynomialS3SmallRationalBlockCertificateExact as Small
import DASHI.Foundations.PolynomialS3RegularRationalBlockCertificateExact as Big
import DASHI.Foundations.TernaryEndomorphismS3ActionLawsExact as ActionLaws
import DASHI.Foundations.TernaryPermutationS3LawsExact as S3
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

------------------------------------------------------------------------
-- Native rational transport receipts (O69--O72).
--
-- These consume the ORIGINAL 27-code atlas and the existing 2/3/6
-- block-coordinate proofs. Equality stays pointwise: there is no
-- function-extensionality axiom and no identification with a different
-- action, Galois group or Monster representation.
-- SOURCE-WRITTEN / Agda kernel acceptance still pending.
------------------------------------------------------------------------

plusNativeFields : NativeRationalField27 →
  NativeRationalField27 → NativeRationalField27
plusNativeFields f g x = f x + g x

encodeNativeAdditiveAt :
  (f g : NativeRationalField27) (b : Atlas.OrbitBlock27) →
  coordinateAt (encodeNative27 (plusNativeFields f g)) b ≡
  coordinateAt (plusCoordinates27 (encodeNative27 f) (encodeNative27 g)) b
encodeNativeAdditiveAt f g b =
  encodeBlocksAdditiveAt (Atlas.toBlockField f) (Atlas.toBlockField g) b

decodeNativeAdditiveAt :
  (c d : RationalCoordinates27) (x : Tower.LevelTwoCode) →
  decodeNative27 (plusCoordinates27 c d) x ≡
  plusNativeFields (decodeNative27 c) (decodeNative27 d) x
decodeNativeAdditiveAt c d x =
  decodeBlocksAdditiveAt c d (Atlas.codeToBlock x)

-- Precompose with the inverse S3 permutation on the ORIGINAL native code.
nativeSourceAction27 :
  Perm.TriPermutation → NativeRationalField27 → NativeRationalField27
nativeSourceAction27 p f x =
  f (Perm.conjugateCode (Perm.inversePermutation p) x)

nativeActionAgreesWithBlockAt :
  (p : Perm.TriPermutation) (f : NativeRationalField27)
  (b : Atlas.OrbitBlock27) →
  Atlas.toBlockField (nativeSourceAction27 p f) b ≡
  sourceBlockAction p (Atlas.toBlockField f) b
nativeActionAgreesWithBlockAt p f b =
  trans
    (sym (cong f
      (Atlas.blockActionPreservesNative (Perm.inversePermutation p) b)))
    (sym (sourceBlockActionAgreesWithNative p (Atlas.toBlockField f) b))

decodeNativeIntertwinesAt :
  (p : Perm.TriPermutation) (c : RationalCoordinates27)
  (x : Tower.LevelTwoCode) →
  decodeNative27 (coordinateAction27 p c) x ≡
  nativeSourceAction27 p (decodeNative27 c) x
decodeNativeIntertwinesAt p c x =
  trans
    (decodeBlocksIntertwinesAt p c (Atlas.codeToBlock x))
    (trans
      (sourceBlockActionAgreesWithNative p (decodeBlocks27 c)
        (Atlas.codeToBlock x))
      (cong
        (λ y → decodeBlocks27 c
          (Atlas.codeToBlock
            (Perm.conjugateCode (Perm.inversePermutation p) y)))
        (Atlas.blockCodeRoundTrip x)))

------------------------------------------------------------------------
-- O73--O76: complete native S3 field-action and encoder equivariance.
-- Inherited native code conjugation and pointwise Q27 inverse machinery.
-- Finite-coordinate rewriting replaces function extensionality.
-- Classical finite S3 actions (Dixon--Mortimer); this #1414 adapter
-- does not identify polynomial-root monodromy or Monster 3B carriers.
-- SOURCE WRITTEN; compiler/kernel verification outstanding.
------------------------------------------------------------------------

-- The native action is a genuine pointwise left S3 action.
nativeSourceActionIdentityAt :
  (f : NativeRationalField27) (x : Tower.LevelTwoCode) →
  nativeSourceAction27 Perm.permIdentity f x ≡ f x
nativeSourceActionIdentityAt f x =
  cong f (ActionLaws.conjugateIdentity x)

nativeSourceActionCompositionAt :
  (p q : Perm.TriPermutation) (f : NativeRationalField27)
  (x : Tower.LevelTwoCode) →
  nativeSourceAction27 (S3._∙_ p q) f x ≡
  nativeSourceAction27 p (nativeSourceAction27 q f) x
nativeSourceActionCompositionAt p q f x =
  trans
    (cong (λ r → f (Perm.conjugateCode r x))
      (ActionLaws.inverseProduct p q))
    (cong f
      (ActionLaws.conjugateComposition
        (Perm.inversePermutation q) (Perm.inversePermutation p) x))

nativeSourceActionAdditiveAt :
  (p : Perm.TriPermutation) (f g : NativeRationalField27)
  (x : Tower.LevelTwoCode) →
  nativeSourceAction27 p (plusNativeFields f g) x ≡
  plusNativeFields (nativeSourceAction27 p f)
    (nativeSourceAction27 p g) x
nativeSourceActionAdditiveAt p f g x = refl

-- A pointwise equality over the actual Code27 carrier determines
-- all seven rational block coordinates without funext. Rewrites
-- expand the existing finite 1/2/3/6-point rational matrices.
encodeNativeRespectsPointwiseAt :
  (f g : NativeRationalField27) →
  ((x : Tower.LevelTwoCode) → f x ≡ g x) →
  (b : Atlas.OrbitBlock27) →
  coordinateAt (encodeNative27 f) b ≡
  coordinateAt (encodeNative27 g) b
encodeNativeRespectsPointwiseAt f g equal Atlas.identityBlock =
  equal (Atlas.blockToCode Atlas.identityBlock)
encodeNativeRespectsPointwiseAt f g equal (Atlas.cycleBlock i)
  rewrite equal (Atlas.blockToCode (Atlas.cycleBlock Small.pair0))
        | equal (Atlas.blockToCode (Atlas.cycleBlock Small.pair1)) = refl
encodeNativeRespectsPointwiseAt f g equal (Atlas.transpositionBlock i)
  rewrite equal (Atlas.blockToCode (Atlas.transpositionBlock Small.axis0))
        | equal (Atlas.blockToCode (Atlas.transpositionBlock Small.axis1))
        | equal (Atlas.blockToCode (Atlas.transpositionBlock Small.axis2)) = refl
encodeNativeRespectsPointwiseAt f g equal (Atlas.constantBlock i)
  rewrite equal (Atlas.blockToCode (Atlas.constantBlock Small.axis0))
        | equal (Atlas.blockToCode (Atlas.constantBlock Small.axis1))
        | equal (Atlas.blockToCode (Atlas.constantBlock Small.axis2)) = refl
encodeNativeRespectsPointwiseAt f g equal (Atlas.oneFixedBlock i)
  rewrite equal (Atlas.blockToCode (Atlas.oneFixedBlock Big.slot0))
        | equal (Atlas.blockToCode (Atlas.oneFixedBlock Big.slot1))
        | equal (Atlas.blockToCode (Atlas.oneFixedBlock Big.slot2))
        | equal (Atlas.blockToCode (Atlas.oneFixedBlock Big.slot3))
        | equal (Atlas.blockToCode (Atlas.oneFixedBlock Big.slot4))
        | equal (Atlas.blockToCode (Atlas.oneFixedBlock Big.slot5)) = refl
encodeNativeRespectsPointwiseAt f g equal (Atlas.twoFixedBlock i)
  rewrite equal (Atlas.blockToCode (Atlas.twoFixedBlock Big.slot0))
        | equal (Atlas.blockToCode (Atlas.twoFixedBlock Big.slot1))
        | equal (Atlas.blockToCode (Atlas.twoFixedBlock Big.slot2))
        | equal (Atlas.blockToCode (Atlas.twoFixedBlock Big.slot3))
        | equal (Atlas.blockToCode (Atlas.twoFixedBlock Big.slot4))
        | equal (Atlas.blockToCode (Atlas.twoFixedBlock Big.slot5)) = refl
encodeNativeRespectsPointwiseAt f g equal (Atlas.twoCycleBlock i)
  rewrite equal (Atlas.blockToCode (Atlas.twoCycleBlock Big.slot0))
        | equal (Atlas.blockToCode (Atlas.twoCycleBlock Big.slot1))
        | equal (Atlas.blockToCode (Atlas.twoCycleBlock Big.slot2))
        | equal (Atlas.blockToCode (Atlas.twoCycleBlock Big.slot3))
        | equal (Atlas.blockToCode (Atlas.twoCycleBlock Big.slot4))
        | equal (Atlas.blockToCode (Atlas.twoCycleBlock Big.slot5)) = refl

-- Decode the transported coordinate field and compare pointwise
-- to precomposition on the SAME native code carrier.
decodedNativeEquivAt :
  (p : Perm.TriPermutation) (f : NativeRationalField27)
  (x : Tower.LevelTwoCode) →
  decodeNative27 (coordinateAction27 p (encodeNative27 f)) x ≡
  nativeSourceAction27 p f x
decodedNativeEquivAt p f x =
  trans
    (decodeNativeIntertwinesAt p (encodeNative27 f) x)
    (decodeEncodeNativeAt f
      (Perm.conjugateCode (Perm.inversePermutation p) x))

-- Complete encoder-side S3 equivariance by transporting the
-- decoder commutative square across the original two-sided
-- coordinate inverse. No pointwise rational proofs are duplicated.
encodeNativeIntertwinesAt :
  (p : Perm.TriPermutation) (f : NativeRationalField27)
  (b : Atlas.OrbitBlock27) →
  coordinateAt (encodeNative27 (nativeSourceAction27 p f)) b ≡
  coordinateAt (coordinateAction27 p (encodeNative27 f)) b
encodeNativeIntertwinesAt p f b =
  trans
    (sym (encodeNativeRespectsPointwiseAt
      (decodeNative27 (coordinateAction27 p (encodeNative27 f)))
      (nativeSourceAction27 p f)
      (decodedNativeEquivAt p f) b))
    (encodeDecodeNativeCoordinateAt
      (coordinateAction27 p (encodeNative27 f)) b)
