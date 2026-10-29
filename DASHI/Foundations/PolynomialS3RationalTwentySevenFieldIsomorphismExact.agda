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
open import Data.Rational.Base using (ℚ)
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
