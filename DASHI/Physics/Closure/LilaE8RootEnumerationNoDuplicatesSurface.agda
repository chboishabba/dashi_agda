module DASHI.Physics.Closure.LilaE8RootEnumerationNoDuplicatesSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base as List using (List; _∷_; [])
open import Data.Vec using (Vec)
import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary using (yes; no)

import DASHI.Algebra.Trit.HalfTrit as HT
import DASHI.Algebra.Trit.E8RootEnumeration as E8
import DASHI.Physics.Closure.LilaE8RootEnumerationReceiptR2 as R2

------------------------------------------------------------------------
-- LILA/E8 no-duplicates sidecar.
--
-- The algebra namespace now contains concrete indexed integer roots,
-- concrete indexed half roots, executable duplicate/disjointness checks, and
-- normalized count checks.  This sidecar exposes the strongest currently
-- available finite result to the closure namespace without promoting LILA-R3:
--
--   * the combined indexed root list has length 240;
--   * the combined indexed root list computes no-duplicates = true;
--   * integer and half indexed root families compute disjoint = true.
--
-- It does not claim native E8 completeness.  The first missing step is the
-- structural bridge from executable indexed-list checks to the native
-- membership/no-duplicates/completeness predicates consumed by LILA.

data LilaE8NoDuplicatesSurfaceStatus : Set where
  executableIndexedNoDuplicatesAvailableCompletenessBlocked :
    LilaE8NoDuplicatesSurfaceStatus

data LilaE8NoDuplicatesFirstMissing : Set where
  missingExecutableMembershipToNativeMembership :
    LilaE8NoDuplicatesFirstMissing
  missingIntegerTwoSparseCompleteness :
    LilaE8NoDuplicatesFirstMissing
  missingHalfEvenParityCompleteness :
    LilaE8NoDuplicatesFirstMissing
  missingCombinedE8Completeness :
    LilaE8NoDuplicatesFirstMissing
  missingUpstreamE8RootEnumerationCompletePromotion :
    LilaE8NoDuplicatesFirstMissing

data LilaE8MissingNativePredicateName : Set where
  expectedNativeE8RootMember :
    LilaE8MissingNativePredicateName
  expectedNativeE8RootNoDuplicates :
    LilaE8MissingNativePredicateName
  expectedNativeE8RootFamiliesDisjoint :
    LilaE8MissingNativePredicateName
  expectedNativeE8IntegerTwoSparseCompleteness :
    LilaE8MissingNativePredicateName
  expectedNativeE8HalfEvenParityCompleteness :
    LilaE8MissingNativePredicateName
  expectedNativeE8CombinedCompleteness :
    LilaE8MissingNativePredicateName
  expectedNativeE8RootEnumerationCompletePromotion :
    LilaE8MissingNativePredicateName

canonicalLilaE8MissingNativePredicateNames :
  List LilaE8MissingNativePredicateName
canonicalLilaE8MissingNativePredicateNames =
  expectedNativeE8RootEnumerationCompletePromotion
  ∷ []

data LilaE8ExpectedBridgeShape : Set where
  executableIndexedMemberToNativeMember :
    LilaE8ExpectedBridgeShape
  executableIndexedNoDuplicatesToNativeNoDuplicates :
    LilaE8ExpectedBridgeShape
  executableIndexedDisjointToNativeDisjoint :
    LilaE8ExpectedBridgeShape
  integerGeneratorToNativeTwoSparseCompleteness :
    LilaE8ExpectedBridgeShape
  halfGeneratorToNativeEvenParityCompleteness :
    LilaE8ExpectedBridgeShape
  combinedGeneratorToNativeE8Completeness :
    LilaE8ExpectedBridgeShape
  localSemanticCompletenessToUpstreamE8ReceiptPromotion :
    LilaE8ExpectedBridgeShape

canonicalLilaE8ExpectedBridgeShapes :
  List LilaE8ExpectedBridgeShape
canonicalLilaE8ExpectedBridgeShapes =
  localSemanticCompletenessToUpstreamE8ReceiptPromotion
  ∷ []

record LilaE8NativeReflectionBridgeRequest : Set where
  field
    missingNativePredicateNames :
      List LilaE8MissingNativePredicateName

    missingNativePredicateNamesAreCanonical :
      missingNativePredicateNames ≡
      canonicalLilaE8MissingNativePredicateNames

    expectedBridgeShapes :
      List LilaE8ExpectedBridgeShape

    expectedBridgeShapesAreCanonical :
      expectedBridgeShapes ≡ canonicalLilaE8ExpectedBridgeShapes

    expectedNativeRootMemberShape :
      String

    expectedNativeNoDuplicatesShape :
      String

    expectedNativeDisjointShape :
      String

    expectedNativeCompletenessShape :
      String

    requestIsNonPromoting :
      Bool

    requestIsNonPromotingIsTrue :
      requestIsNonPromoting ≡ true

canonicalLilaE8NativeReflectionBridgeRequest :
  LilaE8NativeReflectionBridgeRequest
canonicalLilaE8NativeReflectionBridgeRequest =
  record
    { missingNativePredicateNames =
        canonicalLilaE8MissingNativePredicateNames
    ; missingNativePredicateNamesAreCanonical =
        refl
    ; expectedBridgeShapes =
        canonicalLilaE8ExpectedBridgeShapes
    ; expectedBridgeShapesAreCanonical =
        refl
    ; expectedNativeRootMemberShape =
        "E8RootMember : E8.E8RootCarrier -> E8.E8RootList -> Set, available here as an indexed-image-backed native wrapper"
    ; expectedNativeNoDuplicatesShape =
        "E8RootNoDuplicates : E8.E8RootList -> Set, available here as an indexed-image-backed native wrapper"
    ; expectedNativeDisjointShape =
        "E8RootFamiliesDisjoint : E8.E8RootList -> E8.E8RootList -> Set, available here as an indexed-image-backed native wrapper"
    ; expectedNativeCompletenessShape =
        "Local semantic integer/half/combined completeness is implemented for the finite native root predicates; the remaining gap is promoting that surface to the upstream empty E8RootEnumerationComplete receipt"
    ; requestIsNonPromoting =
        true
    ; requestIsNonPromotingIsTrue =
        refl
    }

canonicalLilaE8NoDuplicatesFirstMissing :
  List LilaE8NoDuplicatesFirstMissing
canonicalLilaE8NoDuplicatesFirstMissing =
  missingUpstreamE8RootEnumerationCompletePromotion
  ∷ []

------------------------------------------------------------------------
-- Minimal native-wrapper layer.
--
-- These are native over E8.E8RootCarrier / E8.E8RootList, but they are
-- deliberately image-backed: a native root/list property is available only
-- when the native root/list is definitionally identified with the image of an
-- indexed root/list and the indexed receipt already exists.  This discharges
-- the Bool-to-Prop bridge for membership, no-duplicates, disjointness, and the
-- generator-completeness surfaces without pretending to prove universal native
-- two-sparse/even-parity classification.

indexedImage :
  E8.E8IndexedRootList →
  E8.E8RootList
indexedImage =
  List.map E8.indexedRootToHalfTritRoot

data E8RootMember :
  E8.E8RootCarrier →
  E8.E8RootList →
  Set where
  memberByIndexedImage :
    {root : E8.E8RootCarrier}
    {roots : E8.E8RootList}
    {indexedRoot : E8.E8IndexedRootCarrier}
    {indexedRoots : E8.E8IndexedRootList} →
    root ≡ E8.indexedRootToHalfTritRoot indexedRoot →
    roots ≡ indexedImage indexedRoots →
    E8.IndexedRootMember indexedRoot indexedRoots →
    E8RootMember root roots

data E8RootNoDuplicates :
  E8.E8RootList →
  Set where
  noDuplicatesByIndexedImage :
    {roots : E8.E8RootList}
    {indexedRoots : E8.E8IndexedRootList} →
    roots ≡ indexedImage indexedRoots →
    E8.IndexedRootNoDuplicates indexedRoots →
    E8RootNoDuplicates roots

data E8RootFamiliesDisjoint :
  E8.E8RootList →
  E8.E8RootList →
  Set where
  disjointByIndexedImage :
    {left right : E8.E8RootList}
    {indexedLeft indexedRight : E8.E8IndexedRootList} →
    left ≡ indexedImage indexedLeft →
    right ≡ indexedImage indexedRight →
    E8.IndexedRootFamiliesDisjoint indexedLeft indexedRight →
    E8RootFamiliesDisjoint left right

integerRootsNoDuplicatesNativeWrapper :
  E8RootNoDuplicates E8.integerRoots
integerRootsNoDuplicatesNativeWrapper =
  noDuplicatesByIndexedImage refl E8.integerIndexedRootsNoDuplicatesBridge

halfRootsNoDuplicatesNativeWrapper :
  E8RootNoDuplicates E8.halfRoots
halfRootsNoDuplicatesNativeWrapper =
  noDuplicatesByIndexedImage refl E8.halfIndexedRootsNoDuplicatesBridge

combinedRootsNoDuplicatesNativeWrapper :
  E8RootNoDuplicates E8.combinedRoots
combinedRootsNoDuplicatesNativeWrapper =
  noDuplicatesByIndexedImage refl E8.combinedIndexedRootsNoDuplicatesBridge

integerHalfRootsDisjointNativeWrapper :
  E8RootFamiliesDisjoint E8.integerRoots E8.halfRoots
integerHalfRootsDisjointNativeWrapper =
  disjointByIndexedImage refl refl E8.integerHalfIndexedRootsDisjointBridge

data E8IntegerTwoSparseGeneratorCompleteness :
  E8.E8RootList →
  Set where
  integerTwoSparseGeneratorCompleteByIndexedImage :
    {roots : E8.E8RootList} →
    roots ≡ indexedImage E8.integerIndexedRoots →
    E8RootNoDuplicates roots →
    E8IntegerTwoSparseGeneratorCompleteness roots

data E8HalfEvenParityGeneratorCompleteness :
  E8.E8RootList →
  Set where
  halfEvenParityGeneratorCompleteByIndexedImage :
    {roots : E8.E8RootList} →
    roots ≡ indexedImage E8.halfIndexedRoots →
    E8.HalfIndexedRootParitySound E8.halfIndexedRoots →
    E8RootNoDuplicates roots →
    E8HalfEvenParityGeneratorCompleteness roots

data E8CombinedGeneratorCompleteness :
  E8.E8RootList →
  Set where
  combinedGeneratorCompleteByIndexedImage :
    {roots : E8.E8RootList} →
    roots ≡ indexedImage E8.combinedIndexedRoots →
    E8RootNoDuplicates roots →
    E8RootFamiliesDisjoint E8.integerRoots E8.halfRoots →
    E8CombinedGeneratorCompleteness roots

------------------------------------------------------------------------
-- Native root-shape predicates.
--
-- The previous layer established that the executable indexed lists can be
-- reflected into native list predicates.  The next useful refinement is to
-- name the native root shapes themselves.  These predicates are still
-- generator-backed: they classify roots produced by the concrete integer and
-- half generators, but they do not yet prove the inverse universal
-- completeness direction for arbitrary native roots.

data E8NativeIntegerTwoSparseRoot :
  E8.E8RootCarrier →
  Set where
  integerTwoSparseRootByGenerator :
    (pair : E8.CoordinatePair8) →
    (leftSign rightSign : E8.E8Sign) →
    {root : E8.E8RootCarrier} →
    root ≡
      E8.indexedRootToHalfTritRoot
        (E8.mkIntegerIndexedRoot pair leftSign rightSign) →
    E8NativeIntegerTwoSparseRoot root

data E8NativeHalfEvenParityRoot :
  E8.E8RootCarrier →
  Set where
  halfEvenParityRootByGenerator :
    (signs : E8.EightVec E8.E8Sign) →
    {root : E8.E8RootCarrier} →
    E8.IndexedRootMember
      (E8.signVectorToHalfIndexedRoot signs)
      E8.halfIndexedRoots →
    root ≡
      E8.indexedRootToHalfTritRoot
        (E8.signVectorToHalfIndexedRoot signs) →
    E8NativeHalfEvenParityRoot root

data E8NativeCombinedRoot :
  E8.E8RootCarrier →
  Set where
  combinedIntegerRoot :
    {root : E8.E8RootCarrier} →
    E8NativeIntegerTwoSparseRoot root →
    E8NativeCombinedRoot root
  combinedHalfRoot :
    {root : E8.E8RootCarrier} →
    E8NativeHalfEvenParityRoot root →
    E8NativeCombinedRoot root

integerGeneratorRootNativeShape :
  (pair : E8.CoordinatePair8) →
  (leftSign rightSign : E8.E8Sign) →
  E8NativeIntegerTwoSparseRoot
    (E8.indexedRootToHalfTritRoot
      (E8.mkIntegerIndexedRoot pair leftSign rightSign))
integerGeneratorRootNativeShape pair leftSign rightSign =
  integerTwoSparseRootByGenerator pair leftSign rightSign refl

halfGeneratorRootNativeShape :
  (signs : E8.EightVec E8.E8Sign) →
  E8.IndexedRootMember
    (E8.signVectorToHalfIndexedRoot signs)
    E8.halfIndexedRoots →
  E8NativeHalfEvenParityRoot
    (E8.indexedRootToHalfTritRoot
      (E8.signVectorToHalfIndexedRoot signs))
halfGeneratorRootNativeShape signs signsEven =
  halfEvenParityRootByGenerator signs signsEven refl

integerGeneratorRootCombinedShape :
  (pair : E8.CoordinatePair8) →
  (leftSign rightSign : E8.E8Sign) →
  E8NativeCombinedRoot
    (E8.indexedRootToHalfTritRoot
      (E8.mkIntegerIndexedRoot pair leftSign rightSign))
integerGeneratorRootCombinedShape pair leftSign rightSign =
  combinedIntegerRoot
    (integerGeneratorRootNativeShape pair leftSign rightSign)

halfGeneratorRootCombinedShape :
  (signs : E8.EightVec E8.E8Sign) →
  E8.IndexedRootMember
    (E8.signVectorToHalfIndexedRoot signs)
    E8.halfIndexedRoots →
  E8NativeCombinedRoot
    (E8.indexedRootToHalfTritRoot
      (E8.signVectorToHalfIndexedRoot signs))
halfGeneratorRootCombinedShape signs signsEven =
  combinedHalfRoot (halfGeneratorRootNativeShape signs signsEven)

data LilaE8NativeCompletenessRefinedFirstMissing : Set where
  missingIntegerTwoSparseClassifierInverse :
    LilaE8NativeCompletenessRefinedFirstMissing
  missingHalfEvenParityClassifierInverse :
    LilaE8NativeCompletenessRefinedFirstMissing
  missingCombinedClassifierCaseSplit :
    LilaE8NativeCompletenessRefinedFirstMissing
  missingIntegerGeneratorMembershipNormalization :
    LilaE8NativeCompletenessRefinedFirstMissing
  missingHalfGeneratorCombinedMembershipNormalization :
    LilaE8NativeCompletenessRefinedFirstMissing
  missingSemanticNativeClassifierPredicatesForArbitraryRoots :
    LilaE8NativeCompletenessRefinedFirstMissing
  missingSemanticFiniteMembershipToGeneratorClassifierEquivalence :
    LilaE8NativeCompletenessRefinedFirstMissing
  missingNativeFiniteMembershipWitnessToGeneratorClassifierCase :
    LilaE8NativeCompletenessRefinedFirstMissing

canonicalLilaE8NativeCompletenessRefinedFirstMissing :
  List LilaE8NativeCompletenessRefinedFirstMissing
canonicalLilaE8NativeCompletenessRefinedFirstMissing =
  missingIntegerGeneratorMembershipNormalization
  ∷ missingHalfGeneratorCombinedMembershipNormalization
  ∷ missingSemanticFiniteMembershipToGeneratorClassifierEquivalence
  ∷ []

------------------------------------------------------------------------
-- Generator-backed classifier inverses.
--
-- The current native shape predicates are intentionally generator-backed:
-- their constructors carry the coordinate pair/sign vector that generated
-- the native root.  That is enough to invert those constructors into indexed
-- membership in a symbolic generator-family inverse.  It is not yet universal
-- native classification for arbitrary roots; the remaining gaps are
-- normalizing symbolic generator membership into the executable lists, and
-- then proving semantic two-sparse / even-parity predicates imply one of
-- these generator constructors.

data E8IntegerTwoSparseClassifierInverse :
  E8.E8RootCarrier →
  Set where
  integerClassifierInverseByGenerator :
    (pair : E8.CoordinatePair8) →
    (leftSign rightSign : E8.E8Sign) →
    {root : E8.E8RootCarrier} →
    root ≡
      E8.indexedRootToHalfTritRoot
        (E8.mkIntegerIndexedRoot pair leftSign rightSign) →
    E8IntegerTwoSparseClassifierInverse root

data E8HalfEvenParityClassifierInverse :
  E8.E8RootCarrier →
  Set where
  halfClassifierInverseByGenerator :
    (signs : E8.EightVec E8.E8Sign) →
    {root : E8.E8RootCarrier} →
    E8.IndexedRootMember
      (E8.signVectorToHalfIndexedRoot signs)
      E8.halfIndexedRoots →
    root ≡
      E8.indexedRootToHalfTritRoot
        (E8.signVectorToHalfIndexedRoot signs) →
    E8HalfEvenParityClassifierInverse root

data E8CombinedClassifierCase :
  E8.E8RootCarrier →
  Set where
  combinedClassifierIntegerCase :
    {root : E8.E8RootCarrier} →
    E8IntegerTwoSparseClassifierInverse root →
    E8CombinedClassifierCase root
  combinedClassifierHalfCase :
    {root : E8.E8RootCarrier} →
    E8HalfEvenParityClassifierInverse root →
    E8CombinedClassifierCase root

integerTwoSparseClassifierInverse :
  {root : E8.E8RootCarrier} →
  E8NativeIntegerTwoSparseRoot root →
  E8IntegerTwoSparseClassifierInverse root
integerTwoSparseClassifierInverse
  (integerTwoSparseRootByGenerator pair leftSign rightSign rootIsGenerator) =
  integerClassifierInverseByGenerator
    pair
    leftSign
    rightSign
    rootIsGenerator

halfEvenParityClassifierInverse :
  {root : E8.E8RootCarrier} →
  E8NativeHalfEvenParityRoot root →
  E8HalfEvenParityClassifierInverse root
halfEvenParityClassifierInverse
  (halfEvenParityRootByGenerator signs signsEven rootIsGenerator) =
  halfClassifierInverseByGenerator
    signs
    signsEven
    rootIsGenerator

combinedClassifierCaseSplit :
  {root : E8.E8RootCarrier} →
  E8NativeCombinedRoot root →
  E8CombinedClassifierCase root
combinedClassifierCaseSplit
  (combinedIntegerRoot integerRoot) =
  combinedClassifierIntegerCase
    (integerTwoSparseClassifierInverse integerRoot)
combinedClassifierCaseSplit
  (combinedHalfRoot halfRoot) =
  combinedClassifierHalfCase
    (halfEvenParityClassifierInverse halfRoot)

------------------------------------------------------------------------
-- Finite generator membership normalization.
--
-- The integer generator side can now be normalized all the way into the
-- executable indexed list.  This is the first finite case split needed by
-- the native-completeness lane: every concrete pair/sign generator reduces
-- to membership in E8.integerIndexedRoots by computation.

integerGeneratorIndexedMembershipCheck :
  (pair : E8.CoordinatePair8) →
  (leftSign rightSign : E8.E8Sign) →
  E8.memberIndexedRoot
    (E8.mkIntegerIndexedRoot pair leftSign rightSign)
    E8.integerIndexedRoots
  ≡
  true
integerGeneratorIndexedMembershipCheck E8.pair01 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair01 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair01 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair01 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair02 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair02 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair02 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair02 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair03 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair03 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair03 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair03 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair04 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair04 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair04 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair04 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair05 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair05 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair05 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair05 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair06 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair06 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair06 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair06 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair07 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair07 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair07 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair07 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair12 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair12 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair12 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair12 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair13 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair13 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair13 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair13 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair14 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair14 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair14 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair14 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair15 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair15 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair15 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair15 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair16 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair16 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair16 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair16 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair17 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair17 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair17 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair17 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair23 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair23 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair23 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair23 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair24 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair24 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair24 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair24 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair25 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair25 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair25 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair25 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair26 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair26 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair26 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair26 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair27 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair27 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair27 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair27 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair34 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair34 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair34 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair34 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair35 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair35 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair35 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair35 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair36 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair36 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair36 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair36 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair37 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair37 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair37 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair37 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair45 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair45 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair45 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair45 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair46 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair46 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair46 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair46 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair47 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair47 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair47 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair47 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair56 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair56 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair56 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair56 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair57 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair57 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair57 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair57 E8.positiveSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair67 E8.negativeSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair67 E8.negativeSign E8.positiveSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair67 E8.positiveSign E8.negativeSign =
  refl
integerGeneratorIndexedMembershipCheck E8.pair67 E8.positiveSign E8.positiveSign =
  refl

integerGeneratorIndexedMembershipNormalization :
  (pair : E8.CoordinatePair8) →
  (leftSign rightSign : E8.E8Sign) →
  E8.IndexedRootMember
    (E8.mkIntegerIndexedRoot pair leftSign rightSign)
    E8.integerIndexedRoots
integerGeneratorIndexedMembershipNormalization pair leftSign rightSign =
  E8.memberByExecutableCheck
    (integerGeneratorIndexedMembershipCheck pair leftSign rightSign)

integerGeneratorNativeMembershipNormalization :
  (pair : E8.CoordinatePair8) →
  (leftSign rightSign : E8.E8Sign) →
  E8RootMember
    (E8.indexedRootToHalfTritRoot
      (E8.mkIntegerIndexedRoot pair leftSign rightSign))
    E8.integerRoots
integerGeneratorNativeMembershipNormalization pair leftSign rightSign =
  memberByIndexedImage
    refl
    refl
    (integerGeneratorIndexedMembershipNormalization pair leftSign rightSign)

integerClassifierInverseNormalizesToMembership :
  {root : E8.E8RootCarrier} →
  E8IntegerTwoSparseClassifierInverse root →
  E8RootMember root E8.integerRoots
integerClassifierInverseNormalizesToMembership
  (integerClassifierInverseByGenerator
    pair
    leftSign
    rightSign
    refl) =
  integerGeneratorNativeMembershipNormalization pair leftSign rightSign

data E8IntegerGeneratorMembershipNormalization :
  Set where
  integerGeneratorMembershipNormalizationByFiniteCaseSplit :
    ((pair : E8.CoordinatePair8) →
     (leftSign rightSign : E8.E8Sign) →
     E8RootMember
       (E8.indexedRootToHalfTritRoot
         (E8.mkIntegerIndexedRoot pair leftSign rightSign))
       E8.integerRoots) →
    E8IntegerGeneratorMembershipNormalization

integerGeneratorMembershipNormalization :
  E8IntegerGeneratorMembershipNormalization
integerGeneratorMembershipNormalization =
  integerGeneratorMembershipNormalizationByFiniteCaseSplit
    integerGeneratorNativeMembershipNormalization

indexedMemberToExecutableCheck :
  {root : E8.E8IndexedRootCarrier} →
  {roots : E8.E8IndexedRootList} →
  E8.IndexedRootMember root roots →
  E8.memberIndexedRoot root roots ≡ true
indexedMemberToExecutableCheck
  (E8.memberByExecutableCheck membershipCheck) =
  membershipCheck

memberIndexedRootAppendLeft :
  (root : E8.E8IndexedRootCarrier) →
  (left right : E8.E8IndexedRootList) →
  E8.memberIndexedRoot root left ≡ true →
  E8.memberIndexedRoot root (left List.++ right) ≡ true
memberIndexedRootAppendLeft root [] right ()
memberIndexedRootAppendLeft root (candidate ∷ left) right membershipCheck
  with E8.decEqIndexedRoot root candidate
... | yes _ =
  refl
... | no _ =
  memberIndexedRootAppendLeft root left right membershipCheck

memberIndexedRootAppendRight :
  (root : E8.E8IndexedRootCarrier) →
  (left right : E8.E8IndexedRootList) →
  E8.memberIndexedRoot root right ≡ true →
  E8.memberIndexedRoot root (left List.++ right) ≡ true
memberIndexedRootAppendRight root [] right membershipCheck =
  membershipCheck
memberIndexedRootAppendRight root (candidate ∷ left) right membershipCheck
  with E8.decEqIndexedRoot root candidate
... | yes _ =
  refl
... | no _ =
  memberIndexedRootAppendRight root left right membershipCheck

integerGeneratorCombinedIndexedMembershipNormalization :
  (pair : E8.CoordinatePair8) →
  (leftSign rightSign : E8.E8Sign) →
  E8.IndexedRootMember
    (E8.mkIntegerIndexedRoot pair leftSign rightSign)
    E8.combinedIndexedRoots
integerGeneratorCombinedIndexedMembershipNormalization pair leftSign rightSign =
  E8.memberByExecutableCheck
    (memberIndexedRootAppendLeft
      (E8.mkIntegerIndexedRoot pair leftSign rightSign)
      E8.integerIndexedRoots
      E8.halfIndexedRoots
      (integerGeneratorIndexedMembershipCheck pair leftSign rightSign))

halfGeneratorIndexedMembershipNormalization :
  (signs : E8.EightVec E8.E8Sign) →
  E8.IndexedRootMember
    (E8.signVectorToHalfIndexedRoot signs)
    E8.halfIndexedRoots →
  E8.IndexedRootMember
    (E8.signVectorToHalfIndexedRoot signs)
    E8.halfIndexedRoots
halfGeneratorIndexedMembershipNormalization signs signsEven =
  signsEven

halfGeneratorNativeMembershipNormalization :
  (signs : E8.EightVec E8.E8Sign) →
  E8.IndexedRootMember
    (E8.signVectorToHalfIndexedRoot signs)
    E8.halfIndexedRoots →
  E8RootMember
    (E8.indexedRootToHalfTritRoot
      (E8.signVectorToHalfIndexedRoot signs))
    E8.halfRoots
halfGeneratorNativeMembershipNormalization signs signsEven =
  memberByIndexedImage
    refl
    refl
    (halfGeneratorIndexedMembershipNormalization signs signsEven)

halfGeneratorCombinedIndexedMembershipNormalization :
  (signs : E8.EightVec E8.E8Sign) →
  E8.IndexedRootMember
    (E8.signVectorToHalfIndexedRoot signs)
    E8.halfIndexedRoots →
  E8.IndexedRootMember
    (E8.signVectorToHalfIndexedRoot signs)
    E8.combinedIndexedRoots
halfGeneratorCombinedIndexedMembershipNormalization signs signsEven =
  E8.memberByExecutableCheck
    (memberIndexedRootAppendRight
      (E8.signVectorToHalfIndexedRoot signs)
      E8.integerIndexedRoots
      E8.halfIndexedRoots
      (indexedMemberToExecutableCheck signsEven))

integerGeneratorCombinedNativeMembershipNormalization :
  (pair : E8.CoordinatePair8) →
  (leftSign rightSign : E8.E8Sign) →
  E8RootMember
    (E8.indexedRootToHalfTritRoot
      (E8.mkIntegerIndexedRoot pair leftSign rightSign))
    E8.combinedRoots
integerGeneratorCombinedNativeMembershipNormalization pair leftSign rightSign =
  memberByIndexedImage
    refl
    refl
    (integerGeneratorCombinedIndexedMembershipNormalization
      pair
      leftSign
      rightSign)

halfGeneratorCombinedNativeMembershipNormalization :
  (signs : E8.EightVec E8.E8Sign) →
  E8.IndexedRootMember
    (E8.signVectorToHalfIndexedRoot signs)
    E8.halfIndexedRoots →
  E8RootMember
    (E8.indexedRootToHalfTritRoot
      (E8.signVectorToHalfIndexedRoot signs))
    E8.combinedRoots
halfGeneratorCombinedNativeMembershipNormalization signs signsEven =
  memberByIndexedImage
    refl
    refl
    (halfGeneratorCombinedIndexedMembershipNormalization signs signsEven)

combinedClassifierCaseNormalizesToMembership :
  {root : E8.E8RootCarrier} →
  E8CombinedClassifierCase root →
  E8RootMember root E8.combinedRoots
combinedClassifierCaseNormalizesToMembership
  (combinedClassifierIntegerCase
    (integerClassifierInverseByGenerator
      pair
      leftSign
      rightSign
      refl)) =
  integerGeneratorCombinedNativeMembershipNormalization
    pair
    leftSign
    rightSign
combinedClassifierCaseNormalizesToMembership
  (combinedClassifierHalfCase
    (halfClassifierInverseByGenerator
      signs
      signsEven
      refl)) =
  halfGeneratorCombinedNativeMembershipNormalization
    signs
    signsEven

data E8HalfGeneratorCombinedMembershipNormalization :
  Set where
  halfGeneratorCombinedMembershipNormalizationByAppendRight :
    ((signs : E8.EightVec E8.E8Sign) →
     E8.IndexedRootMember
       (E8.signVectorToHalfIndexedRoot signs)
       E8.halfIndexedRoots →
     E8RootMember
       (E8.indexedRootToHalfTritRoot
         (E8.signVectorToHalfIndexedRoot signs))
       E8.combinedRoots) →
    E8HalfGeneratorCombinedMembershipNormalization

halfGeneratorCombinedMembershipNormalization :
  E8HalfGeneratorCombinedMembershipNormalization
halfGeneratorCombinedMembershipNormalization =
  halfGeneratorCombinedMembershipNormalizationByAppendRight
    halfGeneratorCombinedNativeMembershipNormalization

data E8CombinedClassifierMembershipNormalization :
  Set where
  combinedClassifierMembershipNormalizationByCases :
    ({root : E8.E8RootCarrier} →
     E8CombinedClassifierCase root →
     E8RootMember root E8.combinedRoots) →
    E8CombinedClassifierMembershipNormalization

combinedClassifierMembershipNormalization :
  E8CombinedClassifierMembershipNormalization
combinedClassifierMembershipNormalization =
  combinedClassifierMembershipNormalizationByCases
    combinedClassifierCaseNormalizesToMembership

------------------------------------------------------------------------
-- Arbitrary-root semantic classifier predicates.
--
-- The generator-backed predicates above classify roots when the generator is
-- already known.  For arbitrary native roots, the precise local semantic
-- predicate available in this file is finite membership in the concrete
-- native integer/half/combined lists.  This gives total predicates over
-- E8.E8RootCarrier without promoting them to generator inverses.

decEqHalfTrit :
  (x y : HT.HalfTrit) →
  Relation.Nullary.Dec (x ≡ y)
decEqHalfTrit HT.negOne HT.negOne =
  yes refl
decEqHalfTrit HT.negOne HT.negHalf =
  no (λ ())
decEqHalfTrit HT.negOne HT.zero =
  no (λ ())
decEqHalfTrit HT.negOne HT.posHalf =
  no (λ ())
decEqHalfTrit HT.negOne HT.posOne =
  no (λ ())
decEqHalfTrit HT.negHalf HT.negOne =
  no (λ ())
decEqHalfTrit HT.negHalf HT.negHalf =
  yes refl
decEqHalfTrit HT.negHalf HT.zero =
  no (λ ())
decEqHalfTrit HT.negHalf HT.posHalf =
  no (λ ())
decEqHalfTrit HT.negHalf HT.posOne =
  no (λ ())
decEqHalfTrit HT.zero HT.negOne =
  no (λ ())
decEqHalfTrit HT.zero HT.negHalf =
  no (λ ())
decEqHalfTrit HT.zero HT.zero =
  yes refl
decEqHalfTrit HT.zero HT.posHalf =
  no (λ ())
decEqHalfTrit HT.zero HT.posOne =
  no (λ ())
decEqHalfTrit HT.posHalf HT.negOne =
  no (λ ())
decEqHalfTrit HT.posHalf HT.negHalf =
  no (λ ())
decEqHalfTrit HT.posHalf HT.zero =
  no (λ ())
decEqHalfTrit HT.posHalf HT.posHalf =
  yes refl
decEqHalfTrit HT.posHalf HT.posOne =
  no (λ ())
decEqHalfTrit HT.posOne HT.negOne =
  no (λ ())
decEqHalfTrit HT.posOne HT.negHalf =
  no (λ ())
decEqHalfTrit HT.posOne HT.zero =
  no (λ ())
decEqHalfTrit HT.posOne HT.posHalf =
  no (λ ())
decEqHalfTrit HT.posOne HT.posOne =
  yes refl

decEqNativeRoot :
  {n : Nat} →
  (x y : Vec HT.HalfTrit n) →
  Relation.Nullary.Dec (x ≡ y)
decEqNativeRoot Vec.[] Vec.[] =
  yes refl
decEqNativeRoot (x Vec.∷ xs) (y Vec.∷ ys)
  with decEqHalfTrit x y
... | no neq =
  no (λ eq → neq (cong Vec.head eq))
... | yes refl
  with decEqNativeRoot xs ys
... | no neq =
  no (λ eq → neq (cong Vec.tail eq))
... | yes refl =
  yes refl

memberNativeRoot :
  E8.E8RootCarrier →
  E8.E8RootList →
  Bool
memberNativeRoot root [] =
  false
memberNativeRoot root (candidate ∷ roots)
  with decEqNativeRoot root candidate
... | yes _ =
  true
... | no _ =
  memberNativeRoot root roots

data E8NativeFiniteRootMember :
  E8.E8RootCarrier →
  E8.E8RootList →
  Set where
  nativeMemberByExecutableCheck :
    {root : E8.E8RootCarrier}
    {roots : E8.E8RootList} →
    memberNativeRoot root roots ≡ true →
    E8NativeFiniteRootMember root roots

nativeBoolMembershipToFiniteRootMember :
  {root : E8.E8RootCarrier} →
  {roots : E8.E8RootList} →
  memberNativeRoot root roots ≡ true →
  E8NativeFiniteRootMember root roots
nativeBoolMembershipToFiniteRootMember =
  nativeMemberByExecutableCheck

nativeFiniteRootMemberToBoolMembership :
  {root : E8.E8RootCarrier} →
  {roots : E8.E8RootList} →
  E8NativeFiniteRootMember root roots →
  memberNativeRoot root roots ≡ true
nativeFiniteRootMemberToBoolMembership
  (nativeMemberByExecutableCheck membershipCheck) =
  membershipCheck

indexedBoolMembershipToIndexedRootMember :
  {root : E8.E8IndexedRootCarrier} →
  {roots : E8.E8IndexedRootList} →
  E8.memberIndexedRoot root roots ≡ true →
  E8.IndexedRootMember root roots
indexedBoolMembershipToIndexedRootMember =
  E8.memberByExecutableCheck

record E8IndexedImageLookup
  (root : E8.E8RootCarrier)
  (indexedRoots : E8.E8IndexedRootList) :
  Set where
  constructor indexedImageLookup
  field
    indexedRoot :
      E8.E8IndexedRootCarrier

    rootIsIndexedImage :
      root ≡ E8.indexedRootToHalfTritRoot indexedRoot

    indexedMembership :
      E8.IndexedRootMember indexedRoot indexedRoots

indexedBoolMemberHead :
  (root : E8.E8IndexedRootCarrier) →
  (roots : E8.E8IndexedRootList) →
  E8.memberIndexedRoot root (root ∷ roots) ≡ true
indexedBoolMemberHead root roots
  with E8.decEqIndexedRoot root root
... | yes _ =
  refl
... | no root≢root =
  ⊥-elim (root≢root refl)

indexedBoolMemberConsFromTail :
  (root head : E8.E8IndexedRootCarrier) →
  (tail : E8.E8IndexedRootList) →
  E8.memberIndexedRoot root tail ≡ true →
  E8.memberIndexedRoot root (head ∷ tail) ≡ true
indexedBoolMemberConsFromTail root head tail tailMembership
  with E8.decEqIndexedRoot root head
... | yes _ =
  refl
... | no _ =
  tailMembership

indexedMemberConsFromTail :
  {root head : E8.E8IndexedRootCarrier} →
  {tail : E8.E8IndexedRootList} →
  E8.IndexedRootMember root tail →
  E8.IndexedRootMember root (head ∷ tail)
indexedMemberConsFromTail {root} {head} {tail}
  (E8.memberByExecutableCheck tailMembership) =
  E8.memberByExecutableCheck
    (indexedBoolMemberConsFromTail root head tail tailMembership)

indexedImageBoolMembershipLookup :
  {root : E8.E8RootCarrier} →
  (indexedRoots : E8.E8IndexedRootList) →
  memberNativeRoot root (indexedImage indexedRoots) ≡ true →
  E8IndexedImageLookup root indexedRoots
indexedImageBoolMembershipLookup [] ()
indexedImageBoolMembershipLookup {root} (indexedRoot ∷ indexedRoots) membershipCheck
  with decEqNativeRoot root (E8.indexedRootToHalfTritRoot indexedRoot)
... | yes rootIsIndexedImage =
  indexedImageLookup
    indexedRoot
    rootIsIndexedImage
    (E8.memberByExecutableCheck
      (indexedBoolMemberHead indexedRoot indexedRoots))
... | no _
  with indexedImageBoolMembershipLookup {root = root} indexedRoots membershipCheck
... | indexedImageLookup foundRoot rootIsIndexedImage indexedMembership =
  indexedImageLookup
    foundRoot
    rootIsIndexedImage
    (indexedMemberConsFromTail indexedMembership)

indexedImageLookupToNativeRootMember :
  {root : E8.E8RootCarrier} →
  {indexedRoots : E8.E8IndexedRootList} →
  E8IndexedImageLookup root indexedRoots →
  E8RootMember root (indexedImage indexedRoots)
indexedImageLookupToNativeRootMember
  (indexedImageLookup indexedRoot rootIsIndexedImage indexedMembership) =
  memberByIndexedImage
    rootIsIndexedImage
    refl
    indexedMembership

integerNativeBoolMembershipToIndexedImageLookup :
  {root : E8.E8RootCarrier} →
  memberNativeRoot root E8.integerRoots ≡ true →
  E8IndexedImageLookup root E8.integerIndexedRoots
integerNativeBoolMembershipToIndexedImageLookup =
  indexedImageBoolMembershipLookup E8.integerIndexedRoots

halfNativeBoolMembershipToIndexedImageLookup :
  {root : E8.E8RootCarrier} →
  memberNativeRoot root E8.halfRoots ≡ true →
  E8IndexedImageLookup root E8.halfIndexedRoots
halfNativeBoolMembershipToIndexedImageLookup =
  indexedImageBoolMembershipLookup E8.halfIndexedRoots

combinedNativeBoolMembershipToIndexedImageLookup :
  {root : E8.E8RootCarrier} →
  memberNativeRoot root E8.combinedRoots ≡ true →
  E8IndexedImageLookup root E8.combinedIndexedRoots
combinedNativeBoolMembershipToIndexedImageLookup =
  indexedImageBoolMembershipLookup E8.combinedIndexedRoots

E8SemanticNativeIntegerTwoSparseRoot :
  E8.E8RootCarrier →
  Set
E8SemanticNativeIntegerTwoSparseRoot root =
  E8NativeFiniteRootMember root E8.integerRoots

E8SemanticNativeHalfEvenParityRoot :
  E8.E8RootCarrier →
  Set
E8SemanticNativeHalfEvenParityRoot root =
  E8NativeFiniteRootMember root E8.halfRoots

E8SemanticNativeCombinedRoot :
  E8.E8RootCarrier →
  Set
E8SemanticNativeCombinedRoot root =
  E8NativeFiniteRootMember root E8.combinedRoots

data E8SemanticNativeClassifierPredicatesForArbitraryRoots :
  Set where
  semanticNativeClassifiersByFiniteNativeMembership :
    E8SemanticNativeClassifierPredicatesForArbitraryRoots

semanticNativeClassifierPredicatesForArbitraryRoots :
  E8SemanticNativeClassifierPredicatesForArbitraryRoots
semanticNativeClassifierPredicatesForArbitraryRoots =
  semanticNativeClassifiersByFiniteNativeMembership

canonicalLilaE8NativeCompletenessRefinedFirstMissingAfterIntegerNormalization :
  List LilaE8NativeCompletenessRefinedFirstMissing
canonicalLilaE8NativeCompletenessRefinedFirstMissingAfterIntegerNormalization =
  missingHalfGeneratorCombinedMembershipNormalization
  ∷ missingSemanticFiniteMembershipToGeneratorClassifierEquivalence
  ∷ []

canonicalLilaE8NativeCompletenessRefinedFirstMissingAfterHalfCombinedNormalization :
  List LilaE8NativeCompletenessRefinedFirstMissing
canonicalLilaE8NativeCompletenessRefinedFirstMissingAfterHalfCombinedNormalization =
  []

data E8SemanticFiniteMembershipClassifierInverseObligation : Set where
  integerFiniteMembershipToPairSignClassifier :
    E8SemanticFiniteMembershipClassifierInverseObligation
  halfFiniteMembershipToEvenSignVectorClassifier :
    E8SemanticFiniteMembershipClassifierInverseObligation
  combinedFiniteMembershipToIntegerOrHalfClassifierCase :
    E8SemanticFiniteMembershipClassifierInverseObligation

canonicalE8SemanticFiniteMembershipClassifierInverseObligations :
  List E8SemanticFiniteMembershipClassifierInverseObligation
canonicalE8SemanticFiniteMembershipClassifierInverseObligations =
  integerFiniteMembershipToPairSignClassifier
  ∷ halfFiniteMembershipToEvenSignVectorClassifier
  ∷ combinedFiniteMembershipToIntegerOrHalfClassifierCase
  ∷ []

record E8IntegerFiniteMembershipGeneratorIndexedWitness
  (root : E8.E8RootCarrier) :
  Set where
  constructor integerFiniteMembershipGeneratorIndexedWitness
  field
    pair :
      E8.CoordinatePair8

    leftSign :
      E8.E8Sign

    rightSign :
      E8.E8Sign

    rootIsGeneratorImage :
      root ≡
      E8.indexedRootToHalfTritRoot
        (E8.mkIntegerIndexedRoot pair leftSign rightSign)

    indexedMembership :
      E8.IndexedRootMember
        (E8.mkIntegerIndexedRoot pair leftSign rightSign)
        E8.integerIndexedRoots

integerGeneratorFiniteMembershipWitness :
  (pair : E8.CoordinatePair8) →
  (leftSign rightSign : E8.E8Sign) →
  E8IntegerFiniteMembershipGeneratorIndexedWitness
    (E8.indexedRootToHalfTritRoot
      (E8.mkIntegerIndexedRoot pair leftSign rightSign))
integerGeneratorFiniteMembershipWitness pair leftSign rightSign =
  integerFiniteMembershipGeneratorIndexedWitness
    pair
    leftSign
    rightSign
    refl
    (integerGeneratorIndexedMembershipNormalization pair leftSign rightSign)

record E8IntegerGeneratorMembershipWitnessTable : Set where
  field
    rowWitness :
      (pair : E8.CoordinatePair8) →
      (leftSign rightSign : E8.E8Sign) →
      E8IntegerFiniteMembershipGeneratorIndexedWitness
        (E8.indexedRootToHalfTritRoot
          (E8.mkIntegerIndexedRoot pair leftSign rightSign))

    rowNativeMembership :
      (pair : E8.CoordinatePair8) →
      (leftSign rightSign : E8.E8Sign) →
      E8RootMember
        (E8.indexedRootToHalfTritRoot
          (E8.mkIntegerIndexedRoot pair leftSign rightSign))
        E8.integerRoots

    rowClassifier :
      (pair : E8.CoordinatePair8) →
      (leftSign rightSign : E8.E8Sign) →
      E8IntegerTwoSparseClassifierInverse
        (E8.indexedRootToHalfTritRoot
          (E8.mkIntegerIndexedRoot pair leftSign rightSign))

canonicalE8IntegerGeneratorMembershipWitnessTable :
  E8IntegerGeneratorMembershipWitnessTable
canonicalE8IntegerGeneratorMembershipWitnessTable =
  record
    { rowWitness =
        integerGeneratorFiniteMembershipWitness
    ; rowNativeMembership =
        integerGeneratorNativeMembershipNormalization
    ; rowClassifier =
        λ pair leftSign rightSign →
          integerClassifierInverseByGenerator
            pair
            leftSign
            rightSign
            refl
    }

record E8HalfFiniteMembershipGeneratorIndexedWitness
  (root : E8.E8RootCarrier) :
  Set where
  constructor halfFiniteMembershipGeneratorIndexedWitness
  field
    signs :
      E8.EightVec E8.E8Sign

    rootIsGeneratorImage :
      root ≡
      E8.indexedRootToHalfTritRoot
        (E8.signVectorToHalfIndexedRoot signs)

    indexedMembership :
      E8.IndexedRootMember
        (E8.signVectorToHalfIndexedRoot signs)
        E8.halfIndexedRoots

data E8CombinedFiniteMembershipGeneratorIndexedWitness
  (root : E8.E8RootCarrier) :
  Set where
  combinedFiniteMembershipIntegerWitness :
    E8IntegerFiniteMembershipGeneratorIndexedWitness root →
    E8CombinedFiniteMembershipGeneratorIndexedWitness root

  combinedFiniteMembershipHalfWitness :
    E8HalfFiniteMembershipGeneratorIndexedWitness root →
    E8CombinedFiniteMembershipGeneratorIndexedWitness root

record E8NativeFiniteMembershipWitnessToGeneratorClassifierPrimitive :
  Set where
  field
    integerFiniteMembershipCarriesGeneratorIndex :
      {root : E8.E8RootCarrier} →
      E8SemanticNativeIntegerTwoSparseRoot root →
      E8IntegerFiniteMembershipGeneratorIndexedWitness root

    halfFiniteMembershipCarriesGeneratorIndex :
      {root : E8.E8RootCarrier} →
      E8SemanticNativeHalfEvenParityRoot root →
      E8HalfFiniteMembershipGeneratorIndexedWitness root

    combinedFiniteMembershipCarriesGeneratorIndex :
      {root : E8.E8RootCarrier} →
      E8SemanticNativeCombinedRoot root →
      E8CombinedFiniteMembershipGeneratorIndexedWitness root

data E8FiniteMembershipWitnessTableField : Set where
  finiteMembershipWitnessRootField :
    E8FiniteMembershipWitnessTableField
  finiteMembershipWitnessFamilyField :
    E8FiniteMembershipWitnessTableField
  finiteMembershipWitnessNativeMembershipCheckField :
    E8FiniteMembershipWitnessTableField
  finiteMembershipWitnessGeneratorIndexField :
    E8FiniteMembershipWitnessTableField
  finiteMembershipWitnessIndexedImageEqualityField :
    E8FiniteMembershipWitnessTableField
  finiteMembershipWitnessIndexedMembershipField :
    E8FiniteMembershipWitnessTableField
  finiteMembershipWitnessProofField :
    E8FiniteMembershipWitnessTableField

canonicalE8FiniteMembershipWitnessTableFields :
  List E8FiniteMembershipWitnessTableField
canonicalE8FiniteMembershipWitnessTableFields =
  finiteMembershipWitnessRootField
  ∷ finiteMembershipWitnessFamilyField
  ∷ finiteMembershipWitnessNativeMembershipCheckField
  ∷ finiteMembershipWitnessGeneratorIndexField
  ∷ finiteMembershipWitnessIndexedImageEqualityField
  ∷ finiteMembershipWitnessIndexedMembershipField
  ∷ finiteMembershipWitnessProofField
  ∷ []

record E8FiniteMembershipWitnessTableRequest : Set where
  field
    requestedTableFields :
      List E8FiniteMembershipWitnessTableField

    requestedTableFieldsAreCanonical :
      requestedTableFields ≡
      canonicalE8FiniteMembershipWitnessTableFields

    rootFieldShape :
      String

    familyFieldShape :
      String

    nativeMembershipCheckFieldShape :
      String

    generatorIndexFieldShape :
      String

    indexedImageEqualityFieldShape :
      String

    indexedMembershipFieldShape :
      String

    proofFieldShape :
      String

    consumerPrimitiveShape :
      String

    requestIsNonPromoting :
      Bool

    requestIsNonPromotingIsTrue :
      requestIsNonPromoting ≡ true

canonicalE8FiniteMembershipWitnessTableRequest :
  E8FiniteMembershipWitnessTableRequest
canonicalE8FiniteMembershipWitnessTableRequest =
  record
    { requestedTableFields =
        canonicalE8FiniteMembershipWitnessTableFields
    ; requestedTableFieldsAreCanonical =
        refl
    ; rootFieldShape =
        "root : E8.E8RootCarrier, matching the semantic finite native-list membership row"
    ; familyFieldShape =
        "family : integer, half, or combined; combined rows must carry the integer/half source case"
    ; nativeMembershipCheckFieldShape =
        "nativeMembershipCheck : memberNativeRoot root familyRoots == true; integer generator rows now carry witnesses, but arbitrary native-list membership still needs proof-relevant inversion"
    ; generatorIndexFieldShape =
        "generator index : integer pair/signs, half even sign vector, or combined integer/half case"
    ; indexedImageEqualityFieldShape =
        "rootIsGeneratorImage : root == indexedRootToHalfTritRoot(generator-indexed root)"
    ; indexedMembershipFieldShape =
        "indexedMembership : generator-indexed root is a member of the corresponding integer, half, or combined indexed list"
    ; proofFieldShape =
        "proof : proof-relevant lookup from native finite membership to the generator-indexed witness, not just a Bool membership check"
    ; consumerPrimitiveShape =
        "consumer primitive supplies total integer, half, and combined finite-membership-to-generator-witness functions; only integer generator-indexed rows are available here"
    ; requestIsNonPromoting =
        true
    ; requestIsNonPromotingIsTrue =
        refl
    }

integerFiniteMembershipWitnessToClassifier :
  {root : E8.E8RootCarrier} →
  E8IntegerFiniteMembershipGeneratorIndexedWitness root →
  E8IntegerTwoSparseClassifierInverse root
integerFiniteMembershipWitnessToClassifier
  (integerFiniteMembershipGeneratorIndexedWitness
    pair
    leftSign
    rightSign
    rootIsGeneratorImage
    indexedMembership) =
  integerClassifierInverseByGenerator
    pair
    leftSign
    rightSign
    rootIsGeneratorImage

halfFiniteMembershipWitnessToClassifier :
  {root : E8.E8RootCarrier} →
  E8HalfFiniteMembershipGeneratorIndexedWitness root →
  E8HalfEvenParityClassifierInverse root
halfFiniteMembershipWitnessToClassifier
  (halfFiniteMembershipGeneratorIndexedWitness
    signs
    rootIsGeneratorImage
    indexedMembership) =
  halfClassifierInverseByGenerator
    signs
    indexedMembership
    rootIsGeneratorImage

combinedFiniteMembershipWitnessToClassifierCase :
  {root : E8.E8RootCarrier} →
  E8CombinedFiniteMembershipGeneratorIndexedWitness root →
  E8CombinedClassifierCase root
combinedFiniteMembershipWitnessToClassifierCase
  (combinedFiniteMembershipIntegerWitness witness) =
  combinedClassifierIntegerCase
    (integerFiniteMembershipWitnessToClassifier witness)
combinedFiniteMembershipWitnessToClassifierCase
  (combinedFiniteMembershipHalfWitness witness) =
  combinedClassifierHalfCase
    (halfFiniteMembershipWitnessToClassifier witness)

record E8IntegerIndexedRootGeneratorShape
  (indexedRoot : E8.E8IndexedRootCarrier) :
  Set where
  constructor integerIndexedRootGeneratorShape
  field
    pair :
      E8.CoordinatePair8

    leftSign :
      E8.E8Sign

    rightSign :
      E8.E8Sign

    indexedRootIsGenerator :
      indexedRoot ≡
      E8.mkIntegerIndexedRoot pair leftSign rightSign

record E8HalfIndexedRootGeneratorShape
  (indexedRoot : E8.E8IndexedRootCarrier) :
  Set where
  constructor halfIndexedRootGeneratorShape
  field
    signs :
      E8.EightVec E8.E8Sign

    indexedRootIsGenerator :
      indexedRoot ≡
      E8.signVectorToHalfIndexedRoot signs

data E8CombinedIndexedRootGeneratorShape
  (indexedRoot : E8.E8IndexedRootCarrier) :
  Set where
  combinedIndexedRootIntegerShape :
    E8IntegerIndexedRootGeneratorShape indexedRoot →
    E8.IndexedRootMember indexedRoot E8.integerIndexedRoots →
    E8CombinedIndexedRootGeneratorShape indexedRoot

  combinedIndexedRootHalfShape :
    E8HalfIndexedRootGeneratorShape indexedRoot →
    E8.IndexedRootMember indexedRoot E8.halfIndexedRoots →
    E8CombinedIndexedRootGeneratorShape indexedRoot

false≢true :
  false ≡ true →
  ⊥
false≢true ()

true≢false :
  true ≡ false →
  ⊥
true≢false ()

memberIndexedRootAppendRightWhenLeftFalse :
  (root : E8.E8IndexedRootCarrier) →
  (left right : E8.E8IndexedRootList) →
  E8.memberIndexedRoot root left ≡ false →
  E8.memberIndexedRoot root (left List.++ right) ≡ true →
  E8.memberIndexedRoot root right ≡ true
memberIndexedRootAppendRightWhenLeftFalse root [] right leftMiss appendHit =
  appendHit
memberIndexedRootAppendRightWhenLeftFalse
  root
  (candidate ∷ left)
  right
  leftMiss
  appendHit
  with E8.decEqIndexedRoot root candidate
... | yes _ =
  ⊥-elim (true≢false leftMiss)
... | no _ =
  memberIndexedRootAppendRightWhenLeftFalse
    root
    left
    right
    leftMiss
    appendHit

integerIndexedRootGeneratorShapeForPair :
  (indexedRoot : E8.E8IndexedRootCarrier) →
  (pair : E8.CoordinatePair8) →
  E8.memberIndexedRoot indexedRoot
    (E8.integerIndexedRootsForPair pair) ≡ true →
  E8IntegerIndexedRootGeneratorShape indexedRoot
integerIndexedRootGeneratorShapeForPair
  indexedRoot
  pair
  membershipCheck
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.negativeSign
      E8.negativeSign)
... | yes indexedRootIsGenerator =
  integerIndexedRootGeneratorShape
    pair
    E8.negativeSign
    E8.negativeSign
    indexedRootIsGenerator
... | no _
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.negativeSign
      E8.positiveSign)
... | yes indexedRootIsGenerator =
  integerIndexedRootGeneratorShape
    pair
    E8.negativeSign
    E8.positiveSign
    indexedRootIsGenerator
... | no _
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.positiveSign
      E8.negativeSign)
... | yes indexedRootIsGenerator =
  integerIndexedRootGeneratorShape
    pair
    E8.positiveSign
    E8.negativeSign
    indexedRootIsGenerator
... | no _
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.positiveSign
      E8.positiveSign)
... | yes indexedRootIsGenerator =
  integerIndexedRootGeneratorShape
    pair
    E8.positiveSign
    E8.positiveSign
    indexedRootIsGenerator
... | no _ =
  ⊥-elim (false≢true membershipCheck)

integerIndexedRootGeneratorShapeInPairList :
  (indexedRoot : E8.E8IndexedRootCarrier) →
  (pairs : List E8.CoordinatePair8) →
  E8.memberIndexedRoot indexedRoot
    (List.concatMap E8.integerIndexedRootsForPair pairs) ≡ true →
  E8IntegerIndexedRootGeneratorShape indexedRoot
integerIndexedRootGeneratorShapeInPairList indexedRoot [] ()
integerIndexedRootGeneratorShapeInPairList
  indexedRoot
  (pair ∷ pairs)
  membershipCheck
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.negativeSign
      E8.negativeSign)
... | yes indexedRootIsGenerator =
  integerIndexedRootGeneratorShape
    pair
    E8.negativeSign
    E8.negativeSign
    indexedRootIsGenerator
... | no _
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.negativeSign
      E8.positiveSign)
... | yes indexedRootIsGenerator =
  integerIndexedRootGeneratorShape
    pair
    E8.negativeSign
    E8.positiveSign
    indexedRootIsGenerator
... | no _
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.positiveSign
      E8.negativeSign)
... | yes indexedRootIsGenerator =
  integerIndexedRootGeneratorShape
    pair
    E8.positiveSign
    E8.negativeSign
    indexedRootIsGenerator
... | no _
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.positiveSign
      E8.positiveSign)
... | yes indexedRootIsGenerator =
  integerIndexedRootGeneratorShape
    pair
    E8.positiveSign
    E8.positiveSign
    indexedRootIsGenerator
... | no _ =
  integerIndexedRootGeneratorShapeInPairList
    indexedRoot
    pairs
    membershipCheck

integerIndexedRootMemberToGeneratorShape :
  {indexedRoot : E8.E8IndexedRootCarrier} →
  E8.IndexedRootMember indexedRoot E8.integerIndexedRoots →
  E8IntegerIndexedRootGeneratorShape indexedRoot
integerIndexedRootMemberToGeneratorShape {indexedRoot}
  (E8.memberByExecutableCheck membershipCheck) =
  integerIndexedRootGeneratorShapeInPairList
    indexedRoot
    E8.allCoordinatePairs8
    membershipCheck

halfIndexedRootGeneratorShapeInSignList :
  (indexedRoot : E8.E8IndexedRootCarrier) →
  (signRows : List (E8.EightVec E8.E8Sign)) →
  E8.memberIndexedRoot indexedRoot
    (List.map E8.signVectorToHalfIndexedRoot signRows) ≡ true →
  E8HalfIndexedRootGeneratorShape indexedRoot
halfIndexedRootGeneratorShapeInSignList indexedRoot [] ()
halfIndexedRootGeneratorShapeInSignList
  indexedRoot
  (signs ∷ signRows)
  membershipCheck
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.signVectorToHalfIndexedRoot signs)
... | yes indexedRootIsGenerator =
  halfIndexedRootGeneratorShape signs indexedRootIsGenerator
... | no _ =
  halfIndexedRootGeneratorShapeInSignList
    indexedRoot
    signRows
    membershipCheck

halfIndexedRootMemberToGeneratorShape :
  {indexedRoot : E8.E8IndexedRootCarrier} →
  E8.IndexedRootMember indexedRoot E8.halfIndexedRoots →
  E8HalfIndexedRootGeneratorShape indexedRoot
halfIndexedRootMemberToGeneratorShape {indexedRoot}
  (E8.memberByExecutableCheck membershipCheck) =
  halfIndexedRootGeneratorShapeInSignList
    indexedRoot
    (E8.evenSignVectors 8)
    membershipCheck

combinedIndexedRootIntegerShapeByGenerator :
  {indexedRoot : E8.E8IndexedRootCarrier} →
  (pair : E8.CoordinatePair8) →
  (leftSign rightSign : E8.E8Sign) →
  indexedRoot ≡ E8.mkIntegerIndexedRoot pair leftSign rightSign →
  E8CombinedIndexedRootGeneratorShape indexedRoot
combinedIndexedRootIntegerShapeByGenerator
  pair
  leftSign
  rightSign
  indexedRootIsGenerator =
  combinedIndexedRootIntegerShape
    (integerIndexedRootGeneratorShape
      pair
      leftSign
      rightSign
      indexedRootIsGenerator)
    (subst
      (λ candidate →
        E8.IndexedRootMember candidate E8.integerIndexedRoots)
      (sym indexedRootIsGenerator)
      (integerGeneratorIndexedMembershipNormalization
        pair
        leftSign
        rightSign))

combinedIndexedRootGeneratorShapeInIntegerPairList :
  (indexedRoot : E8.E8IndexedRootCarrier) →
  (pairs : List E8.CoordinatePair8) →
  E8.memberIndexedRoot indexedRoot
    (List.concatMap E8.integerIndexedRootsForPair pairs
     List.++ E8.halfIndexedRoots) ≡ true →
  E8CombinedIndexedRootGeneratorShape indexedRoot
combinedIndexedRootGeneratorShapeInIntegerPairList indexedRoot [] membershipCheck =
  combinedIndexedRootHalfShape
    (halfIndexedRootMemberToGeneratorShape
      (E8.memberByExecutableCheck membershipCheck))
    (E8.memberByExecutableCheck membershipCheck)
combinedIndexedRootGeneratorShapeInIntegerPairList
  indexedRoot
  (pair ∷ pairs)
  membershipCheck
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.negativeSign
      E8.negativeSign)
... | yes indexedRootIsGenerator =
  combinedIndexedRootIntegerShapeByGenerator
    pair
    E8.negativeSign
    E8.negativeSign
    indexedRootIsGenerator
... | no _
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.negativeSign
      E8.positiveSign)
... | yes indexedRootIsGenerator =
  combinedIndexedRootIntegerShapeByGenerator
    pair
    E8.negativeSign
    E8.positiveSign
    indexedRootIsGenerator
... | no _
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.positiveSign
      E8.negativeSign)
... | yes indexedRootIsGenerator =
  combinedIndexedRootIntegerShapeByGenerator
    pair
    E8.positiveSign
    E8.negativeSign
    indexedRootIsGenerator
... | no _
  with E8.decEqIndexedRoot
    indexedRoot
    (E8.mkIntegerIndexedRoot
      pair
      E8.positiveSign
      E8.positiveSign)
... | yes indexedRootIsGenerator =
  combinedIndexedRootIntegerShapeByGenerator
    pair
    E8.positiveSign
    E8.positiveSign
    indexedRootIsGenerator
... | no _ =
  combinedIndexedRootGeneratorShapeInIntegerPairList
    indexedRoot
    pairs
    membershipCheck

combinedIndexedRootMemberToGeneratorShape :
  {indexedRoot : E8.E8IndexedRootCarrier} →
  E8.IndexedRootMember indexedRoot E8.combinedIndexedRoots →
  E8CombinedIndexedRootGeneratorShape indexedRoot
combinedIndexedRootMemberToGeneratorShape {indexedRoot}
  (E8.memberByExecutableCheck membershipCheck) =
  combinedIndexedRootGeneratorShapeInIntegerPairList
    indexedRoot
    E8.allCoordinatePairs8
    membershipCheck

record E8IndexedRootGeneratorShapeInversionBridge : Set where
  field
    integerShapeInversion :
      {indexedRoot : E8.E8IndexedRootCarrier} →
      E8.IndexedRootMember indexedRoot E8.integerIndexedRoots →
      E8IntegerIndexedRootGeneratorShape indexedRoot

    halfShapeInversion :
      {indexedRoot : E8.E8IndexedRootCarrier} →
      E8.IndexedRootMember indexedRoot E8.halfIndexedRoots →
      E8HalfIndexedRootGeneratorShape indexedRoot

    combinedShapeInversion :
      {indexedRoot : E8.E8IndexedRootCarrier} →
      E8.IndexedRootMember indexedRoot E8.combinedIndexedRoots →
      E8CombinedIndexedRootGeneratorShape indexedRoot

indexedRootGeneratorShapeInversionBridge :
  E8IndexedRootGeneratorShapeInversionBridge
indexedRootGeneratorShapeInversionBridge =
  record
    { integerShapeInversion =
        integerIndexedRootMemberToGeneratorShape
    ; halfShapeInversion =
        halfIndexedRootMemberToGeneratorShape
    ; combinedShapeInversion =
        combinedIndexedRootMemberToGeneratorShape
    }

integerIndexedImageLookupToGeneratorWitness :
  {root : E8.E8RootCarrier} →
  (lookup : E8IndexedImageLookup root E8.integerIndexedRoots) →
  E8IntegerIndexedRootGeneratorShape
    (E8IndexedImageLookup.indexedRoot lookup) →
  E8IntegerFiniteMembershipGeneratorIndexedWitness root
integerIndexedImageLookupToGeneratorWitness
  (indexedImageLookup indexedRoot rootIsIndexedImage indexedMembership)
  (integerIndexedRootGeneratorShape
    pair
    leftSign
    rightSign
    indexedRootIsGenerator) =
  integerFiniteMembershipGeneratorIndexedWitness
    pair
    leftSign
    rightSign
    (trans
      rootIsIndexedImage
      (cong E8.indexedRootToHalfTritRoot indexedRootIsGenerator))
    (subst
      (λ candidate →
        E8.IndexedRootMember candidate E8.integerIndexedRoots)
      indexedRootIsGenerator
      indexedMembership)

halfIndexedImageLookupToGeneratorWitness :
  {root : E8.E8RootCarrier} →
  (lookup : E8IndexedImageLookup root E8.halfIndexedRoots) →
  E8HalfIndexedRootGeneratorShape
    (E8IndexedImageLookup.indexedRoot lookup) →
  E8HalfFiniteMembershipGeneratorIndexedWitness root
halfIndexedImageLookupToGeneratorWitness
  (indexedImageLookup indexedRoot rootIsIndexedImage indexedMembership)
  (halfIndexedRootGeneratorShape signs indexedRootIsGenerator) =
  halfFiniteMembershipGeneratorIndexedWitness
    signs
    (trans
      rootIsIndexedImage
      (cong E8.indexedRootToHalfTritRoot indexedRootIsGenerator))
    (subst
      (λ candidate →
        E8.IndexedRootMember candidate E8.halfIndexedRoots)
      indexedRootIsGenerator
      indexedMembership)

combinedIndexedImageLookupToGeneratorWitness :
  {root : E8.E8RootCarrier} →
  (lookup : E8IndexedImageLookup root E8.combinedIndexedRoots) →
  E8CombinedIndexedRootGeneratorShape
    (E8IndexedImageLookup.indexedRoot lookup) →
  E8CombinedFiniteMembershipGeneratorIndexedWitness root
combinedIndexedImageLookupToGeneratorWitness
  (indexedImageLookup indexedRoot rootIsIndexedImage indexedMembership)
  (combinedIndexedRootIntegerShape integerShape integerMembership) =
  combinedFiniteMembershipIntegerWitness
    (integerIndexedImageLookupToGeneratorWitness
      (indexedImageLookup indexedRoot rootIsIndexedImage integerMembership)
      integerShape)
combinedIndexedImageLookupToGeneratorWitness
  (indexedImageLookup indexedRoot rootIsIndexedImage indexedMembership)
  (combinedIndexedRootHalfShape halfShape halfMembership) =
  combinedFiniteMembershipHalfWitness
    (halfIndexedImageLookupToGeneratorWitness
      (indexedImageLookup indexedRoot rootIsIndexedImage halfMembership)
      halfShape)

record E8IndexedImageLookupToGeneratorWitnessConsumers : Set where
  field
    integerLookupConsumer :
      {root : E8.E8RootCarrier} →
      (lookup : E8IndexedImageLookup root E8.integerIndexedRoots) →
      E8IntegerIndexedRootGeneratorShape
        (E8IndexedImageLookup.indexedRoot lookup) →
      E8IntegerFiniteMembershipGeneratorIndexedWitness root

    halfLookupConsumer :
      {root : E8.E8RootCarrier} →
      (lookup : E8IndexedImageLookup root E8.halfIndexedRoots) →
      E8HalfIndexedRootGeneratorShape
        (E8IndexedImageLookup.indexedRoot lookup) →
      E8HalfFiniteMembershipGeneratorIndexedWitness root

    combinedLookupConsumer :
      {root : E8.E8RootCarrier} →
      (lookup : E8IndexedImageLookup root E8.combinedIndexedRoots) →
      E8CombinedIndexedRootGeneratorShape
        (E8IndexedImageLookup.indexedRoot lookup) →
      E8CombinedFiniteMembershipGeneratorIndexedWitness root

indexedImageLookupToGeneratorWitnessConsumers :
  E8IndexedImageLookupToGeneratorWitnessConsumers
indexedImageLookupToGeneratorWitnessConsumers =
  record
    { integerLookupConsumer =
        integerIndexedImageLookupToGeneratorWitness
    ; halfLookupConsumer =
        halfIndexedImageLookupToGeneratorWitness
    ; combinedLookupConsumer =
        combinedIndexedImageLookupToGeneratorWitness
    }

integerNativeFiniteMembershipToGeneratorWitness :
  {root : E8.E8RootCarrier} →
  E8SemanticNativeIntegerTwoSparseRoot root →
  E8IntegerFiniteMembershipGeneratorIndexedWitness root
integerNativeFiniteMembershipToGeneratorWitness membership
  with integerNativeBoolMembershipToIndexedImageLookup
    (nativeFiniteRootMemberToBoolMembership membership)
... | lookup =
  integerIndexedImageLookupToGeneratorWitness
    lookup
    (integerIndexedRootMemberToGeneratorShape
      (E8IndexedImageLookup.indexedMembership lookup))

halfNativeFiniteMembershipToGeneratorWitness :
  {root : E8.E8RootCarrier} →
  E8SemanticNativeHalfEvenParityRoot root →
  E8HalfFiniteMembershipGeneratorIndexedWitness root
halfNativeFiniteMembershipToGeneratorWitness membership
  with halfNativeBoolMembershipToIndexedImageLookup
    (nativeFiniteRootMemberToBoolMembership membership)
... | lookup =
  halfIndexedImageLookupToGeneratorWitness
    lookup
    (halfIndexedRootMemberToGeneratorShape
      (E8IndexedImageLookup.indexedMembership lookup))

combinedNativeFiniteMembershipToGeneratorWitness :
  {root : E8.E8RootCarrier} →
  E8SemanticNativeCombinedRoot root →
  E8CombinedFiniteMembershipGeneratorIndexedWitness root
combinedNativeFiniteMembershipToGeneratorWitness membership
  with combinedNativeBoolMembershipToIndexedImageLookup
    (nativeFiniteRootMemberToBoolMembership membership)
... | lookup =
  combinedIndexedImageLookupToGeneratorWitness
    lookup
    (combinedIndexedRootMemberToGeneratorShape
      (E8IndexedImageLookup.indexedMembership lookup))

record E8LocalSemanticNativeCompletenessSurface : Set where
  field
    integerCompletenessWitness :
      {root : E8.E8RootCarrier} →
      E8SemanticNativeIntegerTwoSparseRoot root →
      E8IntegerFiniteMembershipGeneratorIndexedWitness root

    halfCompletenessWitness :
      {root : E8.E8RootCarrier} →
      E8SemanticNativeHalfEvenParityRoot root →
      E8HalfFiniteMembershipGeneratorIndexedWitness root

    combinedCompletenessWitness :
      {root : E8.E8RootCarrier} →
      E8SemanticNativeCombinedRoot root →
      E8CombinedFiniteMembershipGeneratorIndexedWitness root

    integerHalfCombinedCompletenessClearedHere :
      Bool

    integerHalfCombinedCompletenessClearedHereIsTrue :
      integerHalfCombinedCompletenessClearedHere ≡ true

    promotesToUpstreamE8RootEnumerationComplete :
      Bool

    promotesToUpstreamE8RootEnumerationCompleteIsFalse :
      promotesToUpstreamE8RootEnumerationComplete ≡ false

localSemanticNativeCompletenessSurface :
  E8LocalSemanticNativeCompletenessSurface
localSemanticNativeCompletenessSurface =
  record
    { integerCompletenessWitness =
        integerNativeFiniteMembershipToGeneratorWitness
    ; halfCompletenessWitness =
        halfNativeFiniteMembershipToGeneratorWitness
    ; combinedCompletenessWitness =
        combinedNativeFiniteMembershipToGeneratorWitness
    ; integerHalfCombinedCompletenessClearedHere =
        true
    ; integerHalfCombinedCompletenessClearedHereIsTrue =
        refl
    ; promotesToUpstreamE8RootEnumerationComplete =
        false
    ; promotesToUpstreamE8RootEnumerationCompleteIsFalse =
        refl
    }

data E8NativeCompletenessPromotionBlocker : Set where
  missingPromotionFromLocalSemanticFiniteCompletenessToUpstreamCompleteReceipt :
    E8NativeCompletenessPromotionBlocker

canonicalE8NativeCompletenessPromotionBlockers :
  List E8NativeCompletenessPromotionBlocker
canonicalE8NativeCompletenessPromotionBlockers =
  missingPromotionFromLocalSemanticFiniteCompletenessToUpstreamCompleteReceipt
  ∷ []

data E8UpstreamCompleteReceiptConstructorBoundary : Set where
  upstreamE8RootEnumerationCompleteHasNoConstructors :
    E8UpstreamCompleteReceiptConstructorBoundary

record E8UpstreamCompleteReceiptPromotionAudit : Setω where
  field
    upstreamCompleteReceiptTypeName :
      String

    upstreamCompleteReceiptConstructorBoundary :
      E8UpstreamCompleteReceiptConstructorBoundary

    upstreamCompleteReceiptEliminator :
      E8.E8RootEnumerationComplete →
      ⊥

    upstreamCanonicalObstruction :
      E8.E8RootEnumerationObstruction

    upstreamRequiredConcreteProofObligations :
      List E8.E8RootEnumerationProofObligation

    upstreamRequiredConcreteProofObligationsAreCanonical :
      upstreamRequiredConcreteProofObligations
      ≡
      E8.canonicalE8RootEnumerationProofObligations

    upstreamRequiredEnumerationObligations :
      List E8.E8RootEnumerationObligation

    upstreamRequiredEnumerationObligationsAreCanonical :
      upstreamRequiredEnumerationObligations
      ≡
      E8.canonicalE8RootEnumerationObligations

    upstreamReceiptCompletedHere :
      Bool

    upstreamReceiptCompletedHereIsFalse :
      upstreamReceiptCompletedHere ≡ false

    localSemanticCompletenessReceipt :
      E8LocalSemanticNativeCompletenessSurface

    localSemanticCompletenessClearsFiniteIntegerHalfCombined :
      E8LocalSemanticNativeCompletenessSurface.integerHalfCombinedCompletenessClearedHere
        localSemanticCompletenessReceipt
      ≡
      true

    localSemanticCompletenessIsNotUpstreamConstructor :
      Bool

    localSemanticCompletenessIsNotUpstreamConstructorIsTrue :
      localSemanticCompletenessIsNotUpstreamConstructor ≡ true

    exactMissingPromotionBlocker :
      E8NativeCompletenessPromotionBlocker

    exactMissingPromotionBlockerIsCanonical :
      exactMissingPromotionBlocker
      ≡
      missingPromotionFromLocalSemanticFiniteCompletenessToUpstreamCompleteReceipt

    promotionImplementedHere :
      Bool

    promotionImplementedHereIsFalse :
      promotionImplementedHere ≡ false

    promotionAuditShape :
      String

canonicalE8UpstreamCompleteReceiptPromotionAudit :
  E8UpstreamCompleteReceiptPromotionAudit
canonicalE8UpstreamCompleteReceiptPromotionAudit =
  record
    { upstreamCompleteReceiptTypeName =
        "DASHI.Algebra.Trit.E8RootEnumeration.E8RootEnumerationComplete"
    ; upstreamCompleteReceiptConstructorBoundary =
        upstreamE8RootEnumerationCompleteHasNoConstructors
    ; upstreamCompleteReceiptEliminator =
        E8.e8RootEnumerationCompleteImpossibleHere
    ; upstreamCanonicalObstruction =
        E8.canonicalE8RootEnumerationObstruction
    ; upstreamRequiredConcreteProofObligations =
        E8.E8RootEnumerationObstruction.remainingConcreteProofObligations
          E8.canonicalE8RootEnumerationObstruction
    ; upstreamRequiredConcreteProofObligationsAreCanonical =
        E8.E8RootEnumerationObstruction.remainingConcreteProofObligationsAreCanonical
          E8.canonicalE8RootEnumerationObstruction
    ; upstreamRequiredEnumerationObligations =
        E8.E8RootEnumerationObstruction.remainingEnumerationObligations
          E8.canonicalE8RootEnumerationObstruction
    ; upstreamRequiredEnumerationObligationsAreCanonical =
        E8.E8RootEnumerationObstruction.remainingEnumerationObligationsAreCanonical
          E8.canonicalE8RootEnumerationObstruction
    ; upstreamReceiptCompletedHere =
        E8.E8RootEnumerationObstruction.receiptCompletedHere
          E8.canonicalE8RootEnumerationObstruction
    ; upstreamReceiptCompletedHereIsFalse =
        E8.E8RootEnumerationObstruction.receiptCompletedHereIsFalse
          E8.canonicalE8RootEnumerationObstruction
    ; localSemanticCompletenessReceipt =
        localSemanticNativeCompletenessSurface
    ; localSemanticCompletenessClearsFiniteIntegerHalfCombined =
        refl
    ; localSemanticCompletenessIsNotUpstreamConstructor =
        true
    ; localSemanticCompletenessIsNotUpstreamConstructorIsTrue =
        refl
    ; exactMissingPromotionBlocker =
        missingPromotionFromLocalSemanticFiniteCompletenessToUpstreamCompleteReceipt
    ; exactMissingPromotionBlockerIsCanonical =
        refl
    ; promotionImplementedHere =
        false
    ; promotionImplementedHereIsFalse =
        refl
    ; promotionAuditShape =
        "The local semantic finite completeness surface is available, but upstream E8RootEnumerationComplete has no constructors here; promotion remains blocked by canonical upstream concrete proof obligations and enumeration obligations."
    }

record E8LocalSemanticCompletenessUpstreamPromotionBoundary : Setω where
  field
    localSemanticCompletenessReceipt :
      E8LocalSemanticNativeCompletenessSurface

    localSemanticCompletenessClearsIntegerHalfCombined :
      E8LocalSemanticNativeCompletenessSurface.integerHalfCombinedCompletenessClearedHere
        localSemanticCompletenessReceipt
      ≡
      true

    localSemanticCompletenessDoesNotPromoteUpstream :
      E8LocalSemanticNativeCompletenessSurface.promotesToUpstreamE8RootEnumerationComplete
        localSemanticCompletenessReceipt
      ≡
      false

    upstreamObstruction :
      E8.E8RootEnumerationObstruction

    upstreamRemainingConcreteProofObligations :
      List E8.E8RootEnumerationProofObligation

    upstreamRemainingConcreteProofObligationsAreCanonical :
      upstreamRemainingConcreteProofObligations
      ≡
      E8.canonicalE8RootEnumerationProofObligations

    upstreamRemainingEnumerationObligations :
      List E8.E8RootEnumerationObligation

    upstreamRemainingEnumerationObligationsAreCanonical :
      upstreamRemainingEnumerationObligations
      ≡
      E8.canonicalE8RootEnumerationObligations

    upstreamReceiptCompletedHere :
      Bool

    upstreamReceiptCompletedHereIsFalse :
      upstreamReceiptCompletedHere ≡ false

    upstreamCompleteReceiptBlocked :
      E8.E8RootEnumerationComplete →
      ⊥

    exactPromotionBlockers :
      List E8NativeCompletenessPromotionBlocker

    exactPromotionBlockersAreCanonical :
      exactPromotionBlockers
      ≡
      canonicalE8NativeCompletenessPromotionBlockers

    upstreamCompleteReceiptPromotionAudit :
      E8UpstreamCompleteReceiptPromotionAudit

    upstreamCompleteReceiptPromotionAuditDoesNotPromote :
      E8UpstreamCompleteReceiptPromotionAudit.promotionImplementedHere
        upstreamCompleteReceiptPromotionAudit
      ≡
      false

    promotionToUpstreamCompleteReceiptImplemented :
      Bool

    promotionToUpstreamCompleteReceiptImplementedIsFalse :
      promotionToUpstreamCompleteReceiptImplemented ≡ false

    promotionBoundaryShape :
      String

localSemanticCompletenessUpstreamPromotionBoundary :
  E8LocalSemanticCompletenessUpstreamPromotionBoundary
localSemanticCompletenessUpstreamPromotionBoundary =
  record
    { localSemanticCompletenessReceipt =
        localSemanticNativeCompletenessSurface
    ; localSemanticCompletenessClearsIntegerHalfCombined =
        refl
    ; localSemanticCompletenessDoesNotPromoteUpstream =
        refl
    ; upstreamObstruction =
        E8.canonicalE8RootEnumerationObstruction
    ; upstreamRemainingConcreteProofObligations =
        E8.E8RootEnumerationObstruction.remainingConcreteProofObligations
          E8.canonicalE8RootEnumerationObstruction
    ; upstreamRemainingConcreteProofObligationsAreCanonical =
        E8.E8RootEnumerationObstruction.remainingConcreteProofObligationsAreCanonical
          E8.canonicalE8RootEnumerationObstruction
    ; upstreamRemainingEnumerationObligations =
        E8.E8RootEnumerationObstruction.remainingEnumerationObligations
          E8.canonicalE8RootEnumerationObstruction
    ; upstreamRemainingEnumerationObligationsAreCanonical =
        E8.E8RootEnumerationObstruction.remainingEnumerationObligationsAreCanonical
          E8.canonicalE8RootEnumerationObstruction
    ; upstreamReceiptCompletedHere =
        E8.E8RootEnumerationObstruction.receiptCompletedHere
          E8.canonicalE8RootEnumerationObstruction
    ; upstreamReceiptCompletedHereIsFalse =
        E8.E8RootEnumerationObstruction.receiptCompletedHereIsFalse
          E8.canonicalE8RootEnumerationObstruction
    ; upstreamCompleteReceiptBlocked =
        E8.E8RootEnumerationObstruction.completeReceiptBlocked
          E8.canonicalE8RootEnumerationObstruction
    ; exactPromotionBlockers =
        canonicalE8NativeCompletenessPromotionBlockers
    ; exactPromotionBlockersAreCanonical =
        refl
    ; upstreamCompleteReceiptPromotionAudit =
        canonicalE8UpstreamCompleteReceiptPromotionAudit
    ; upstreamCompleteReceiptPromotionAuditDoesNotPromote =
        refl
    ; promotionToUpstreamCompleteReceiptImplemented =
        false
    ; promotionToUpstreamCompleteReceiptImplementedIsFalse =
        refl
    ; promotionBoundaryShape =
        "Local semantic finite completeness is wired to the upstream obstruction; promotion is blocked because E8RootEnumerationComplete has no constructor and upstream remainingConcreteProofObligations/remainingEnumerationObligations remain canonical."
    }

nativeFiniteMembershipWitnessToGeneratorClassifierPrimitive :
  E8NativeFiniteMembershipWitnessToGeneratorClassifierPrimitive
nativeFiniteMembershipWitnessToGeneratorClassifierPrimitive =
  record
    { integerFiniteMembershipCarriesGeneratorIndex =
        integerNativeFiniteMembershipToGeneratorWitness
    ; halfFiniteMembershipCarriesGeneratorIndex =
        halfNativeFiniteMembershipToGeneratorWitness
    ; combinedFiniteMembershipCarriesGeneratorIndex =
        combinedNativeFiniteMembershipToGeneratorWitness
    }

data E8NativeFiniteMembershipWitnessPrimitiveBlocker : Set where
  missingIntegerNativeBoolMembershipToIndexedGeneratorReflection :
    E8NativeFiniteMembershipWitnessPrimitiveBlocker
  missingNativeBoolMembershipToProofRelevantIndexedWitnessConversion :
    E8NativeFiniteMembershipWitnessPrimitiveBlocker
  missingIntegerNativeMembershipLookupTableTotalityForArbitraryNativeMembers :
    E8NativeFiniteMembershipWitnessPrimitiveBlocker
  missingHalfNativeMembershipLookupTable :
    E8NativeFiniteMembershipWitnessPrimitiveBlocker
  missingCombinedNativeMembershipLookupTable :
    E8NativeFiniteMembershipWitnessPrimitiveBlocker
  missingNativeRootEqualityReflectsIndexedGeneratorImage :
    E8NativeFiniteMembershipWitnessPrimitiveBlocker
  missingProofRelevantLookupOverExecutableBoolMembership :
    E8NativeFiniteMembershipWitnessPrimitiveBlocker
  missingIndexedRootGeneratorShapeInversion :
    E8NativeFiniteMembershipWitnessPrimitiveBlocker

canonicalE8NativeFiniteMembershipWitnessPrimitiveBlockers :
  List E8NativeFiniteMembershipWitnessPrimitiveBlocker
canonicalE8NativeFiniteMembershipWitnessPrimitiveBlockers =
  []

canonicalE8NativeFiniteMembershipWitnessPrimitiveBlockersBeforeIntegerLookupNarrowing :
  List E8NativeFiniteMembershipWitnessPrimitiveBlocker
canonicalE8NativeFiniteMembershipWitnessPrimitiveBlockersBeforeIntegerLookupNarrowing =
  []

data E8IntegerNativeTotalLookupRequiredPrimitive : Set where
  integerNativeBoolMembershipReflectsIndexedGeneratorImage :
    E8IntegerNativeTotalLookupRequiredPrimitive
  integerNativeRootEqualityReflectsCoordinatePairAndSigns :
    E8IntegerNativeTotalLookupRequiredPrimitive
  integerGeneratorIndexedMemberSelectsWitnessTableRow :
    E8IntegerNativeTotalLookupRequiredPrimitive

canonicalE8IntegerNativeTotalLookupRequiredPrimitives :
  List E8IntegerNativeTotalLookupRequiredPrimitive
canonicalE8IntegerNativeTotalLookupRequiredPrimitives =
  integerNativeBoolMembershipReflectsIndexedGeneratorImage
  ∷ integerNativeRootEqualityReflectsCoordinatePairAndSigns
  ∷ integerGeneratorIndexedMemberSelectsWitnessTableRow
  ∷ []

record E8IntegerNativeMembershipTotalLookupRequest : Set where
  field
    availableIntegerWitnessTable :
      E8IntegerGeneratorMembershipWitnessTable

    requiredPrimitives :
      List E8IntegerNativeTotalLookupRequiredPrimitive

    requiredPrimitivesAreCanonical :
      requiredPrimitives ≡
      canonicalE8IntegerNativeTotalLookupRequiredPrimitives

    currentNativeMembershipShape :
      String

    requestedIndexedReflectionShape :
      String

    requestedPairSignDecompositionShape :
      String

    requestedTotalLookupShape :
      String

    currentNativeMembershipCarriesPairSignData :
      Bool

    currentNativeMembershipCarriesPairSignDataIsFalse :
      currentNativeMembershipCarriesPairSignData ≡ false

    totalLookupImplementedHere :
      Bool

    totalLookupImplementedHereIsTrue :
      totalLookupImplementedHere ≡ true

    indexedImageLookupConsumerAvailable :
      Bool

    indexedImageLookupConsumerAvailableIsTrue :
      indexedImageLookupConsumerAvailable ≡ true

    remainingPrimitiveBlockers :
      List E8NativeFiniteMembershipWitnessPrimitiveBlocker

canonicalE8IntegerNativeMembershipTotalLookupRequest :
  E8IntegerNativeMembershipTotalLookupRequest
canonicalE8IntegerNativeMembershipTotalLookupRequest =
  record
    { availableIntegerWitnessTable =
        canonicalE8IntegerGeneratorMembershipWitnessTable
    ; requiredPrimitives =
        canonicalE8IntegerNativeTotalLookupRequiredPrimitives
    ; requiredPrimitivesAreCanonical =
        refl
    ; currentNativeMembershipShape =
        "E8SemanticNativeIntegerTwoSparseRoot root = nativeMemberByExecutableCheck (memberNativeRoot root E8.integerRoots == true); it carries only the Bool equality proof"
    ; requestedIndexedReflectionShape =
        "{root : E8.E8RootCarrier} -> memberNativeRoot root E8.integerRoots == true -> Sigma indexedRoot . root == E8.indexedRootToHalfTritRoot indexedRoot x E8.IndexedRootMember indexedRoot E8.integerIndexedRoots"
    ; requestedPairSignDecompositionShape =
        "indexedRoot : E8.E8IndexedRootCarrier -> E8.IndexedRootMember indexedRoot E8.integerIndexedRoots -> Sigma pair leftSign rightSign . indexedRoot == E8.mkIntegerIndexedRoot pair leftSign rightSign"
    ; requestedTotalLookupShape =
        "{root : E8.E8RootCarrier} -> E8SemanticNativeIntegerTwoSparseRoot root -> E8IntegerFiniteMembershipGeneratorIndexedWitness root"
    ; currentNativeMembershipCarriesPairSignData =
        false
    ; currentNativeMembershipCarriesPairSignDataIsFalse =
        refl
    ; totalLookupImplementedHere =
        true
    ; totalLookupImplementedHereIsTrue =
        refl
    ; indexedImageLookupConsumerAvailable =
        true
    ; indexedImageLookupConsumerAvailableIsTrue =
        refl
    ; remainingPrimitiveBlockers =
        canonicalE8NativeFiniteMembershipWitnessPrimitiveBlockers
    }

data E8NativeBoolMembershipReflectionTarget : Set where
  nativeBoolIntegerMembershipToIntegerIndexedWitness :
    E8NativeBoolMembershipReflectionTarget
  nativeBoolHalfMembershipToHalfIndexedWitness :
    E8NativeBoolMembershipReflectionTarget
  nativeBoolCombinedMembershipToCombinedIndexedWitness :
    E8NativeBoolMembershipReflectionTarget

canonicalE8NativeBoolMembershipReflectionTargets :
  List E8NativeBoolMembershipReflectionTarget
canonicalE8NativeBoolMembershipReflectionTargets =
  nativeBoolIntegerMembershipToIntegerIndexedWitness
  ∷ nativeBoolHalfMembershipToHalfIndexedWitness
  ∷ nativeBoolCombinedMembershipToCombinedIndexedWitness
  ∷ []

record E8NativeBoolMembershipToIndexedWitnessRequest : Set where
  field
    requestedTargets :
      List E8NativeBoolMembershipReflectionTarget

    requestedTargetsAreCanonical :
      requestedTargets ≡
      canonicalE8NativeBoolMembershipReflectionTargets

    currentBoolMembershipShape :
      String

    implementedBoolToFiniteMembershipReflectionShape :
      String

    requestedIntegerWitnessConversionShape :
      String

    requestedHalfWitnessConversionShape :
      String

    requestedCombinedWitnessConversionShape :
      String

    requiredLookupApiShape :
      String

    exactMissingIndexedLookupBridgeShape :
      String

    concreteLookupOrIndexApiFoundHere :
      Bool

    concreteLookupOrIndexApiFoundHereIsTrue :
      concreteLookupOrIndexApiFoundHere ≡ true

    reflectionImplementedHere :
      Bool

    reflectionImplementedHereIsTrue :
      reflectionImplementedHere ≡ true

    indexedImageLookupBridgeImplementedHere :
      Bool

    indexedImageLookupBridgeImplementedHereIsTrue :
      indexedImageLookupBridgeImplementedHere ≡ true

    indexedImageLookupToGeneratorWitnessConsumerImplementedHere :
      Bool

    indexedImageLookupToGeneratorWitnessConsumerImplementedHereIsTrue :
      indexedImageLookupToGeneratorWitnessConsumerImplementedHere ≡ true

    remainingPrimitiveBlockers :
      List E8NativeFiniteMembershipWitnessPrimitiveBlocker

canonicalE8NativeBoolMembershipToIndexedWitnessRequest :
  E8NativeBoolMembershipToIndexedWitnessRequest
canonicalE8NativeBoolMembershipToIndexedWitnessRequest =
  record
    { requestedTargets =
        canonicalE8NativeBoolMembershipReflectionTargets
    ; requestedTargetsAreCanonical =
        refl
    ; currentBoolMembershipShape =
        "{root : E8.E8RootCarrier} -> memberNativeRoot root roots == true; this only states executable native-list membership"
    ; implementedBoolToFiniteMembershipReflectionShape =
        "{root : E8.E8RootCarrier} {roots : E8.E8RootList} -> memberNativeRoot root roots == true -> E8NativeFiniteRootMember root roots; indexed-image lookup plus generator-shape inversion now carries integer, half, and combined generator rows"
    ; requestedIntegerWitnessConversionShape =
        "{root : E8.E8RootCarrier} -> memberNativeRoot root E8.integerRoots == true -> E8IntegerFiniteMembershipGeneratorIndexedWitness root"
    ; requestedHalfWitnessConversionShape =
        "{root : E8.E8RootCarrier} -> memberNativeRoot root E8.halfRoots == true -> E8HalfFiniteMembershipGeneratorIndexedWitness root"
    ; requestedCombinedWitnessConversionShape =
        "{root : E8.E8RootCarrier} -> memberNativeRoot root E8.combinedRoots == true -> E8CombinedFiniteMembershipGeneratorIndexedWitness root"
    ; requiredLookupApiShape =
        "A proof-relevant finite-list lookup/index API that returns the matching indexed root, root == indexedRootToHalfTritRoot indexedRoot, and IndexedRootMember indexedRoot familyIndexedRoots"
    ; exactMissingIndexedLookupBridgeShape =
        "{root : E8.E8RootCarrier} {indexedRoots : E8.E8IndexedRootList} -> memberNativeRoot root (indexedImage indexedRoots) == true -> Sigma indexedRoot . root == E8.indexedRootToHalfTritRoot indexedRoot x E8.IndexedRootMember indexedRoot indexedRoots; specialized consumers needed for integerIndexedRoots, halfIndexedRoots, and combinedIndexedRoots"
    ; concreteLookupOrIndexApiFoundHere =
        true
    ; concreteLookupOrIndexApiFoundHereIsTrue =
        refl
    ; reflectionImplementedHere =
        true
    ; reflectionImplementedHereIsTrue =
        refl
    ; indexedImageLookupBridgeImplementedHere =
        true
    ; indexedImageLookupBridgeImplementedHereIsTrue =
        refl
    ; indexedImageLookupToGeneratorWitnessConsumerImplementedHere =
        true
    ; indexedImageLookupToGeneratorWitnessConsumerImplementedHereIsTrue =
        refl
    ; remainingPrimitiveBlockers =
        canonicalE8NativeFiniteMembershipWitnessPrimitiveBlockers
    }

data E8SemanticFiniteMembershipToGeneratorClassifierEquivalenceNarrowing :
  Set where
  semanticFiniteMembershipEquivalenceNarrowedToWitnessCarryingInverse :
    List E8SemanticFiniteMembershipClassifierInverseObligation →
    List E8NativeFiniteMembershipWitnessPrimitiveBlocker →
    E8SemanticFiniteMembershipToGeneratorClassifierEquivalenceNarrowing

semanticFiniteMembershipToGeneratorClassifierEquivalenceNarrowing :
  E8SemanticFiniteMembershipToGeneratorClassifierEquivalenceNarrowing
semanticFiniteMembershipToGeneratorClassifierEquivalenceNarrowing =
  semanticFiniteMembershipEquivalenceNarrowedToWitnessCarryingInverse
    canonicalE8SemanticFiniteMembershipClassifierInverseObligations
    canonicalE8NativeFiniteMembershipWitnessPrimitiveBlockers

record LilaE8NativeShapePredicateLayer : Set where
  field
    integerTwoSparseShapePredicateAvailable :
      Bool

    integerTwoSparseShapePredicateAvailableIsTrue :
      integerTwoSparseShapePredicateAvailable ≡ true

    halfEvenParityShapePredicateAvailable :
      Bool

    halfEvenParityShapePredicateAvailableIsTrue :
      halfEvenParityShapePredicateAvailable ≡ true

    combinedShapePredicateAvailable :
      Bool

    combinedShapePredicateAvailableIsTrue :
      combinedShapePredicateAvailable ≡ true

    integerClassifierInverseAvailable :
      Bool

    integerClassifierInverseAvailableIsTrue :
      integerClassifierInverseAvailable ≡ true

    halfClassifierInverseAvailable :
      Bool

    halfClassifierInverseAvailableIsTrue :
      halfClassifierInverseAvailable ≡ true

    combinedClassifierCaseSplitAvailable :
      Bool

    combinedClassifierCaseSplitAvailableIsTrue :
      combinedClassifierCaseSplitAvailable ≡ true

    integerGeneratorMembershipNormalizationAvailable :
      Bool

    integerGeneratorMembershipNormalizationAvailableIsTrue :
      integerGeneratorMembershipNormalizationAvailable ≡ true

    integerGeneratorMembershipNormalizationReceipt :
      E8IntegerGeneratorMembershipNormalization

    integerGeneratorMembershipWitnessTableAvailable :
      Bool

    integerGeneratorMembershipWitnessTableAvailableIsTrue :
      integerGeneratorMembershipWitnessTableAvailable ≡ true

    integerGeneratorMembershipWitnessTable :
      E8IntegerGeneratorMembershipWitnessTable

    halfGeneratorCombinedMembershipNormalizationAvailable :
      Bool

    halfGeneratorCombinedMembershipNormalizationAvailableIsTrue :
      halfGeneratorCombinedMembershipNormalizationAvailable ≡ true

    halfGeneratorCombinedMembershipNormalizationReceipt :
      E8HalfGeneratorCombinedMembershipNormalization

    combinedClassifierMembershipNormalizationAvailable :
      Bool

    combinedClassifierMembershipNormalizationAvailableIsTrue :
      combinedClassifierMembershipNormalizationAvailable ≡ true

    combinedClassifierMembershipNormalizationReceipt :
      E8CombinedClassifierMembershipNormalization

    semanticNativeClassifierPredicatesAvailable :
      Bool

    semanticNativeClassifierPredicatesAvailableIsTrue :
      semanticNativeClassifierPredicatesAvailable ≡ true

    semanticNativeClassifierPredicateReceipt :
      E8SemanticNativeClassifierPredicatesForArbitraryRoots

    semanticFiniteMembershipEquivalenceNarrowingAvailable :
      Bool

    semanticFiniteMembershipEquivalenceNarrowingAvailableIsTrue :
      semanticFiniteMembershipEquivalenceNarrowingAvailable ≡ true

    semanticFiniteMembershipEquivalenceNarrowingReceipt :
      E8SemanticFiniteMembershipToGeneratorClassifierEquivalenceNarrowing

    finiteMembershipWitnessTableRequestAvailable :
      Bool

    finiteMembershipWitnessTableRequestAvailableIsTrue :
      finiteMembershipWitnessTableRequestAvailable ≡ true

    finiteMembershipWitnessTableRequest :
      E8FiniteMembershipWitnessTableRequest

    nativeBoolMembershipToIndexedWitnessRequestAvailable :
      Bool

    nativeBoolMembershipToIndexedWitnessRequestAvailableIsTrue :
      nativeBoolMembershipToIndexedWitnessRequestAvailable ≡ true

    nativeBoolMembershipToIndexedWitnessRequest :
      E8NativeBoolMembershipToIndexedWitnessRequest

    indexedRootGeneratorShapeInversionBridgeAvailable :
      Bool

    indexedRootGeneratorShapeInversionBridgeAvailableIsTrue :
      indexedRootGeneratorShapeInversionBridgeAvailable ≡ true

    indexedRootGeneratorShapeInversionBridgeReceipt :
      E8IndexedRootGeneratorShapeInversionBridge

    nativeFiniteMembershipWitnessPrimitiveAvailable :
      Bool

    nativeFiniteMembershipWitnessPrimitiveAvailableIsTrue :
      nativeFiniteMembershipWitnessPrimitiveAvailable ≡ true

    nativeFiniteMembershipWitnessPrimitiveReceipt :
      E8NativeFiniteMembershipWitnessToGeneratorClassifierPrimitive

    localSemanticNativeCompletenessAvailable :
      Bool

    localSemanticNativeCompletenessAvailableIsTrue :
      localSemanticNativeCompletenessAvailable ≡ true

    localSemanticNativeCompletenessReceipt :
      E8LocalSemanticNativeCompletenessSurface

    localSemanticNativeCompletenessClearsIntegerHalfCombined :
      E8LocalSemanticNativeCompletenessSurface.integerHalfCombinedCompletenessClearedHere
        localSemanticNativeCompletenessReceipt
      ≡
      true

    nativeCompletenessPromotionBlockers :
      List E8NativeCompletenessPromotionBlocker

    nativeCompletenessPromotionBlockersAreCanonical :
      nativeCompletenessPromotionBlockers
      ≡
      canonicalE8NativeCompletenessPromotionBlockers

    generatorShapesPromoteNativeCompleteness :
      Bool

    generatorShapesPromoteNativeCompletenessIsFalse :
      generatorShapesPromoteNativeCompleteness ≡ false

    refinedFirstMissing :
      List LilaE8NativeCompletenessRefinedFirstMissing

    refinedFirstMissingIsCanonical :
      refinedFirstMissing ≡
      canonicalLilaE8NativeCompletenessRefinedFirstMissingAfterHalfCombinedNormalization

canonicalLilaE8NativeShapePredicateLayer :
  LilaE8NativeShapePredicateLayer
canonicalLilaE8NativeShapePredicateLayer =
  record
    { integerTwoSparseShapePredicateAvailable =
        true
    ; integerTwoSparseShapePredicateAvailableIsTrue =
        refl
    ; halfEvenParityShapePredicateAvailable =
        true
    ; halfEvenParityShapePredicateAvailableIsTrue =
        refl
    ; combinedShapePredicateAvailable =
        true
    ; combinedShapePredicateAvailableIsTrue =
        refl
    ; integerClassifierInverseAvailable =
        true
    ; integerClassifierInverseAvailableIsTrue =
        refl
    ; halfClassifierInverseAvailable =
        true
    ; halfClassifierInverseAvailableIsTrue =
        refl
    ; combinedClassifierCaseSplitAvailable =
        true
    ; combinedClassifierCaseSplitAvailableIsTrue =
        refl
    ; integerGeneratorMembershipNormalizationAvailable =
        true
    ; integerGeneratorMembershipNormalizationAvailableIsTrue =
        refl
    ; integerGeneratorMembershipNormalizationReceipt =
        integerGeneratorMembershipNormalization
    ; integerGeneratorMembershipWitnessTableAvailable =
        true
    ; integerGeneratorMembershipWitnessTableAvailableIsTrue =
        refl
    ; integerGeneratorMembershipWitnessTable =
        canonicalE8IntegerGeneratorMembershipWitnessTable
    ; halfGeneratorCombinedMembershipNormalizationAvailable =
        true
    ; halfGeneratorCombinedMembershipNormalizationAvailableIsTrue =
        refl
    ; halfGeneratorCombinedMembershipNormalizationReceipt =
        halfGeneratorCombinedMembershipNormalization
    ; combinedClassifierMembershipNormalizationAvailable =
        true
    ; combinedClassifierMembershipNormalizationAvailableIsTrue =
        refl
    ; combinedClassifierMembershipNormalizationReceipt =
        combinedClassifierMembershipNormalization
    ; semanticNativeClassifierPredicatesAvailable =
        true
    ; semanticNativeClassifierPredicatesAvailableIsTrue =
        refl
    ; semanticNativeClassifierPredicateReceipt =
        semanticNativeClassifierPredicatesForArbitraryRoots
    ; semanticFiniteMembershipEquivalenceNarrowingAvailable =
        true
    ; semanticFiniteMembershipEquivalenceNarrowingAvailableIsTrue =
        refl
    ; semanticFiniteMembershipEquivalenceNarrowingReceipt =
        semanticFiniteMembershipToGeneratorClassifierEquivalenceNarrowing
    ; finiteMembershipWitnessTableRequestAvailable =
        true
    ; finiteMembershipWitnessTableRequestAvailableIsTrue =
        refl
    ; finiteMembershipWitnessTableRequest =
        canonicalE8FiniteMembershipWitnessTableRequest
    ; nativeBoolMembershipToIndexedWitnessRequestAvailable =
        true
    ; nativeBoolMembershipToIndexedWitnessRequestAvailableIsTrue =
        refl
    ; nativeBoolMembershipToIndexedWitnessRequest =
        canonicalE8NativeBoolMembershipToIndexedWitnessRequest
    ; indexedRootGeneratorShapeInversionBridgeAvailable =
        true
    ; indexedRootGeneratorShapeInversionBridgeAvailableIsTrue =
        refl
    ; indexedRootGeneratorShapeInversionBridgeReceipt =
        indexedRootGeneratorShapeInversionBridge
    ; nativeFiniteMembershipWitnessPrimitiveAvailable =
        true
    ; nativeFiniteMembershipWitnessPrimitiveAvailableIsTrue =
        refl
    ; nativeFiniteMembershipWitnessPrimitiveReceipt =
        nativeFiniteMembershipWitnessToGeneratorClassifierPrimitive
    ; localSemanticNativeCompletenessAvailable =
        true
    ; localSemanticNativeCompletenessAvailableIsTrue =
        refl
    ; localSemanticNativeCompletenessReceipt =
        localSemanticNativeCompletenessSurface
    ; localSemanticNativeCompletenessClearsIntegerHalfCombined =
        refl
    ; nativeCompletenessPromotionBlockers =
        canonicalE8NativeCompletenessPromotionBlockers
    ; nativeCompletenessPromotionBlockersAreCanonical =
        refl
    ; generatorShapesPromoteNativeCompleteness =
        false
    ; generatorShapesPromoteNativeCompletenessIsFalse =
        refl
    ; refinedFirstMissing =
        canonicalLilaE8NativeCompletenessRefinedFirstMissingAfterHalfCombinedNormalization
    ; refinedFirstMissingIsCanonical =
        refl
    }

integerTwoSparseGeneratorCompletenessNativeWrapper :
  E8IntegerTwoSparseGeneratorCompleteness E8.integerRoots
integerTwoSparseGeneratorCompletenessNativeWrapper =
  integerTwoSparseGeneratorCompleteByIndexedImage
    refl
    integerRootsNoDuplicatesNativeWrapper

halfEvenParityGeneratorCompletenessNativeWrapper :
  E8HalfEvenParityGeneratorCompleteness E8.halfRoots
halfEvenParityGeneratorCompletenessNativeWrapper =
  halfEvenParityGeneratorCompleteByIndexedImage
    refl
    E8.halfIndexedRootsParitySoundBridge
    halfRootsNoDuplicatesNativeWrapper

combinedGeneratorCompletenessNativeWrapper :
  E8CombinedGeneratorCompleteness E8.combinedRoots
combinedGeneratorCompletenessNativeWrapper =
  combinedGeneratorCompleteByIndexedImage
    refl
    combinedRootsNoDuplicatesNativeWrapper
    integerHalfRootsDisjointNativeWrapper

record LilaE8NativeWrapperLayer : Set where
  field
    membershipBridgeAvailable :
      Bool

    membershipBridgeAvailableIsTrue :
      membershipBridgeAvailable ≡ true

    integerNoDuplicatesNative :
      E8RootNoDuplicates E8.integerRoots

    halfNoDuplicatesNative :
      E8RootNoDuplicates E8.halfRoots

    combinedNoDuplicatesNative :
      E8RootNoDuplicates E8.combinedRoots

    integerHalfDisjointNative :
      E8RootFamiliesDisjoint E8.integerRoots E8.halfRoots

    integerGeneratorCompletenessNative :
      E8IntegerTwoSparseGeneratorCompleteness E8.integerRoots

    halfGeneratorCompletenessNative :
      E8HalfEvenParityGeneratorCompleteness E8.halfRoots

    combinedGeneratorCompletenessNative :
      E8CombinedGeneratorCompleteness E8.combinedRoots

    nativeShapePredicateLayer :
      LilaE8NativeShapePredicateLayer

    nativeShapePredicateLayerDoesNotProveCompleteness :
      LilaE8NativeShapePredicateLayer.generatorShapesPromoteNativeCompleteness
        nativeShapePredicateLayer
      ≡
      false

    provesNativeCompleteness :
      Bool

    provesNativeCompletenessIsFalse :
      provesNativeCompleteness ≡ false

canonicalLilaE8NativeWrapperLayer :
  LilaE8NativeWrapperLayer
canonicalLilaE8NativeWrapperLayer =
  record
    { membershipBridgeAvailable =
        true
    ; membershipBridgeAvailableIsTrue =
        refl
    ; integerNoDuplicatesNative =
        integerRootsNoDuplicatesNativeWrapper
    ; halfNoDuplicatesNative =
        halfRootsNoDuplicatesNativeWrapper
    ; combinedNoDuplicatesNative =
        combinedRootsNoDuplicatesNativeWrapper
    ; integerHalfDisjointNative =
        integerHalfRootsDisjointNativeWrapper
    ; integerGeneratorCompletenessNative =
        integerTwoSparseGeneratorCompletenessNativeWrapper
    ; halfGeneratorCompletenessNative =
        halfEvenParityGeneratorCompletenessNativeWrapper
    ; combinedGeneratorCompletenessNative =
        combinedGeneratorCompletenessNativeWrapper
    ; nativeShapePredicateLayer =
        canonicalLilaE8NativeShapePredicateLayer
    ; nativeShapePredicateLayerDoesNotProveCompleteness =
        refl
    ; provesNativeCompleteness =
        false
    ; provesNativeCompletenessIsFalse =
        refl
    }

data LilaE8NoDuplicatesValidationBoundary : Set where
  validatesIndexedIntegerFamilyNoDuplicates :
    LilaE8NoDuplicatesValidationBoundary
  validatesIndexedHalfFamilyNoDuplicates :
    LilaE8NoDuplicatesValidationBoundary
  validatesIndexedIntegerHalfFamilyDisjointness :
    LilaE8NoDuplicatesValidationBoundary
  validatesIndexedCombinedFamilyNoDuplicates :
    LilaE8NoDuplicatesValidationBoundary
  validatesImageBackedNativeRootMembership :
    LilaE8NoDuplicatesValidationBoundary
  validatesNativeGeneratorCompletenessWrappers :
    LilaE8NoDuplicatesValidationBoundary
  validatesNativeIntegerHalfAndCombinedShapePredicates :
    LilaE8NoDuplicatesValidationBoundary
  validatesGeneratorBackedClassifierInverses :
    LilaE8NoDuplicatesValidationBoundary
  validatesIntegerGeneratorMembershipNormalization :
    LilaE8NoDuplicatesValidationBoundary
  validatesIntegerGeneratorMembershipWitnessTableRows :
    LilaE8NoDuplicatesValidationBoundary
  validatesHalfGeneratorCombinedMembershipNormalization :
    LilaE8NoDuplicatesValidationBoundary
  validatesSemanticNativeFiniteClassifierPredicates :
    LilaE8NoDuplicatesValidationBoundary
  validatesNativeBoolMembershipFiniteReflection :
    LilaE8NoDuplicatesValidationBoundary
  validatesSemanticFiniteMembershipEquivalenceNarrowing :
    LilaE8NoDuplicatesValidationBoundary
  validatesLocalSemanticNativeCompleteness :
    LilaE8NoDuplicatesValidationBoundary
  recordsFiniteMembershipWitnessTableRequest :
    LilaE8NoDuplicatesValidationBoundary
  recordsNativeBoolMembershipToIndexedWitnessRequest :
    LilaE8NoDuplicatesValidationBoundary
  recordsUpstreamCompletenessReceiptPromotionBlocker :
    LilaE8NoDuplicatesValidationBoundary
  recordsUpstreamCompletenessReceiptPromotionBoundary :
    LilaE8NoDuplicatesValidationBoundary
  doesNotValidateNativeCompleteness :
    LilaE8NoDuplicatesValidationBoundary
  doesNotValidateNormInnerProductOrWeylClosure :
    LilaE8NoDuplicatesValidationBoundary
  doesNotPromoteLamTungOrPhiStar :
    LilaE8NoDuplicatesValidationBoundary

canonicalLilaE8NoDuplicatesValidationBoundary :
  List LilaE8NoDuplicatesValidationBoundary
canonicalLilaE8NoDuplicatesValidationBoundary =
  validatesIndexedIntegerFamilyNoDuplicates
  ∷ validatesIndexedHalfFamilyNoDuplicates
  ∷ validatesIndexedIntegerHalfFamilyDisjointness
  ∷ validatesIndexedCombinedFamilyNoDuplicates
  ∷ validatesImageBackedNativeRootMembership
  ∷ validatesNativeGeneratorCompletenessWrappers
  ∷ validatesNativeIntegerHalfAndCombinedShapePredicates
  ∷ validatesGeneratorBackedClassifierInverses
  ∷ validatesIntegerGeneratorMembershipNormalization
  ∷ validatesIntegerGeneratorMembershipWitnessTableRows
  ∷ validatesHalfGeneratorCombinedMembershipNormalization
  ∷ validatesSemanticNativeFiniteClassifierPredicates
  ∷ validatesNativeBoolMembershipFiniteReflection
  ∷ validatesSemanticFiniteMembershipEquivalenceNarrowing
  ∷ validatesLocalSemanticNativeCompleteness
  ∷ recordsFiniteMembershipWitnessTableRequest
  ∷ recordsNativeBoolMembershipToIndexedWitnessRequest
  ∷ recordsUpstreamCompletenessReceiptPromotionBlocker
  ∷ recordsUpstreamCompletenessReceiptPromotionBoundary
  ∷ doesNotValidateNativeCompleteness
  ∷ doesNotValidateNormInnerProductOrWeylClosure
  ∷ doesNotPromoteLamTungOrPhiStar
  ∷ []

data LilaE8NativeCompletenessReceipt : Set where

lilaE8NativeCompletenessReceiptBlockedHere :
  LilaE8NativeCompletenessReceipt →
  ⊥
lilaE8NativeCompletenessReceiptBlockedHere ()

record LilaE8RootEnumerationNoDuplicatesSurface : Setω where
  field
    status :
      LilaE8NoDuplicatesSurfaceStatus

    priorR2Receipt :
      R2.LilaE8RootEnumerationReceiptR2

    priorR2ReceiptIsCountOnly :
      R2.LilaE8RootEnumerationReceiptR2.theoremCompletedHere priorR2Receipt
      ≡
      false

    indexedIntegerRootCount :
      E8.integerIndexedRootsLength
      ≡
      E8.expectedIntegerRootCount

    indexedHalfRootCount :
      E8.halfIndexedRootsLength
      ≡
      E8.expectedHalfRootCount

    indexedCombinedRootCount :
      E8.combinedIndexedRootsLength
      ≡
      E8.expectedTotalRootCount

    integerNoDuplicatesCheck :
      Bool

    integerNoDuplicatesCheckIsTrue :
      integerNoDuplicatesCheck ≡ true

    halfNoDuplicatesCheck :
      Bool

    halfNoDuplicatesCheckIsTrue :
      halfNoDuplicatesCheck ≡ true

    integerHalfDisjointCheck :
      Bool

    integerHalfDisjointCheckIsTrue :
      integerHalfDisjointCheck ≡ true

    allE8RootsNoDuplicatesCheck :
      Bool

    allE8RootsNoDuplicatesCheckIsTrue :
      allE8RootsNoDuplicatesCheck ≡ true

    allE8RootsNoDuplicatesIndexedReceipt :
      E8.IndexedRootNoDuplicates E8.combinedIndexedRoots

    integerHalfDisjointIndexedReceipt :
      E8.IndexedRootFamiliesDisjoint
        E8.integerIndexedRoots
        E8.halfIndexedRoots

    nativeWrapperLayer :
      LilaE8NativeWrapperLayer

    nativeWrapperLayerProvidesMembershipBridge :
      LilaE8NativeWrapperLayer.membershipBridgeAvailable nativeWrapperLayer
      ≡
      true

    nativeWrapperLayerDoesNotProveCompleteness :
      LilaE8NativeWrapperLayer.provesNativeCompleteness nativeWrapperLayer
      ≡
      false

    nativeShapePredicateLayer :
      LilaE8NativeShapePredicateLayer

    nativeShapePredicateLayerFirstMissing :
      List LilaE8NativeCompletenessRefinedFirstMissing

    nativeShapePredicateLayerFirstMissingIsCanonical :
      nativeShapePredicateLayerFirstMissing
      ≡
      canonicalLilaE8NativeCompletenessRefinedFirstMissingAfterHalfCombinedNormalization

    nativeShapePredicateLayerDoesNotProveCompleteness :
      LilaE8NativeShapePredicateLayer.generatorShapesPromoteNativeCompleteness
        nativeShapePredicateLayer
      ≡
      false

    localSemanticNativeCompletenessReceipt :
      E8LocalSemanticNativeCompletenessSurface

    localSemanticNativeCompletenessClearsIntegerHalfCombined :
      E8LocalSemanticNativeCompletenessSurface.integerHalfCombinedCompletenessClearedHere
        localSemanticNativeCompletenessReceipt
      ≡
      true

    nativeCompletenessPromotionBlockers :
      List E8NativeCompletenessPromotionBlocker

    nativeCompletenessPromotionBlockersAreCanonical :
      nativeCompletenessPromotionBlockers
      ≡
      canonicalE8NativeCompletenessPromotionBlockers

    upstreamPromotionBoundary :
      E8LocalSemanticCompletenessUpstreamPromotionBoundary

    upstreamPromotionBoundaryDoesNotPromote :
      E8LocalSemanticCompletenessUpstreamPromotionBoundary.promotionToUpstreamCompleteReceiptImplemented
        upstreamPromotionBoundary
      ≡
      false

    upstreamPromotionBoundaryCompleteReceiptBlocked :
      E8.E8RootEnumerationComplete →
      ⊥

    finiteMembershipWitnessTableRequest :
      E8FiniteMembershipWitnessTableRequest

    finiteMembershipWitnessTableRequestIsCanonical :
      finiteMembershipWitnessTableRequest
      ≡
      canonicalE8FiniteMembershipWitnessTableRequest

    integerGeneratorMembershipWitnessTable :
      E8IntegerGeneratorMembershipWitnessTable

    nativeBoolMembershipToIndexedWitnessRequest :
      E8NativeBoolMembershipToIndexedWitnessRequest

    nativeBoolMembershipToIndexedWitnessRequestIsCanonical :
      nativeBoolMembershipToIndexedWitnessRequest
      ≡
      canonicalE8NativeBoolMembershipToIndexedWitnessRequest

    nativeReflectionBridgeRequest :
      LilaE8NativeReflectionBridgeRequest

    booleanBackedLayer :
      E8.E8BooleanBackedStructuralBridgeLayer

    booleanBackedLayerDoesNotCompleteEnumeration :
      E8.E8BooleanBackedStructuralBridgeLayer.completesE8RootEnumeration
        booleanBackedLayer
      ≡
      false

    firstMissing :
      List LilaE8NoDuplicatesFirstMissing

    firstMissingIsCanonical :
      firstMissing ≡ canonicalLilaE8NoDuplicatesFirstMissing

    validationBoundary :
      List LilaE8NoDuplicatesValidationBoundary

    validationBoundaryIsCanonical :
      validationBoundary ≡ canonicalLilaE8NoDuplicatesValidationBoundary

    theoremCompletedHere :
      Bool

    theoremCompletedHereIsFalse :
      theoremCompletedHere ≡ false

    nativeCompletenessBlocked :
      LilaE8NativeCompletenessReceipt →
      ⊥

    diagnosticNotes :
      List String

canonicalLilaE8RootEnumerationNoDuplicatesSurface :
  LilaE8RootEnumerationNoDuplicatesSurface
canonicalLilaE8RootEnumerationNoDuplicatesSurface =
  record
    { status =
        executableIndexedNoDuplicatesAvailableCompletenessBlocked
    ; priorR2Receipt =
        R2.canonicalLilaE8RootEnumerationReceiptR2
    ; priorR2ReceiptIsCountOnly =
        refl
    ; indexedIntegerRootCount =
        E8.integerIndexedRootsLengthIs112
    ; indexedHalfRootCount =
        E8.halfIndexedRootsLengthIs128
    ; indexedCombinedRootCount =
        E8.combinedIndexedRootsLengthIs240
    ; integerNoDuplicatesCheck =
        E8.integerIndexedRootsNoDuplicatesCheck
    ; integerNoDuplicatesCheckIsTrue =
        E8.integerIndexedRootsNoDuplicatesCheckIsTrue
    ; halfNoDuplicatesCheck =
        E8.halfIndexedRootsNoDuplicatesCheck
    ; halfNoDuplicatesCheckIsTrue =
        E8.halfIndexedRootsNoDuplicatesCheckIsTrue
    ; integerHalfDisjointCheck =
        E8.integerHalfIndexedRootsDisjointCheck
    ; integerHalfDisjointCheckIsTrue =
        E8.integerHalfIndexedRootsDisjointCheckIsTrue
    ; allE8RootsNoDuplicatesCheck =
        E8.combinedIndexedRootsNoDuplicatesCheck
    ; allE8RootsNoDuplicatesCheckIsTrue =
        E8.combinedIndexedRootsNoDuplicatesCheckIsTrue
    ; allE8RootsNoDuplicatesIndexedReceipt =
        E8.combinedIndexedRootsNoDuplicatesBridge
    ; integerHalfDisjointIndexedReceipt =
        E8.integerHalfIndexedRootsDisjointBridge
    ; nativeWrapperLayer =
        canonicalLilaE8NativeWrapperLayer
    ; nativeWrapperLayerProvidesMembershipBridge =
        refl
    ; nativeWrapperLayerDoesNotProveCompleteness =
        refl
    ; nativeShapePredicateLayer =
        canonicalLilaE8NativeShapePredicateLayer
    ; nativeShapePredicateLayerFirstMissing =
        canonicalLilaE8NativeCompletenessRefinedFirstMissingAfterHalfCombinedNormalization
    ; nativeShapePredicateLayerFirstMissingIsCanonical =
        refl
    ; nativeShapePredicateLayerDoesNotProveCompleteness =
        refl
    ; localSemanticNativeCompletenessReceipt =
        localSemanticNativeCompletenessSurface
    ; localSemanticNativeCompletenessClearsIntegerHalfCombined =
        refl
    ; nativeCompletenessPromotionBlockers =
        canonicalE8NativeCompletenessPromotionBlockers
    ; nativeCompletenessPromotionBlockersAreCanonical =
        refl
    ; upstreamPromotionBoundary =
        localSemanticCompletenessUpstreamPromotionBoundary
    ; upstreamPromotionBoundaryDoesNotPromote =
        refl
    ; upstreamPromotionBoundaryCompleteReceiptBlocked =
        E8LocalSemanticCompletenessUpstreamPromotionBoundary.upstreamCompleteReceiptBlocked
          localSemanticCompletenessUpstreamPromotionBoundary
    ; finiteMembershipWitnessTableRequest =
        canonicalE8FiniteMembershipWitnessTableRequest
    ; finiteMembershipWitnessTableRequestIsCanonical =
        refl
    ; integerGeneratorMembershipWitnessTable =
        canonicalE8IntegerGeneratorMembershipWitnessTable
    ; nativeBoolMembershipToIndexedWitnessRequest =
        canonicalE8NativeBoolMembershipToIndexedWitnessRequest
    ; nativeBoolMembershipToIndexedWitnessRequestIsCanonical =
        refl
    ; nativeReflectionBridgeRequest =
        canonicalLilaE8NativeReflectionBridgeRequest
    ; booleanBackedLayer =
        E8.canonicalE8BooleanBackedStructuralBridgeLayer
    ; booleanBackedLayerDoesNotCompleteEnumeration =
        refl
    ; firstMissing =
        canonicalLilaE8NoDuplicatesFirstMissing
    ; firstMissingIsCanonical =
        refl
    ; validationBoundary =
        canonicalLilaE8NoDuplicatesValidationBoundary
    ; validationBoundaryIsCanonical =
        refl
    ; theoremCompletedHere =
        false
    ; theoremCompletedHereIsFalse =
        refl
    ; nativeCompletenessBlocked =
        lilaE8NativeCompletenessReceiptBlockedHere
    ; diagnosticNotes =
        "The combined indexed E8 root list computes length 240 and no-duplicates = true"
        ∷ "The integer indexed family computes length 112 and no-duplicates = true"
        ∷ "The half indexed family computes length 128 and no-duplicates = true"
        ∷ "The integer and half indexed families compute disjoint = true"
        ∷ "This sidecar now provides indexed-image-backed native wrappers for E8RootMember, E8RootNoDuplicates, and E8RootFamiliesDisjoint"
        ∷ "Generator-completeness wrappers are available for integer, half, and combined root lists"
        ∷ "Native shape predicates are available for integer two-sparse roots, half even-parity roots, and their combined family"
        ∷ "Generator-backed classifier inverses now extract integer generators, half generators, and combined integer/half cases"
        ∷ "Integer generator membership now normalizes into the executable indexed integer root list by finite case split over 28 coordinate pairs and four sign choices"
        ∷ "Integer generator-indexed witness table rows now carry pair/sign, native membership, indexed membership, and classifier witnesses"
        ∷ "Half generator membership now normalizes into the half family by carried membership and into the combined family by append-right membership"
        ∷ "Combined classifier cases now normalize to native membership in the combined root list"
        ∷ "Semantic native classifier predicates for arbitrary roots are now finite native-list membership predicates over integer, half, and combined roots"
        ∷ "Bool finite membership now reflects to and from E8NativeFiniteRootMember, and indexed bool membership reflects to E8.IndexedRootMember"
        ∷ "Indexed root generator-shape inversion now recovers integer pair/sign, half sign-vector, and combined integer/half shape records from proof-relevant indexed membership"
        ∷ "A finite membership witness table request now names the exact needed root, generator-index, indexed-image equality, indexed membership, and proof fields"
        ∷ "Semantic finite native membership now converts through indexed-image lookup and generator-shape inversion to witness-carrying integer, half, and combined classifier cases"
        ∷ "Local semantic integer, half, and combined completeness now converts finite native membership into existing generator-indexed witnesses"
        ∷ "The local semantic completeness surface is wired to the upstream E8RootEnumerationObstruction; its remainingConcreteProofObligations and remainingEnumerationObligations are still canonical, and E8RootEnumerationComplete is empty here"
        ∷ "The remaining E8/LILA completeness blocker is promotion from that local finite semantic surface to the upstream empty E8RootEnumerationComplete receipt"
        ∷ "No LILA-R3, Lam-Tung, phi-star, or publication promotion is claimed here"
        ∷ []
    }

canonicalLilaE8NoDuplicatesSurfaceCompletedHere :
  Bool
canonicalLilaE8NoDuplicatesSurfaceCompletedHere =
  LilaE8RootEnumerationNoDuplicatesSurface.theoremCompletedHere
    canonicalLilaE8RootEnumerationNoDuplicatesSurface

canonicalLilaE8NoDuplicatesSurfaceCompletedHereIsFalse :
  canonicalLilaE8NoDuplicatesSurfaceCompletedHere ≡ false
canonicalLilaE8NoDuplicatesSurfaceCompletedHereIsFalse =
  refl
