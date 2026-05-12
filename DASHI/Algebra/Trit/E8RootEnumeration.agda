module DASHI.Algebra.Trit.E8RootEnumeration where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Vec using (Vec)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.Trit.HalfTrit as HT
import DASHI.Physics.Closure.LilaE8RootEnumerationReceiptR2 as R2

------------------------------------------------------------------------
-- LILA-R2 HalfTrit / E8 root-enumeration obstruction.
--
-- The algebra namespace has the balanced ternary carrier
-- DASHI.Algebra.Trit.Trit and a five-point HalfTrit carrier.  HalfTrit is
-- enough to fix the coordinate API, but the lane still lacks the root
-- enumerators, equality decision, no-duplicate/cardinality bridges, and
-- completeness proof needed to turn the existing R2 count-support surface into
-- a constructive 240-root enumeration receipt.

EightVec : Set → Set
EightVec A = Vec A 8

data E8RootEnumerationStatus : Set where
  blockedOnHalfTritInterface :
    E8RootEnumerationStatus
  blockedOnEnumerationCardinalityMachinery :
    E8RootEnumerationStatus

data HalfTritInterfaceMissing : Set where
  missingHalfTritCarrier :
    HalfTritInterfaceMissing
  missingNegativeHalfConstructor :
    HalfTritInterfaceMissing
  missingPositiveHalfConstructor :
    HalfTritInterfaceMissing
  missingDoubledZeroConstructor :
    HalfTritInterfaceMissing
  missingDoubledMinusTwoConstructor :
    HalfTritInterfaceMissing
  missingDoubledPlusTwoConstructor :
    HalfTritInterfaceMissing
  missingEightCoordinateVectorCarrier :
    HalfTritInterfaceMissing
  missingRootEqualityDecision :
    HalfTritInterfaceMissing
  missingDuplicateFreedomLemma :
    HalfTritInterfaceMissing
  missingCompletenessLemma :
    HalfTritInterfaceMissing
  missingVecLengthCardinalityBridge :
    HalfTritInterfaceMissing
  missingListNoDuplicateCardinalityBridge :
    HalfTritInterfaceMissing

canonicalHalfTritInterfaceMissing :
  List HalfTritInterfaceMissing
canonicalHalfTritInterfaceMissing =
  missingRootEqualityDecision
  ∷ missingDuplicateFreedomLemma
  ∷ missingCompletenessLemma
  ∷ missingVecLengthCardinalityBridge
  ∷ missingListNoDuplicateCardinalityBridge
  ∷ []

data E8DoubledCoordinateFamilyShape : Set where
  integerTwoSparseShape :
    E8DoubledCoordinateFamilyShape
  halfAllSignedOddUnitShape :
    E8DoubledCoordinateFamilyShape

canonicalE8DoubledCoordinateFamilyShapes :
  List E8DoubledCoordinateFamilyShape
canonicalE8DoubledCoordinateFamilyShapes =
  integerTwoSparseShape
  ∷ halfAllSignedOddUnitShape
  ∷ []

data E8IntegerRootShapeField : Set where
  integerRootUsesEightCoordinates :
    E8IntegerRootShapeField
  integerRootHasExactlyTwoNonzeroCoordinates :
    E8IntegerRootShapeField
  integerRootNonzeroCoordinatesAreDoubledPlusOrMinusTwo :
    E8IntegerRootShapeField
  integerRootRangesOverAllCoordinatePairs :
    E8IntegerRootShapeField
  integerRootRangesOverAllFourSignChoices :
    E8IntegerRootShapeField

canonicalE8IntegerRootShapeFields :
  List E8IntegerRootShapeField
canonicalE8IntegerRootShapeFields =
  integerRootUsesEightCoordinates
  ∷ integerRootHasExactlyTwoNonzeroCoordinates
  ∷ integerRootNonzeroCoordinatesAreDoubledPlusOrMinusTwo
  ∷ integerRootRangesOverAllCoordinatePairs
  ∷ integerRootRangesOverAllFourSignChoices
  ∷ []

data E8HalfRootShapeField : Set where
  halfRootUsesEightCoordinates :
    E8HalfRootShapeField
  halfRootEveryCoordinateIsDoubledPlusOrMinusOne :
    E8HalfRootShapeField
  halfRootHasEvenMinusParity :
    E8HalfRootShapeField
  halfRootRangesOverAllEvenParitySignVectors :
    E8HalfRootShapeField
  halfRootCountUsesParitySplitOfTwoToTheEight :
    E8HalfRootShapeField

canonicalE8HalfRootShapeFields :
  List E8HalfRootShapeField
canonicalE8HalfRootShapeFields =
  halfRootUsesEightCoordinates
  ∷ halfRootEveryCoordinateIsDoubledPlusOrMinusOne
  ∷ halfRootHasEvenMinusParity
  ∷ halfRootRangesOverAllEvenParitySignVectors
  ∷ halfRootCountUsesParitySplitOfTwoToTheEight
  ∷ []

data E8EnumerationCardinalityMachinery : Set where
  listLengthFunction :
    E8EnumerationCardinalityMachinery
  vecEightCoordinateCarrier :
    E8EnumerationCardinalityMachinery
  decidableRootEquality :
    E8EnumerationCardinalityMachinery
  noDuplicateListPredicate :
    E8EnumerationCardinalityMachinery
  noDuplicateImpliesLengthIsCardinality :
    E8EnumerationCardinalityMachinery
  integerPairAndSignCountProof :
    E8EnumerationCardinalityMachinery
  halfParitySplitCountProof :
    E8EnumerationCardinalityMachinery
  appendDisjointFamilyCountProof :
    E8EnumerationCardinalityMachinery

canonicalE8EnumerationCardinalityMachinery :
  List E8EnumerationCardinalityMachinery
canonicalE8EnumerationCardinalityMachinery =
  listLengthFunction
  ∷ vecEightCoordinateCarrier
  ∷ decidableRootEquality
  ∷ noDuplicateListPredicate
  ∷ noDuplicateImpliesLengthIsCardinality
  ∷ integerPairAndSignCountProof
  ∷ halfParitySplitCountProof
  ∷ appendDisjointFamilyCountProof
  ∷ []

data E8RootEnumerationObligation : Set where
  integerFamily112 :
    E8RootEnumerationObligation
  halfFamily128 :
    E8RootEnumerationObligation
  totalFamily240 :
    E8RootEnumerationObligation
  allRootsHaveEightCoordinates :
    E8RootEnumerationObligation
  integerRootsArePairwisePlusMinusTwo :
    E8RootEnumerationObligation
  halfRootsAreAllPlusMinusOneWithEvenMinusParity :
    E8RootEnumerationObligation
  familiesAreDisjoint :
    E8RootEnumerationObligation
  noDuplicateRoots :
    E8RootEnumerationObligation
  enumerationIsComplete :
    E8RootEnumerationObligation

canonicalE8RootEnumerationObligations :
  List E8RootEnumerationObligation
canonicalE8RootEnumerationObligations =
  integerFamily112
  ∷ halfFamily128
  ∷ totalFamily240
  ∷ allRootsHaveEightCoordinates
  ∷ integerRootsArePairwisePlusMinusTwo
  ∷ halfRootsAreAllPlusMinusOneWithEvenMinusParity
  ∷ familiesAreDisjoint
  ∷ noDuplicateRoots
  ∷ enumerationIsComplete
  ∷ []

expectedIntegerRootCount : Nat
expectedIntegerRootCount = 112

expectedHalfRootCount : Nat
expectedHalfRootCount = 128

expectedTotalRootCount : Nat
expectedTotalRootCount = 240

data E8RootEnumerationComplete : Set where

e8RootEnumerationCompleteImpossibleHere :
  E8RootEnumerationComplete →
  ⊥
e8RootEnumerationCompleteImpossibleHere ()

record E8RootEnumerationObstruction : Setω where
  field
    status :
      E8RootEnumerationStatus

    availableTritCarrier :
      Set

    availableTritNegative :
      availableTritCarrier

    availableTritZero :
      availableTritCarrier

    availableTritPositive :
      availableTritCarrier

    availableHalfTritReceipt :
      HT.HalfTritComplete

    availableHalfTritCarrier :
      Set

    availableHalfTritNegativeOne :
      availableHalfTritCarrier

    availableHalfTritNegativeHalf :
      availableHalfTritCarrier

    availableHalfTritZero :
      availableHalfTritCarrier

    availableHalfTritPositiveHalf :
      availableHalfTritCarrier

    availableHalfTritPositiveOne :
      availableHalfTritCarrier

    halfTritDoesNotConstructE8Enumeration :
      HT.HalfTritComplete.constructsE8RootEnumeration availableHalfTritReceipt
      ≡
      false

    preparedEightCoordinateCarrierShape :
      Set → Set

    preparedHalfTritRootCarrier :
      Set

    upstreamR2CountReceipt :
      R2.LilaE8RootEnumerationReceiptR2

    upstreamR2CountOnly :
      R2.LilaE8RootEnumerationReceiptR2.theoremCompletedHere
        upstreamR2CountReceipt
      ≡
      false

    expectedIntegerRoots :
      Nat

    expectedIntegerRootsIs112 :
      expectedIntegerRoots ≡ expectedIntegerRootCount

    expectedHalfRoots :
      Nat

    expectedHalfRootsIs128 :
      expectedHalfRoots ≡ expectedHalfRootCount

    expectedTotalRoots :
      Nat

    expectedTotalRootsIs240 :
      expectedTotalRoots ≡ expectedTotalRootCount

    preparedFamilyShapes :
      List E8DoubledCoordinateFamilyShape

    preparedFamilyShapesAreCanonical :
      preparedFamilyShapes ≡ canonicalE8DoubledCoordinateFamilyShapes

    preparedIntegerFamilyShape :
      List E8IntegerRootShapeField

    preparedIntegerFamilyShapeIsCanonical :
      preparedIntegerFamilyShape ≡ canonicalE8IntegerRootShapeFields

    preparedHalfFamilyShape :
      List E8HalfRootShapeField

    preparedHalfFamilyShapeIsCanonical :
      preparedHalfFamilyShape ≡ canonicalE8HalfRootShapeFields

    requiredCardinalityMachinery :
      List E8EnumerationCardinalityMachinery

    requiredCardinalityMachineryIsCanonical :
      requiredCardinalityMachinery ≡ canonicalE8EnumerationCardinalityMachinery

    missingHalfTritInterface :
      List HalfTritInterfaceMissing

    missingHalfTritInterfaceIsCanonical :
      missingHalfTritInterface ≡ canonicalHalfTritInterfaceMissing

    remainingEnumerationObligations :
      List E8RootEnumerationObligation

    remainingEnumerationObligationsAreCanonical :
      remainingEnumerationObligations ≡ canonicalE8RootEnumerationObligations

    receiptCompletedHere :
      Bool

    receiptCompletedHereIsFalse :
      receiptCompletedHere ≡ false

    obstructionNotes :
      List String

    flipWhenHalfTritLands :
      List String

    completeReceiptBlocked :
      E8RootEnumerationComplete →
      ⊥

canonicalE8RootEnumerationObstruction :
  E8RootEnumerationObstruction
canonicalE8RootEnumerationObstruction =
  record
    { status =
        blockedOnEnumerationCardinalityMachinery
    ; availableTritCarrier =
        Trit.Trit
    ; availableTritNegative =
        Trit.neg
    ; availableTritZero =
        Trit.zer
    ; availableTritPositive =
        Trit.pos
    ; availableHalfTritReceipt =
        HT.canonicalHalfTritComplete
    ; availableHalfTritCarrier =
        HT.HalfTrit
    ; availableHalfTritNegativeOne =
        HT.negOne
    ; availableHalfTritNegativeHalf =
        HT.negHalf
    ; availableHalfTritZero =
        HT.zero
    ; availableHalfTritPositiveHalf =
        HT.posHalf
    ; availableHalfTritPositiveOne =
        HT.posOne
    ; halfTritDoesNotConstructE8Enumeration =
        refl
    ; preparedEightCoordinateCarrierShape =
        EightVec
    ; preparedHalfTritRootCarrier =
        EightVec HT.HalfTrit
    ; upstreamR2CountReceipt =
        R2.canonicalLilaE8RootEnumerationReceiptR2
    ; upstreamR2CountOnly =
        refl
    ; expectedIntegerRoots =
        expectedIntegerRootCount
    ; expectedIntegerRootsIs112 =
        refl
    ; expectedHalfRoots =
        expectedHalfRootCount
    ; expectedHalfRootsIs128 =
        refl
    ; expectedTotalRoots =
        expectedTotalRootCount
    ; expectedTotalRootsIs240 =
        refl
    ; preparedFamilyShapes =
        canonicalE8DoubledCoordinateFamilyShapes
    ; preparedFamilyShapesAreCanonical =
        refl
    ; preparedIntegerFamilyShape =
        canonicalE8IntegerRootShapeFields
    ; preparedIntegerFamilyShapeIsCanonical =
        refl
    ; preparedHalfFamilyShape =
        canonicalE8HalfRootShapeFields
    ; preparedHalfFamilyShapeIsCanonical =
        refl
    ; requiredCardinalityMachinery =
        canonicalE8EnumerationCardinalityMachinery
    ; requiredCardinalityMachineryIsCanonical =
        refl
    ; missingHalfTritInterface =
        canonicalHalfTritInterfaceMissing
    ; missingHalfTritInterfaceIsCanonical =
        refl
    ; remainingEnumerationObligations =
        canonicalE8RootEnumerationObligations
    ; remainingEnumerationObligationsAreCanonical =
        refl
    ; receiptCompletedHere =
        false
    ; receiptCompletedHereIsFalse =
        refl
    ; obstructionNotes =
        "DASHI.Algebra.Trit exposes Trit with neg/zer/pos"
        ∷ "DASHI.Algebra.Trit.HalfTrit exposes HalfTrit with negOne/negHalf/zero/posHalf/posOne"
        ∷ "HalfTrit.canonicalHalfTritComplete records constructsE8RootEnumeration = false"
        ∷ "The preflight root-carrier shape is EightVec HalfTrit"
        ∷ "The existing LILA-R2 receipt records count support only and theoremCompletedHere = false"
        ∷ "The integer family shape is two nonzero doubled +/-2 coordinates over all coordinate pairs and sign choices"
        ∷ "The half family shape is all eight-coordinate doubled +/-1 sign vectors with even minus parity"
        ∷ "A complete receipt still needs enumerators, decidable equality, duplicate freedom, cardinality bridges, and completeness"
        ∷ []
    ; flipWhenHalfTritLands =
        "HalfTrit is available locally; keep importing it without redefining it here"
        ∷ "Use EightVec HalfTrit as the root carrier shape"
        ∷ "Build integerRoots : List (EightVec HalfTrit) with length/cardinality 112"
        ∷ "Build halfRoots : List (EightVec HalfTrit) with length/cardinality 128"
        ∷ "Prove decidable equality, no duplicates within each family, disjointness across families, and appended count 240"
        ∷ "Only then replace this obstruction with an E8RootEnumerationComplete receipt"
        ∷ []
    ; completeReceiptBlocked =
        e8RootEnumerationCompleteImpossibleHere
    }

LILA-R2Obstruction :
  E8RootEnumerationObstruction
LILA-R2Obstruction =
  canonicalE8RootEnumerationObstruction

lilaR2ReceiptCannotBeInhabitedHere :
  E8RootEnumerationComplete →
  ⊥
lilaR2ReceiptCannotBeInhabitedHere =
  E8RootEnumerationObstruction.completeReceiptBlocked LILA-R2Obstruction
