module DASHI.Algebra.Trit.E8RootEnumeration where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base as List using (List; _∷_; []; length; _++_)
open import Data.Vec using (Vec)
import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality using (cong)
open import Relation.Nullary using (Dec)
open import Relation.Nullary using (yes; no)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.Trit.HalfTrit as HT
import DASHI.Algebra.Trit.HalfTritIndexed as HTI
import DASHI.Physics.Closure.LilaE8RootEnumerationReceiptR2 as R2

------------------------------------------------------------------------
-- LILA-R2 HalfTrit / E8 root-enumeration obstruction.
--
-- The algebra namespace has the balanced ternary carrier
-- DASHI.Algebra.Trit.Trit and a five-point HalfTrit carrier.  HalfTrit is
-- enough to fix the coordinate API.  This module now stages concrete finite
-- integer/half-family lists and normalized length surfaces, but still lacks
-- root membership/equality, no-duplicate/disjointness, parity-soundness, and
-- completeness proofs needed to turn the existing R2 count-support surface
-- into a constructive 240-root enumeration receipt.

EightVec : Set → Set
EightVec A = Vec A 8

E8RootCarrier : Set
E8RootCarrier = EightVec HT.HalfTrit

E8RootList : Set
E8RootList = List E8RootCarrier

E8IndexedRootCarrier : Set
E8IndexedRootCarrier = EightVec HTI.HalfTritIndexed

E8IndexedRootList : Set
E8IndexedRootList = List E8IndexedRootCarrier

rootListLength : E8RootList → Nat
rootListLength = length

indexedRootListLength : E8IndexedRootList → Nat
indexedRootListLength = length

data E8RootEnumerationStatus : Set where
  blockedOnHalfTritInterface :
    E8RootEnumerationStatus
  blockedOnEnumerationCardinalityMachinery :
    E8RootEnumerationStatus

data HalfTritIndexedSurfaceStatus : Set where
  halfTritIndexedSurfaceNotFound :
    HalfTritIndexedSurfaceStatus
  halfTritIndexedSurfaceAvailable :
    HalfTritIndexedSurfaceStatus

data RequiredHalfTritIndexedField : Set where
  indexedHalfTritCarrier :
    RequiredHalfTritIndexedField
  indexedHalfTritToFin :
    RequiredHalfTritIndexedField
  indexedFinToHalfTrit :
    RequiredHalfTritIndexedField
  indexedRoundTripLaws :
    RequiredHalfTritIndexedField
  indexedHalfTritDecidableEquality :
    RequiredHalfTritIndexedField
  indexedAllHalfTritValues :
    RequiredHalfTritIndexedField
  indexedAllHalfTritValuesLengthFive :
    RequiredHalfTritIndexedField
  indexedAllHalfTritValuesNoDuplicates :
    RequiredHalfTritIndexedField

canonicalRequiredHalfTritIndexedFields :
  List RequiredHalfTritIndexedField
canonicalRequiredHalfTritIndexedFields =
  indexedHalfTritCarrier
  ∷ indexedHalfTritToFin
  ∷ indexedFinToHalfTrit
  ∷ indexedRoundTripLaws
  ∷ indexedHalfTritDecidableEquality
  ∷ indexedAllHalfTritValues
  ∷ indexedAllHalfTritValuesLengthFive
  ∷ indexedAllHalfTritValuesNoDuplicates
  ∷ []

data AvailableHalfTritIndexedField : Set where
  availableIndexedHalfTritCarrier :
    AvailableHalfTritIndexedField
  availableIndexedHalfTritToFin :
    AvailableHalfTritIndexedField
  availableIndexedFinToHalfTrit :
    AvailableHalfTritIndexedField
  availableIndexedRoundTripLaws :
    AvailableHalfTritIndexedField
  availableIndexedHalfTritDecidableEquality :
    AvailableHalfTritIndexedField
  availableIndexedAllHalfTritValues :
    AvailableHalfTritIndexedField
  availableIndexedAllHalfTritValuesLengthFive :
    AvailableHalfTritIndexedField
  availableIndexedAllHalfTritValuesNoDuplicates :
    AvailableHalfTritIndexedField
  availableIndexedHalfTritEmbedding :
    AvailableHalfTritIndexedField
  availableIndexedHalfTritEmbeddingInjective :
    AvailableHalfTritIndexedField
  availableIndexedCoordinateDuplicateFreedomReceipt :
    AvailableHalfTritIndexedField
  availableIndexedEightCoordinateCarrier :
    AvailableHalfTritIndexedField
  availableIndexedRootListCarrier :
    AvailableHalfTritIndexedField

canonicalAvailableHalfTritIndexedFields :
  List AvailableHalfTritIndexedField
canonicalAvailableHalfTritIndexedFields =
  availableIndexedHalfTritCarrier
  ∷ availableIndexedHalfTritToFin
  ∷ availableIndexedFinToHalfTrit
  ∷ availableIndexedRoundTripLaws
  ∷ availableIndexedHalfTritDecidableEquality
  ∷ availableIndexedAllHalfTritValues
  ∷ availableIndexedAllHalfTritValuesLengthFive
  ∷ availableIndexedAllHalfTritValuesNoDuplicates
  ∷ availableIndexedHalfTritEmbedding
  ∷ availableIndexedHalfTritEmbeddingInjective
  ∷ availableIndexedCoordinateDuplicateFreedomReceipt
  ∷ availableIndexedEightCoordinateCarrier
  ∷ availableIndexedRootListCarrier
  ∷ []

data AvailableCardinalityPrimitive : Set where
  natPrimitiveAvailable :
    AvailableCardinalityPrimitive
  listPrimitiveAvailable :
    AvailableCardinalityPrimitive
  listLengthFunctionAvailable :
    AvailableCardinalityPrimitive
  vecPrimitiveAvailable :
    AvailableCardinalityPrimitive
  vecEightRootCarrierShapeAvailable :
    AvailableCardinalityPrimitive

canonicalAvailableCardinalityPrimitives :
  List AvailableCardinalityPrimitive
canonicalAvailableCardinalityPrimitives =
  natPrimitiveAvailable
  ∷ listPrimitiveAvailable
  ∷ listLengthFunctionAvailable
  ∷ vecPrimitiveAvailable
  ∷ vecEightRootCarrierShapeAvailable
  ∷ []

data ConcreteE8CardinalityWitnessMissing : Set where
  missingIntegerRootMembershipDecision :
    ConcreteE8CardinalityWitnessMissing
  missingIntegerRootNoDuplicates :
    ConcreteE8CardinalityWitnessMissing
  missingIntegerRootCompleteness :
    ConcreteE8CardinalityWitnessMissing
  missingHalfRootMembershipDecision :
    ConcreteE8CardinalityWitnessMissing
  missingHalfRootEvenParityProof :
    ConcreteE8CardinalityWitnessMissing
  missingHalfRootNoDuplicates :
    ConcreteE8CardinalityWitnessMissing
  missingHalfRootCompleteness :
    ConcreteE8CardinalityWitnessMissing
  missingFamilyDisjointness :
    ConcreteE8CardinalityWitnessMissing
  missingCombinedRootNoDuplicates :
    ConcreteE8CardinalityWitnessMissing
  missingCombinedCompleteness :
    ConcreteE8CardinalityWitnessMissing

canonicalConcreteE8CardinalityWitnessMissing :
  List ConcreteE8CardinalityWitnessMissing
canonicalConcreteE8CardinalityWitnessMissing =
  missingIntegerRootMembershipDecision
  ∷ missingIntegerRootNoDuplicates
  ∷ missingIntegerRootCompleteness
  ∷ missingHalfRootMembershipDecision
  ∷ missingHalfRootEvenParityProof
  ∷ missingHalfRootNoDuplicates
  ∷ missingHalfRootCompleteness
  ∷ missingFamilyDisjointness
  ∷ missingCombinedRootNoDuplicates
  ∷ missingCombinedCompleteness
  ∷ []

data AvailableConcreteE8Generator : Set where
  availableCoordinatePair28List :
    AvailableConcreteE8Generator
  availableIntegerIndexedRootGenerator :
    AvailableConcreteE8Generator
  availableIntegerIndexedRootList112 :
    AvailableConcreteE8Generator
  availableIntegerHalfTritRootList112 :
    AvailableConcreteE8Generator
  availableHalfIndexedEvenSignVectorGenerator :
    AvailableConcreteE8Generator
  availableHalfIndexedRootList128 :
    AvailableConcreteE8Generator
  availableHalfTritRootList128 :
    AvailableConcreteE8Generator
  availableCombinedIndexedRootList240 :
    AvailableConcreteE8Generator
  availableCombinedHalfTritRootList240 :
    AvailableConcreteE8Generator

canonicalAvailableConcreteE8Generators :
  List AvailableConcreteE8Generator
canonicalAvailableConcreteE8Generators =
  availableCoordinatePair28List
  ∷ availableIntegerIndexedRootGenerator
  ∷ availableIntegerIndexedRootList112
  ∷ availableIntegerHalfTritRootList112
  ∷ availableHalfIndexedEvenSignVectorGenerator
  ∷ availableHalfIndexedRootList128
  ∷ availableHalfTritRootList128
  ∷ availableCombinedIndexedRootList240
  ∷ availableCombinedHalfTritRootList240
  ∷ []

data AvailableConcreteE8ProofLayer : Set where
  availableIndexedRootDecidableEquality :
    AvailableConcreteE8ProofLayer
  availableIndexedRootMembershipCheck :
    AvailableConcreteE8ProofLayer
  availableIntegerIndexedRootNoDuplicateCheck :
    AvailableConcreteE8ProofLayer
  availableHalfIndexedRootNoDuplicateCheck :
    AvailableConcreteE8ProofLayer
  availableIntegerHalfFamilyDisjointCheck :
    AvailableConcreteE8ProofLayer
  availableCombinedIndexedRootNoDuplicateCheck :
    AvailableConcreteE8ProofLayer
  availableHalfRootEvenParityByConstruction :
    AvailableConcreteE8ProofLayer
  availableBooleanBackedIndexedMembershipBridge :
    AvailableConcreteE8ProofLayer
  availableBooleanBackedNoDuplicateBridge :
    AvailableConcreteE8ProofLayer
  availableBooleanBackedDisjointnessBridge :
    AvailableConcreteE8ProofLayer
  availableBooleanBackedHalfParityBridge :
    AvailableConcreteE8ProofLayer

canonicalAvailableConcreteE8ProofLayer :
  List AvailableConcreteE8ProofLayer
canonicalAvailableConcreteE8ProofLayer =
  availableIndexedRootDecidableEquality
  ∷ availableIndexedRootMembershipCheck
  ∷ availableIntegerIndexedRootNoDuplicateCheck
  ∷ availableHalfIndexedRootNoDuplicateCheck
  ∷ availableIntegerHalfFamilyDisjointCheck
  ∷ availableCombinedIndexedRootNoDuplicateCheck
  ∷ availableHalfRootEvenParityByConstruction
  ∷ availableBooleanBackedIndexedMembershipBridge
  ∷ availableBooleanBackedNoDuplicateBridge
  ∷ availableBooleanBackedDisjointnessBridge
  ∷ availableBooleanBackedHalfParityBridge
  ∷ []

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

data E8Sign : Set where
  negativeSign :
    E8Sign
  positiveSign :
    E8Sign

_≟E8Sign_ :
  (x y : E8Sign) →
  Dec (x ≡ y)
negativeSign ≟E8Sign negativeSign =
  yes refl
negativeSign ≟E8Sign positiveSign =
  no (λ ())
positiveSign ≟E8Sign negativeSign =
  no (λ ())
positiveSign ≟E8Sign positiveSign =
  yes refl

decEqIndexedRoot :
  {n : Nat} →
  (x y : Vec HTI.HalfTritIndexed n) →
  Dec (x ≡ y)
decEqIndexedRoot Vec.[] Vec.[] =
  yes refl
decEqIndexedRoot (x Vec.∷ xs) (y Vec.∷ ys)
  with HTI._≟Indexed_ x y
... | no neq =
  no (λ eq → neq (cong Vec.head eq))
... | yes refl
  with decEqIndexedRoot xs ys
... | no neq =
  no (λ eq → neq (cong Vec.tail eq))
... | yes refl =
  yes refl

memberIndexedRoot :
  {n : Nat} →
  Vec HTI.HalfTritIndexed n →
  List (Vec HTI.HalfTritIndexed n) →
  Bool
memberIndexedRoot x [] =
  false
memberIndexedRoot x (y ∷ ys)
  with decEqIndexedRoot x y
... | yes _ =
  true
... | no _ =
  memberIndexedRoot x ys

noDuplicatesIndexedRootList :
  {n : Nat} →
  List (Vec HTI.HalfTritIndexed n) →
  Bool
noDuplicatesIndexedRootList [] =
  true
noDuplicatesIndexedRootList (x ∷ xs)
  with memberIndexedRoot x xs
... | true =
  false
... | false =
  noDuplicatesIndexedRootList xs

disjointIndexedRootLists :
  {n : Nat} →
  List (Vec HTI.HalfTritIndexed n) →
  List (Vec HTI.HalfTritIndexed n) →
  Bool
disjointIndexedRootLists [] ys =
  true
disjointIndexedRootLists (x ∷ xs) ys
  with memberIndexedRoot x ys
... | true =
  false
... | false =
  disjointIndexedRootLists xs ys

allE8Signs :
  List E8Sign
allE8Signs =
  negativeSign
  ∷ positiveSign
  ∷ []

integerSignCoordinate :
  E8Sign →
  HTI.HalfTritIndexed
integerSignCoordinate negativeSign =
  HTI.indexedNegOne
integerSignCoordinate positiveSign =
  HTI.indexedPosOne

halfSignCoordinate :
  E8Sign →
  HTI.HalfTritIndexed
halfSignCoordinate negativeSign =
  HTI.indexedNegHalf
halfSignCoordinate positiveSign =
  HTI.indexedPosHalf

indexedToHalfTrit :
  HTI.HalfTritIndexed →
  HT.HalfTrit
indexedToHalfTrit HTI.indexedNegOne =
  HT.negOne
indexedToHalfTrit HTI.indexedNegHalf =
  HT.negHalf
indexedToHalfTrit HTI.indexedZero =
  HT.zero
indexedToHalfTrit HTI.indexedPosHalf =
  HT.posHalf
indexedToHalfTrit HTI.indexedPosOne =
  HT.posOne

indexedRootToHalfTritRoot :
  E8IndexedRootCarrier →
  E8RootCarrier
indexedRootToHalfTritRoot =
  Vec.map indexedToHalfTrit

infixr 5 _∷ᵥ_

_∷ᵥ_ :
  {A : Set} {n : Nat} →
  A →
  Vec A n →
  Vec A (suc n)
_∷ᵥ_ =
  Vec._∷_

[]ᵥ :
  {A : Set} →
  Vec A zero
[]ᵥ =
  Vec.[]

data CoordinatePair8 : Set where
  pair01 pair02 pair03 pair04 pair05 pair06 pair07 :
    CoordinatePair8
  pair12 pair13 pair14 pair15 pair16 pair17 :
    CoordinatePair8
  pair23 pair24 pair25 pair26 pair27 :
    CoordinatePair8
  pair34 pair35 pair36 pair37 :
    CoordinatePair8
  pair45 pair46 pair47 :
    CoordinatePair8
  pair56 pair57 :
    CoordinatePair8
  pair67 :
    CoordinatePair8

allCoordinatePairs8 :
  List CoordinatePair8
allCoordinatePairs8 =
  pair01 ∷ pair02 ∷ pair03 ∷ pair04 ∷ pair05 ∷ pair06 ∷ pair07
  ∷ pair12 ∷ pair13 ∷ pair14 ∷ pair15 ∷ pair16 ∷ pair17
  ∷ pair23 ∷ pair24 ∷ pair25 ∷ pair26 ∷ pair27
  ∷ pair34 ∷ pair35 ∷ pair36 ∷ pair37
  ∷ pair45 ∷ pair46 ∷ pair47
  ∷ pair56 ∷ pair57
  ∷ pair67
  ∷ []

allCoordinatePairs8Length :
  length allCoordinatePairs8 ≡ 28
allCoordinatePairs8Length =
  refl

zᵢ :
  HTI.HalfTritIndexed
zᵢ =
  HTI.indexedZero

mkIntegerIndexedRoot :
  CoordinatePair8 →
  E8Sign →
  E8Sign →
  E8IndexedRootCarrier
mkIntegerIndexedRoot pair01 s t =
  integerSignCoordinate s ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair02 s t =
  integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair03 s t =
  integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair04 s t =
  integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair05 s t =
  integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair06 s t =
  integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair07 s t =
  integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair12 s t =
  zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair13 s t =
  zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair14 s t =
  zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair15 s t =
  zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair16 s t =
  zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair17 s t =
  zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair23 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ integerSignCoordinate t ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair24 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ
  integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair25 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair26 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair27 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair34 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ
  integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair35 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ
  zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair36 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair37 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair45 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  integerSignCoordinate s ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair46 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair47 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair56 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ integerSignCoordinate t ∷ᵥ zᵢ ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair57 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate t ∷ᵥ []ᵥ
mkIntegerIndexedRoot pair67 s t =
  zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ zᵢ ∷ᵥ
  zᵢ ∷ᵥ zᵢ ∷ᵥ integerSignCoordinate s ∷ᵥ integerSignCoordinate t ∷ᵥ []ᵥ

integerIndexedRootsForPair :
  CoordinatePair8 →
  E8IndexedRootList
integerIndexedRootsForPair p =
  List.concatMap
    (λ s →
      List.map
        (λ t → mkIntegerIndexedRoot p s t)
        allE8Signs)
    allE8Signs

integerIndexedRoots :
  E8IndexedRootList
integerIndexedRoots =
  List.concatMap integerIndexedRootsForPair allCoordinatePairs8

integerIndexedRootsLength :
  Nat
integerIndexedRootsLength =
  indexedRootListLength integerIndexedRoots

integerIndexedRootsLengthIs112 :
  integerIndexedRootsLength ≡ expectedIntegerRootCount
integerIndexedRootsLengthIs112 =
  refl

integerRoots :
  E8RootList
integerRoots =
  List.map indexedRootToHalfTritRoot integerIndexedRoots

integerRootsLength :
  Nat
integerRootsLength =
  rootListLength integerRoots

integerRootsLengthIs112 :
  integerRootsLength ≡ expectedIntegerRootCount
integerRootsLengthIs112 =
  refl

evenSignVectors oddSignVectors :
  (n : Nat) →
  List (Vec E8Sign n)
evenSignVectors zero =
  []ᵥ ∷ []
evenSignVectors (suc n) =
  List.map (λ xs → positiveSign ∷ᵥ xs) (evenSignVectors n)
  ++
  List.map (λ xs → negativeSign ∷ᵥ xs) (oddSignVectors n)
oddSignVectors zero =
  []
oddSignVectors (suc n) =
  List.map (λ xs → positiveSign ∷ᵥ xs) (oddSignVectors n)
  ++
  List.map (λ xs → negativeSign ∷ᵥ xs) (evenSignVectors n)

signVectorToHalfIndexedRoot :
  Vec E8Sign 8 →
  E8IndexedRootCarrier
signVectorToHalfIndexedRoot =
  Vec.map halfSignCoordinate

halfIndexedRoots :
  E8IndexedRootList
halfIndexedRoots =
  List.map signVectorToHalfIndexedRoot (evenSignVectors 8)

halfIndexedRootsLength :
  Nat
halfIndexedRootsLength =
  indexedRootListLength halfIndexedRoots

halfIndexedRootsLengthIs128 :
  halfIndexedRootsLength ≡ expectedHalfRootCount
halfIndexedRootsLengthIs128 =
  refl

halfRoots :
  E8RootList
halfRoots =
  List.map indexedRootToHalfTritRoot halfIndexedRoots

halfRootsLength :
  Nat
halfRootsLength =
  rootListLength halfRoots

halfRootsLengthIs128 :
  halfRootsLength ≡ expectedHalfRootCount
halfRootsLengthIs128 =
  refl

combinedIndexedRoots :
  E8IndexedRootList
combinedIndexedRoots =
  integerIndexedRoots ++ halfIndexedRoots

combinedIndexedRootsLength :
  Nat
combinedIndexedRootsLength =
  indexedRootListLength combinedIndexedRoots

combinedIndexedRootsLengthIs240 :
  combinedIndexedRootsLength ≡ expectedTotalRootCount
combinedIndexedRootsLengthIs240 =
  refl

combinedRoots :
  E8RootList
combinedRoots =
  integerRoots ++ halfRoots

combinedRootsLength :
  Nat
combinedRootsLength =
  rootListLength combinedRoots

combinedRootsLengthIs240 :
  combinedRootsLength ≡ expectedTotalRootCount
combinedRootsLengthIs240 =
  refl

integerIndexedRootsNoDuplicatesCheck :
  Bool
integerIndexedRootsNoDuplicatesCheck =
  noDuplicatesIndexedRootList integerIndexedRoots

integerIndexedRootsNoDuplicatesCheckIsTrue :
  integerIndexedRootsNoDuplicatesCheck ≡ true
integerIndexedRootsNoDuplicatesCheckIsTrue =
  refl

halfIndexedRootsNoDuplicatesCheck :
  Bool
halfIndexedRootsNoDuplicatesCheck =
  noDuplicatesIndexedRootList halfIndexedRoots

halfIndexedRootsNoDuplicatesCheckIsTrue :
  halfIndexedRootsNoDuplicatesCheck ≡ true
halfIndexedRootsNoDuplicatesCheckIsTrue =
  refl

integerHalfIndexedRootsDisjointCheck :
  Bool
integerHalfIndexedRootsDisjointCheck =
  disjointIndexedRootLists integerIndexedRoots halfIndexedRoots

integerHalfIndexedRootsDisjointCheckIsTrue :
  integerHalfIndexedRootsDisjointCheck ≡ true
integerHalfIndexedRootsDisjointCheckIsTrue =
  refl

combinedIndexedRootsNoDuplicatesCheck :
  Bool
combinedIndexedRootsNoDuplicatesCheck =
  noDuplicatesIndexedRootList combinedIndexedRoots

combinedIndexedRootsNoDuplicatesCheckIsTrue :
  combinedIndexedRootsNoDuplicatesCheck ≡ true
combinedIndexedRootsNoDuplicatesCheckIsTrue =
  refl

halfIndexedRootsEvenParityByConstruction :
  halfIndexedRoots ≡ List.map signVectorToHalfIndexedRoot (evenSignVectors 8)
halfIndexedRootsEvenParityByConstruction =
  refl

-- Boolean-backed proof bridge layer.
--
-- These predicates are intentionally tied to the executable checks above.
-- They give downstream modules proof terms that the concrete computations
-- normalized as expected, but they are not yet native E8 lattice-membership or
-- completeness proofs.

data IndexedRootMember :
  {n : Nat} →
  Vec HTI.HalfTritIndexed n →
  List (Vec HTI.HalfTritIndexed n) →
  Set where
  memberByExecutableCheck :
    {n : Nat}
    {x : Vec HTI.HalfTritIndexed n}
    {xs : List (Vec HTI.HalfTritIndexed n)} →
    memberIndexedRoot x xs ≡ true →
    IndexedRootMember x xs

data IndexedRootNoDuplicates :
  {n : Nat} →
  List (Vec HTI.HalfTritIndexed n) →
  Set where
  noDuplicatesByExecutableCheck :
    {n : Nat}
    {xs : List (Vec HTI.HalfTritIndexed n)} →
    noDuplicatesIndexedRootList xs ≡ true →
    IndexedRootNoDuplicates xs

data IndexedRootFamiliesDisjoint :
  {n : Nat} →
  List (Vec HTI.HalfTritIndexed n) →
  List (Vec HTI.HalfTritIndexed n) →
  Set where
  disjointByExecutableCheck :
    {n : Nat}
    {xs ys : List (Vec HTI.HalfTritIndexed n)} →
    disjointIndexedRootLists xs ys ≡ true →
    IndexedRootFamiliesDisjoint xs ys

data HalfIndexedRootParitySound :
  E8IndexedRootList →
  Set where
  paritySoundByEvenSignVectorConstruction :
    {xs : E8IndexedRootList} →
    xs ≡ List.map signVectorToHalfIndexedRoot (evenSignVectors 8) →
    HalfIndexedRootParitySound xs

integerIndexedRootsNoDuplicatesBridge :
  IndexedRootNoDuplicates integerIndexedRoots
integerIndexedRootsNoDuplicatesBridge =
  noDuplicatesByExecutableCheck integerIndexedRootsNoDuplicatesCheckIsTrue

halfIndexedRootsNoDuplicatesBridge :
  IndexedRootNoDuplicates halfIndexedRoots
halfIndexedRootsNoDuplicatesBridge =
  noDuplicatesByExecutableCheck halfIndexedRootsNoDuplicatesCheckIsTrue

combinedIndexedRootsNoDuplicatesBridge :
  IndexedRootNoDuplicates combinedIndexedRoots
combinedIndexedRootsNoDuplicatesBridge =
  noDuplicatesByExecutableCheck combinedIndexedRootsNoDuplicatesCheckIsTrue

integerHalfIndexedRootsDisjointBridge :
  IndexedRootFamiliesDisjoint integerIndexedRoots halfIndexedRoots
integerHalfIndexedRootsDisjointBridge =
  disjointByExecutableCheck integerHalfIndexedRootsDisjointCheckIsTrue

halfIndexedRootsParitySoundBridge :
  HalfIndexedRootParitySound halfIndexedRoots
halfIndexedRootsParitySoundBridge =
  paritySoundByEvenSignVectorConstruction halfIndexedRootsEvenParityByConstruction

data E8NativePropositionalLiftTarget : Set where
  liftMemberIndexedRootToNativeRootMembership :
    E8NativePropositionalLiftTarget
  liftIndexedRootNoDuplicatesToNativeUnique :
    E8NativePropositionalLiftTarget
  liftIndexedRootFamiliesDisjointToNativeDisjoint :
    E8NativePropositionalLiftTarget
  liftHalfIndexedRootParitySoundToNativeEvenParity :
    E8NativePropositionalLiftTarget
  liftIntegerGeneratorToTwoSparseCompleteness :
    E8NativePropositionalLiftTarget
  liftHalfGeneratorToEvenParityCompleteness :
    E8NativePropositionalLiftTarget
  liftCombinedGeneratorToE8Completeness :
    E8NativePropositionalLiftTarget

canonicalE8NativePropositionalLiftTargets :
  List E8NativePropositionalLiftTarget
canonicalE8NativePropositionalLiftTargets =
  liftMemberIndexedRootToNativeRootMembership
  ∷ liftIndexedRootNoDuplicatesToNativeUnique
  ∷ liftIndexedRootFamiliesDisjointToNativeDisjoint
  ∷ liftHalfIndexedRootParitySoundToNativeEvenParity
  ∷ liftIntegerGeneratorToTwoSparseCompleteness
  ∷ liftHalfGeneratorToEvenParityCompleteness
  ∷ liftCombinedGeneratorToE8Completeness
  ∷ []

data E8StructuralBridgeResidualObligation : Set where
  bridgeExecutableMembershipToNativeMembership :
    E8StructuralBridgeResidualObligation
  bridgeExecutableNoDuplicatesToNativeNoDuplicates :
    E8StructuralBridgeResidualObligation
  bridgeExecutableDisjointnessToNativeDisjointness :
    E8StructuralBridgeResidualObligation
  bridgeEvenSignConstructionToNativeParityPredicate :
    E8StructuralBridgeResidualObligation
  proveIntegerTwoSparseCompleteness :
    E8StructuralBridgeResidualObligation
  proveHalfEvenParityCompleteness :
    E8StructuralBridgeResidualObligation
  proveCombinedE8Completeness :
    E8StructuralBridgeResidualObligation

canonicalE8StructuralBridgeResidualObligations :
  List E8StructuralBridgeResidualObligation
canonicalE8StructuralBridgeResidualObligations =
  bridgeExecutableMembershipToNativeMembership
  ∷ bridgeExecutableNoDuplicatesToNativeNoDuplicates
  ∷ bridgeExecutableDisjointnessToNativeDisjointness
  ∷ bridgeEvenSignConstructionToNativeParityPredicate
  ∷ proveIntegerTwoSparseCompleteness
  ∷ proveHalfEvenParityCompleteness
  ∷ proveCombinedE8Completeness
  ∷ []

record E8BooleanBackedStructuralBridgeLayer : Set where
  field
    integerFamilyNoDuplicates :
      IndexedRootNoDuplicates integerIndexedRoots

    halfFamilyNoDuplicates :
      IndexedRootNoDuplicates halfIndexedRoots

    combinedFamilyNoDuplicates :
      IndexedRootNoDuplicates combinedIndexedRoots

    integerHalfFamiliesDisjoint :
      IndexedRootFamiliesDisjoint integerIndexedRoots halfIndexedRoots

    halfFamilyParitySound :
      HalfIndexedRootParitySound halfIndexedRoots

    residualNativeProofObligations :
      List E8StructuralBridgeResidualObligation

    residualNativeProofObligationsAreCanonical :
      residualNativeProofObligations ≡
      canonicalE8StructuralBridgeResidualObligations

    nativePropositionalLiftTargets :
      List E8NativePropositionalLiftTarget

    nativePropositionalLiftTargetsAreCanonical :
      nativePropositionalLiftTargets ≡
      canonicalE8NativePropositionalLiftTargets

    completesE8RootEnumeration :
      Bool

    completesE8RootEnumerationIsFalse :
      completesE8RootEnumeration ≡ false

canonicalE8BooleanBackedStructuralBridgeLayer :
  E8BooleanBackedStructuralBridgeLayer
canonicalE8BooleanBackedStructuralBridgeLayer =
  record
    { integerFamilyNoDuplicates =
        integerIndexedRootsNoDuplicatesBridge
    ; halfFamilyNoDuplicates =
        halfIndexedRootsNoDuplicatesBridge
    ; combinedFamilyNoDuplicates =
        combinedIndexedRootsNoDuplicatesBridge
    ; integerHalfFamiliesDisjoint =
        integerHalfIndexedRootsDisjointBridge
    ; halfFamilyParitySound =
        halfIndexedRootsParitySoundBridge
    ; residualNativeProofObligations =
        canonicalE8StructuralBridgeResidualObligations
    ; residualNativeProofObligationsAreCanonical =
        refl
    ; nativePropositionalLiftTargets =
        canonicalE8NativePropositionalLiftTargets
    ; nativePropositionalLiftTargetsAreCanonical =
        refl
    ; completesE8RootEnumeration =
        false
    ; completesE8RootEnumerationIsFalse =
        refl
    }

data E8RootEnumerationProofObligation : Set where
  integerIndexedRootsNoDuplicatesObligation :
    E8RootEnumerationProofObligation
  integerIndexedRootsCompleteForTwoSparseShapeObligation :
    E8RootEnumerationProofObligation
  halfIndexedRootsEvenParitySoundnessObligation :
    E8RootEnumerationProofObligation
  halfIndexedRootsNoDuplicatesObligation :
    E8RootEnumerationProofObligation
  halfIndexedRootsCompleteForEvenParityShapeObligation :
    E8RootEnumerationProofObligation
  integerHalfIndexedRootsDisjointObligation :
    E8RootEnumerationProofObligation
  combinedIndexedRootsNoDuplicatesObligation :
    E8RootEnumerationProofObligation
  combinedIndexedRootsCompleteForE8ShapeObligation :
    E8RootEnumerationProofObligation

canonicalE8RootEnumerationProofObligations :
  List E8RootEnumerationProofObligation
canonicalE8RootEnumerationProofObligations =
  integerIndexedRootsNoDuplicatesObligation
  ∷ integerIndexedRootsCompleteForTwoSparseShapeObligation
  ∷ halfIndexedRootsEvenParitySoundnessObligation
  ∷ halfIndexedRootsNoDuplicatesObligation
  ∷ halfIndexedRootsCompleteForEvenParityShapeObligation
  ∷ integerHalfIndexedRootsDisjointObligation
  ∷ combinedIndexedRootsNoDuplicatesObligation
  ∷ combinedIndexedRootsCompleteForE8ShapeObligation
  ∷ []

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

    rootListCarrier :
      Set

    emptyRootListLength :
      Nat

    emptyRootListLengthIsZero :
      emptyRootListLength ≡ 0

    halfTritIndexedSurfaceStatus :
      HalfTritIndexedSurfaceStatus

    expectedHalfTritIndexedModule :
      String

    availableHalfTritIndexedReceipt :
      HTI.HalfTritIndexedReceipt

    availableHalfTritIndexedCarrier :
      Set

    availableHalfTritIndexedIndexCarrier :
      Set

    availableHalfTritIndexedToFin :
      HTI.HalfTritIndexed →
      HTI.HalfTritIndexedIndex

    availableIndexedFinToHalfTritEvidence :
      HTI.HalfTritIndexedIndex →
      HTI.HalfTritIndexed

    availableIndexedToFinToIndexedEvidence :
      (x : HTI.HalfTritIndexed) →
      availableIndexedFinToHalfTritEvidence
        (availableHalfTritIndexedToFin x)
      ≡
      x

    availableIndexedFinToIndexedToFinEvidence :
      (i : HTI.HalfTritIndexedIndex) →
      availableHalfTritIndexedToFin
        (availableIndexedFinToHalfTritEvidence i)
      ≡
      i

    availableIndexedHalfTritDecidableEqualityEvidence :
      (x y : HTI.HalfTritIndexed) →
      Dec (x ≡ y)

    availableIndexedAllHalfTritValuesEvidence :
      List HTI.HalfTritIndexed

    availableIndexedAllHalfTritValuesLengthEvidence :
      Nat

    availableIndexedAllHalfTritValuesLengthIsFiveEvidence :
      availableIndexedAllHalfTritValuesLengthEvidence ≡ 5

    availableIndexedAllHalfTritValuesNoDuplicatesEvidence :
      HTI.NoDuplicates availableIndexedAllHalfTritValuesEvidence

    availableHalfTritIndexedEmbedding :
      HT.HalfTrit →
      availableHalfTritIndexedCarrier

    availableHalfTritIndexedEmbeddingInjective :
      (x y : HT.HalfTrit) →
      availableHalfTritIndexedEmbedding x ≡
      availableHalfTritIndexedEmbedding y →
      x ≡ y

    availableHalfTritIndexedDuplicateFreedomStatus :
      HTI.HalfTritIndexedDuplicateFreedomStatus

    halfTritIndexedDoesNotCloseE8DuplicateFreedom :
      HTI.HalfTritIndexedReceipt.e8DuplicateFreedomClosedHere
        availableHalfTritIndexedReceipt
      ≡
      false

    halfTritIndexedDoesNotPromote :
      HTI.HalfTritIndexedReceipt.constructsPromotionClaim
        availableHalfTritIndexedReceipt
      ≡
      false

    preparedIndexedHalfTritRootCarrier :
      Set

    indexedRootListCarrier :
      Set

    emptyIndexedRootListLength :
      Nat

    emptyIndexedRootListLengthIsZero :
      emptyIndexedRootListLength ≡ 0

    availableHalfTritIndexedFields :
      List AvailableHalfTritIndexedField

    availableHalfTritIndexedFieldsAreCanonical :
      availableHalfTritIndexedFields ≡
      canonicalAvailableHalfTritIndexedFields

    requiredHalfTritIndexedFields :
      List RequiredHalfTritIndexedField

    requiredHalfTritIndexedFieldsAreCanonical :
      requiredHalfTritIndexedFields ≡ canonicalRequiredHalfTritIndexedFields

    availableCardinalityPrimitives :
      List AvailableCardinalityPrimitive

    availableCardinalityPrimitivesAreCanonical :
      availableCardinalityPrimitives ≡ canonicalAvailableCardinalityPrimitives

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

    availableConcreteGenerators :
      List AvailableConcreteE8Generator

    availableConcreteGeneratorsAreCanonical :
      availableConcreteGenerators ≡ canonicalAvailableConcreteE8Generators

    availableConcreteProofLayer :
      List AvailableConcreteE8ProofLayer

    availableConcreteProofLayerIsCanonical :
      availableConcreteProofLayer ≡ canonicalAvailableConcreteE8ProofLayer

    coordinatePairGenerator :
      List CoordinatePair8

    coordinatePairGeneratorLengthIs28 :
      length coordinatePairGenerator ≡ 28

    concreteIntegerIndexedRoots :
      E8IndexedRootList

    concreteIntegerIndexedRootsLength :
      Nat

    concreteIntegerIndexedRootsLengthIs112 :
      concreteIntegerIndexedRootsLength ≡ expectedIntegerRootCount

    concreteIntegerRoots :
      E8RootList

    concreteIntegerRootsLength :
      Nat

    concreteIntegerRootsLengthIs112 :
      concreteIntegerRootsLength ≡ expectedIntegerRootCount

    concreteHalfIndexedRoots :
      E8IndexedRootList

    concreteHalfIndexedRootsLength :
      Nat

    concreteHalfIndexedRootsLengthIs128 :
      concreteHalfIndexedRootsLength ≡ expectedHalfRootCount

    concreteHalfRoots :
      E8RootList

    concreteHalfRootsLength :
      Nat

    concreteHalfRootsLengthIs128 :
      concreteHalfRootsLength ≡ expectedHalfRootCount

    concreteCombinedIndexedRoots :
      E8IndexedRootList

    concreteCombinedIndexedRootsLength :
      Nat

    concreteCombinedIndexedRootsLengthIs240 :
      concreteCombinedIndexedRootsLength ≡ expectedTotalRootCount

    concreteCombinedRoots :
      E8RootList

    concreteCombinedRootsLength :
      Nat

    concreteCombinedRootsLengthIs240 :
      concreteCombinedRootsLength ≡ expectedTotalRootCount

    concreteIntegerIndexedRootsNoDuplicatesCheck :
      Bool

    concreteIntegerIndexedRootsNoDuplicatesCheckIsTrue :
      concreteIntegerIndexedRootsNoDuplicatesCheck ≡ true

    concreteHalfIndexedRootsNoDuplicatesCheck :
      Bool

    concreteHalfIndexedRootsNoDuplicatesCheckIsTrue :
      concreteHalfIndexedRootsNoDuplicatesCheck ≡ true

    concreteIntegerHalfIndexedRootsDisjointCheck :
      Bool

    concreteIntegerHalfIndexedRootsDisjointCheckIsTrue :
      concreteIntegerHalfIndexedRootsDisjointCheck ≡ true

    concreteCombinedIndexedRootsNoDuplicatesCheck :
      Bool

    concreteCombinedIndexedRootsNoDuplicatesCheckIsTrue :
      concreteCombinedIndexedRootsNoDuplicatesCheck ≡ true

    concreteHalfIndexedRootsEvenParityByConstruction :
      concreteHalfIndexedRoots ≡
      List.map signVectorToHalfIndexedRoot (evenSignVectors 8)

    booleanBackedStructuralBridgeLayer :
      E8BooleanBackedStructuralBridgeLayer

    booleanBackedStructuralBridgeDoesNotCompleteEnumeration :
      E8BooleanBackedStructuralBridgeLayer.completesE8RootEnumeration
        booleanBackedStructuralBridgeLayer
      ≡
      false

    structuralBridgeResidualObligations :
      List E8StructuralBridgeResidualObligation

    structuralBridgeResidualObligationsAreCanonical :
      structuralBridgeResidualObligations ≡
      canonicalE8StructuralBridgeResidualObligations

    nativePropositionalLiftTargets :
      List E8NativePropositionalLiftTarget

    nativePropositionalLiftTargetsAreCanonical :
      nativePropositionalLiftTargets ≡
      canonicalE8NativePropositionalLiftTargets

    remainingConcreteProofObligations :
      List E8RootEnumerationProofObligation

    remainingConcreteProofObligationsAreCanonical :
      remainingConcreteProofObligations ≡
      canonicalE8RootEnumerationProofObligations

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

    concreteCardinalityWitnessMissing :
      List ConcreteE8CardinalityWitnessMissing

    concreteCardinalityWitnessMissingIsCanonical :
      concreteCardinalityWitnessMissing ≡
      canonicalConcreteE8CardinalityWitnessMissing

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

    flipWhenHalfTritIndexedLands :
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
        E8RootCarrier
    ; rootListCarrier =
        E8RootList
    ; emptyRootListLength =
        rootListLength []
    ; emptyRootListLengthIsZero =
        refl
    ; halfTritIndexedSurfaceStatus =
        halfTritIndexedSurfaceAvailable
    ; expectedHalfTritIndexedModule =
        "DASHI.Algebra.Trit.HalfTritIndexed"
    ; availableHalfTritIndexedReceipt =
        HTI.canonicalHalfTritIndexedReceipt
    ; availableHalfTritIndexedCarrier =
        HTI.HalfTritIndexed
    ; availableHalfTritIndexedIndexCarrier =
        HTI.HalfTritIndexedIndex
    ; availableHalfTritIndexedToFin =
        HTI.indexedToFin
    ; availableIndexedFinToHalfTritEvidence =
        HTI.finToIndexed
    ; availableIndexedToFinToIndexedEvidence =
        HTI.indexedToFinToIndexed
    ; availableIndexedFinToIndexedToFinEvidence =
        HTI.finToIndexedToFin
    ; availableIndexedHalfTritDecidableEqualityEvidence =
        HTI._≟Indexed_
    ; availableIndexedAllHalfTritValuesEvidence =
        HTI.allHalfTritIndexedValues
    ; availableIndexedAllHalfTritValuesLengthEvidence =
        HTI.allHalfTritIndexedValuesLength
    ; availableIndexedAllHalfTritValuesLengthIsFiveEvidence =
        HTI.allHalfTritIndexedValuesLengthIsFive
    ; availableIndexedAllHalfTritValuesNoDuplicatesEvidence =
        HTI.allHalfTritIndexedValuesNoDuplicates
    ; availableHalfTritIndexedEmbedding =
        HTI.embedIndexed
    ; availableHalfTritIndexedEmbeddingInjective =
        HTI.embedIndexed-injective
    ; availableHalfTritIndexedDuplicateFreedomStatus =
        HTI.coordinateDuplicateFreedomEstablished
    ; halfTritIndexedDoesNotCloseE8DuplicateFreedom =
        refl
    ; halfTritIndexedDoesNotPromote =
        refl
    ; preparedIndexedHalfTritRootCarrier =
        E8IndexedRootCarrier
    ; indexedRootListCarrier =
        E8IndexedRootList
    ; emptyIndexedRootListLength =
        indexedRootListLength []
    ; emptyIndexedRootListLengthIsZero =
        refl
    ; availableHalfTritIndexedFields =
        canonicalAvailableHalfTritIndexedFields
    ; availableHalfTritIndexedFieldsAreCanonical =
        refl
    ; requiredHalfTritIndexedFields =
        canonicalRequiredHalfTritIndexedFields
    ; requiredHalfTritIndexedFieldsAreCanonical =
        refl
    ; availableCardinalityPrimitives =
        canonicalAvailableCardinalityPrimitives
    ; availableCardinalityPrimitivesAreCanonical =
        refl
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
    ; availableConcreteGenerators =
        canonicalAvailableConcreteE8Generators
    ; availableConcreteGeneratorsAreCanonical =
        refl
    ; availableConcreteProofLayer =
        canonicalAvailableConcreteE8ProofLayer
    ; availableConcreteProofLayerIsCanonical =
        refl
    ; coordinatePairGenerator =
        allCoordinatePairs8
    ; coordinatePairGeneratorLengthIs28 =
        allCoordinatePairs8Length
    ; concreteIntegerIndexedRoots =
        integerIndexedRoots
    ; concreteIntegerIndexedRootsLength =
        integerIndexedRootsLength
    ; concreteIntegerIndexedRootsLengthIs112 =
        integerIndexedRootsLengthIs112
    ; concreteIntegerRoots =
        integerRoots
    ; concreteIntegerRootsLength =
        integerRootsLength
    ; concreteIntegerRootsLengthIs112 =
        integerRootsLengthIs112
    ; concreteHalfIndexedRoots =
        halfIndexedRoots
    ; concreteHalfIndexedRootsLength =
        halfIndexedRootsLength
    ; concreteHalfIndexedRootsLengthIs128 =
        halfIndexedRootsLengthIs128
    ; concreteHalfRoots =
        halfRoots
    ; concreteHalfRootsLength =
        halfRootsLength
    ; concreteHalfRootsLengthIs128 =
        halfRootsLengthIs128
    ; concreteCombinedIndexedRoots =
        combinedIndexedRoots
    ; concreteCombinedIndexedRootsLength =
        combinedIndexedRootsLength
    ; concreteCombinedIndexedRootsLengthIs240 =
        combinedIndexedRootsLengthIs240
    ; concreteCombinedRoots =
        combinedRoots
    ; concreteCombinedRootsLength =
        combinedRootsLength
    ; concreteCombinedRootsLengthIs240 =
        combinedRootsLengthIs240
    ; concreteIntegerIndexedRootsNoDuplicatesCheck =
        integerIndexedRootsNoDuplicatesCheck
    ; concreteIntegerIndexedRootsNoDuplicatesCheckIsTrue =
        integerIndexedRootsNoDuplicatesCheckIsTrue
    ; concreteHalfIndexedRootsNoDuplicatesCheck =
        halfIndexedRootsNoDuplicatesCheck
    ; concreteHalfIndexedRootsNoDuplicatesCheckIsTrue =
        halfIndexedRootsNoDuplicatesCheckIsTrue
    ; concreteIntegerHalfIndexedRootsDisjointCheck =
        integerHalfIndexedRootsDisjointCheck
    ; concreteIntegerHalfIndexedRootsDisjointCheckIsTrue =
        integerHalfIndexedRootsDisjointCheckIsTrue
    ; concreteCombinedIndexedRootsNoDuplicatesCheck =
        combinedIndexedRootsNoDuplicatesCheck
    ; concreteCombinedIndexedRootsNoDuplicatesCheckIsTrue =
        combinedIndexedRootsNoDuplicatesCheckIsTrue
    ; concreteHalfIndexedRootsEvenParityByConstruction =
        halfIndexedRootsEvenParityByConstruction
    ; booleanBackedStructuralBridgeLayer =
        canonicalE8BooleanBackedStructuralBridgeLayer
    ; booleanBackedStructuralBridgeDoesNotCompleteEnumeration =
        refl
    ; structuralBridgeResidualObligations =
        canonicalE8StructuralBridgeResidualObligations
    ; structuralBridgeResidualObligationsAreCanonical =
        refl
    ; nativePropositionalLiftTargets =
        canonicalE8NativePropositionalLiftTargets
    ; nativePropositionalLiftTargetsAreCanonical =
        refl
    ; remainingConcreteProofObligations =
        canonicalE8RootEnumerationProofObligations
    ; remainingConcreteProofObligationsAreCanonical =
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
    ; concreteCardinalityWitnessMissing =
        canonicalConcreteE8CardinalityWitnessMissing
    ; concreteCardinalityWitnessMissingIsCanonical =
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
        ∷ "DASHI.Algebra.Trit.HalfTritIndexed is imported and provides coordinate-level injectivity"
        ∷ "HalfTritIndexed now provides Fin 5 roundtrips, decidable equality, and a no-duplicate five-value list"
        ∷ "HalfTrit.canonicalHalfTritComplete records constructsE8RootEnumeration = false"
        ∷ "The preflight root-carrier shapes are EightVec HalfTrit and EightVec HalfTritIndexed"
        ∷ "HalfTritIndexed.canonicalHalfTritIndexedReceipt records e8DuplicateFreedomClosedHere = false"
        ∷ "Nat, List, List.length, and Vec are available and wired into rootListLength"
        ∷ "The existing LILA-R2 receipt records count support only and theoremCompletedHere = false"
        ∷ "The integer family shape is two nonzero doubled +/-2 coordinates over all coordinate pairs and sign choices"
        ∷ "integerIndexedRoots concretely enumerates the 28 coordinate pairs times four sign choices and normalizes to length 112"
        ∷ "The half family shape is all eight-coordinate doubled +/-1 sign vectors with even minus parity"
        ∷ "halfIndexedRoots concretely enumerates even-parity sign vectors and normalizes to length 128"
        ∷ "combinedIndexedRoots appends the concrete integer and half families and normalizes to length 240"
        ∷ "Root-level indexed equality, membership, and executable duplicate/disjointness checks are now available"
        ∷ "The integer family, half family, and combined indexed list all compute no-duplicates = true"
        ∷ "The integer and half indexed families compute disjoint = true"
        ∷ "Boolean-backed structural bridge terms now package the normalized executable checks as proof objects"
        ∷ "The bridge layer records completesE8RootEnumeration = false until native predicates and completeness proofs are inhabited"
        ∷ "A complete receipt still needs structural proof bridges from these executable checks to propositional duplicate-freedom, membership, and completeness predicates"
        ∷ []
    ; flipWhenHalfTritLands =
        "HalfTrit is available locally; keep importing it without redefining it here"
        ∷ "Use EightVec HalfTrit as the root carrier shape"
        ∷ "integerRoots : List (EightVec HalfTrit) now exists with normalized length 112"
        ∷ "halfRoots : List (EightVec HalfTrit) now exists with normalized length 128"
        ∷ "Root-level decidable equality and executable no-duplicate/disjointness checks now normalize successfully"
        ∷ "Boolean-backed bridge terms now expose those normalized checks to downstream Agda surfaces"
        ∷ "Bridge the executable checks to structural no-duplicates, disjointness, membership, and completeness proofs"
        ∷ "Only then replace this obstruction with an E8RootEnumerationComplete receipt"
        ∷ []
    ; flipWhenHalfTritIndexedLands =
        "HalfTritIndexed is available locally; keep consuming its coordinate-level injectivity"
        ∷ "Finite index roundtrips, decidable equality, and all-values/no-duplicate facts are now available for coordinates"
        ∷ "Indexed sign vectors now enumerate the 28 coordinate pairs times four signs for the 112 integer roots"
        ∷ "Indexed parity split over eight signs now enumerates the 128 half roots"
        ∷ "Executable disjointness/no-duplicate checks are bound; structural proof bridges remain before receiptCompletedHere can become true"
        ∷ "The current bridge is boolean-backed only and explicitly non-promoting"
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
