module DASHI.Algebra.Trit.HalfTritIndexed where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; _∷_; []; length)
open import Relation.Nullary using (Dec; yes; no)

import DASHI.Algebra.Trit.HalfTrit as Half

------------------------------------------------------------------------
-- Indexed HalfTrit coordinate surface.
--
-- Half.embedTrit is intentionally non-injective.  This module adds a richer
-- coordinate code that preserves the five HalfTrit cases exactly.  The result
-- is enough for coordinate-level duplicate freedom, but it is not an E8 root
-- enumeration or a no-duplicates proof for a concrete 240-root list.

data HalfTritIndexed : Set where
  indexedNegOne :
    HalfTritIndexed
  indexedNegHalf :
    HalfTritIndexed
  indexedZero :
    HalfTritIndexed
  indexedPosHalf :
    HalfTritIndexed
  indexedPosOne :
    HalfTritIndexed

HalfTritIndexedIndex : Set
HalfTritIndexedIndex = Fin 5

indexedToFin :
  HalfTritIndexed →
  HalfTritIndexedIndex
indexedToFin indexedNegOne =
  zero
indexedToFin indexedNegHalf =
  suc zero
indexedToFin indexedZero =
  suc (suc zero)
indexedToFin indexedPosHalf =
  suc (suc (suc zero))
indexedToFin indexedPosOne =
  suc (suc (suc (suc zero)))

finToIndexed :
  HalfTritIndexedIndex →
  HalfTritIndexed
finToIndexed zero =
  indexedNegOne
finToIndexed (suc zero) =
  indexedNegHalf
finToIndexed (suc (suc zero)) =
  indexedZero
finToIndexed (suc (suc (suc zero))) =
  indexedPosHalf
finToIndexed (suc (suc (suc (suc zero)))) =
  indexedPosOne

indexedToFinToIndexed :
  (x : HalfTritIndexed) →
  finToIndexed (indexedToFin x) ≡ x
indexedToFinToIndexed indexedNegOne =
  refl
indexedToFinToIndexed indexedNegHalf =
  refl
indexedToFinToIndexed indexedZero =
  refl
indexedToFinToIndexed indexedPosHalf =
  refl
indexedToFinToIndexed indexedPosOne =
  refl

finToIndexedToFin :
  (i : HalfTritIndexedIndex) →
  indexedToFin (finToIndexed i) ≡ i
finToIndexedToFin zero =
  refl
finToIndexedToFin (suc zero) =
  refl
finToIndexedToFin (suc (suc zero)) =
  refl
finToIndexedToFin (suc (suc (suc zero))) =
  refl
finToIndexedToFin (suc (suc (suc (suc zero)))) =
  refl

_≟Indexed_ :
  (x y : HalfTritIndexed) →
  Dec (x ≡ y)
indexedNegOne ≟Indexed indexedNegOne =
  yes refl
indexedNegOne ≟Indexed indexedNegHalf =
  no (λ ())
indexedNegOne ≟Indexed indexedZero =
  no (λ ())
indexedNegOne ≟Indexed indexedPosHalf =
  no (λ ())
indexedNegOne ≟Indexed indexedPosOne =
  no (λ ())
indexedNegHalf ≟Indexed indexedNegOne =
  no (λ ())
indexedNegHalf ≟Indexed indexedNegHalf =
  yes refl
indexedNegHalf ≟Indexed indexedZero =
  no (λ ())
indexedNegHalf ≟Indexed indexedPosHalf =
  no (λ ())
indexedNegHalf ≟Indexed indexedPosOne =
  no (λ ())
indexedZero ≟Indexed indexedNegOne =
  no (λ ())
indexedZero ≟Indexed indexedNegHalf =
  no (λ ())
indexedZero ≟Indexed indexedZero =
  yes refl
indexedZero ≟Indexed indexedPosHalf =
  no (λ ())
indexedZero ≟Indexed indexedPosOne =
  no (λ ())
indexedPosHalf ≟Indexed indexedNegOne =
  no (λ ())
indexedPosHalf ≟Indexed indexedNegHalf =
  no (λ ())
indexedPosHalf ≟Indexed indexedZero =
  no (λ ())
indexedPosHalf ≟Indexed indexedPosHalf =
  yes refl
indexedPosHalf ≟Indexed indexedPosOne =
  no (λ ())
indexedPosOne ≟Indexed indexedNegOne =
  no (λ ())
indexedPosOne ≟Indexed indexedNegHalf =
  no (λ ())
indexedPosOne ≟Indexed indexedZero =
  no (λ ())
indexedPosOne ≟Indexed indexedPosHalf =
  no (λ ())
indexedPosOne ≟Indexed indexedPosOne =
  yes refl

allHalfTritIndexedValues :
  List HalfTritIndexed
allHalfTritIndexedValues =
  indexedNegOne
  ∷ indexedNegHalf
  ∷ indexedZero
  ∷ indexedPosHalf
  ∷ indexedPosOne
  ∷ []

allHalfTritIndexedValuesLength :
  Nat
allHalfTritIndexedValuesLength =
  length allHalfTritIndexedValues

allHalfTritIndexedValuesLengthIsFive :
  allHalfTritIndexedValuesLength ≡ 5
allHalfTritIndexedValuesLengthIsFive =
  refl

data NotIn :
  HalfTritIndexed →
  List HalfTritIndexed →
  Set where
  notInNil :
    {x : HalfTritIndexed} →
    NotIn x []
  notInCons :
    {x y : HalfTritIndexed}
    {ys : List HalfTritIndexed} →
    (x ≡ y → ⊥) →
    NotIn x ys →
    NotIn x (y ∷ ys)

data NoDuplicates :
  List HalfTritIndexed →
  Set where
  noDuplicatesNil :
    NoDuplicates []
  noDuplicatesCons :
    {x : HalfTritIndexed}
    {xs : List HalfTritIndexed} →
    NotIn x xs →
    NoDuplicates xs →
    NoDuplicates (x ∷ xs)

allHalfTritIndexedValuesNoDuplicates :
  NoDuplicates allHalfTritIndexedValues
allHalfTritIndexedValuesNoDuplicates =
  noDuplicatesCons
    (notInCons (λ ())
      (notInCons (λ ())
        (notInCons (λ ())
          (notInCons (λ ()) notInNil))))
    (noDuplicatesCons
      (notInCons (λ ())
        (notInCons (λ ())
          (notInCons (λ ()) notInNil)))
        (noDuplicatesCons
          (notInCons (λ ())
            (notInCons (λ ()) notInNil))
          (noDuplicatesCons
            (notInCons (λ ()) notInNil)
            (noDuplicatesCons
              notInNil
              noDuplicatesNil))))

embedIndexed :
  Half.HalfTrit →
  HalfTritIndexed
embedIndexed Half.negOne =
  indexedNegOne
embedIndexed Half.negHalf =
  indexedNegHalf
embedIndexed Half.zero =
  indexedZero
embedIndexed Half.posHalf =
  indexedPosHalf
embedIndexed Half.posOne =
  indexedPosOne

embedIndexed-injective :
  (x y : Half.HalfTrit) →
  embedIndexed x ≡ embedIndexed y →
  x ≡ y
embedIndexed-injective Half.negOne Half.negOne refl = refl
embedIndexed-injective Half.negOne Half.negHalf ()
embedIndexed-injective Half.negOne Half.zero ()
embedIndexed-injective Half.negOne Half.posHalf ()
embedIndexed-injective Half.negOne Half.posOne ()
embedIndexed-injective Half.negHalf Half.negOne ()
embedIndexed-injective Half.negHalf Half.negHalf refl = refl
embedIndexed-injective Half.negHalf Half.zero ()
embedIndexed-injective Half.negHalf Half.posHalf ()
embedIndexed-injective Half.negHalf Half.posOne ()
embedIndexed-injective Half.zero Half.negOne ()
embedIndexed-injective Half.zero Half.negHalf ()
embedIndexed-injective Half.zero Half.zero refl = refl
embedIndexed-injective Half.zero Half.posHalf ()
embedIndexed-injective Half.zero Half.posOne ()
embedIndexed-injective Half.posHalf Half.negOne ()
embedIndexed-injective Half.posHalf Half.negHalf ()
embedIndexed-injective Half.posHalf Half.zero ()
embedIndexed-injective Half.posHalf Half.posHalf refl = refl
embedIndexed-injective Half.posHalf Half.posOne ()
embedIndexed-injective Half.posOne Half.negOne ()
embedIndexed-injective Half.posOne Half.negHalf ()
embedIndexed-injective Half.posOne Half.zero ()
embedIndexed-injective Half.posOne Half.posHalf ()
embedIndexed-injective Half.posOne Half.posOne refl = refl

indexedSeparatesNegOneNegHalf :
  embedIndexed Half.negOne ≡ embedIndexed Half.negHalf →
  Half.negOne ≡ Half.negHalf
indexedSeparatesNegOneNegHalf =
  embedIndexed-injective Half.negOne Half.negHalf

indexedSeparatesPosHalfPosOne :
  embedIndexed Half.posHalf ≡ embedIndexed Half.posOne →
  Half.posHalf ≡ Half.posOne
indexedSeparatesPosHalfPosOne =
  embedIndexed-injective Half.posHalf Half.posOne

data HalfTritIndexedDuplicateFreedomStatus : Set where
  coordinateDuplicateFreedomEstablished :
    HalfTritIndexedDuplicateFreedomStatus
  e8RootDuplicateFreedomStillRequiresEnumerator :
    HalfTritIndexedDuplicateFreedomStatus

data HalfTritIndexedResidualObligation : Set where
  e8EightCoordinateIndexedCarrierStillMissing :
    HalfTritIndexedResidualObligation
  e8RootListEnumeratorStillMissing :
    HalfTritIndexedResidualObligation
  e8RootListNoDuplicatesStillMissing :
    HalfTritIndexedResidualObligation
  e8RootCompletenessStillMissing :
    HalfTritIndexedResidualObligation

canonicalHalfTritIndexedResidualObligations :
  List HalfTritIndexedResidualObligation
canonicalHalfTritIndexedResidualObligations =
  e8EightCoordinateIndexedCarrierStillMissing
  ∷ e8RootListEnumeratorStillMissing
  ∷ e8RootListNoDuplicatesStillMissing
  ∷ e8RootCompletenessStillMissing
  ∷ []

record HalfTritIndexedReceipt : Setω where
  field
    sourceHalfTrit :
      Half.HalfTritComplete

    coordinateCarrier :
      Set

    coordinateEmbedding :
      Half.HalfTrit →
      coordinateCarrier

    coordinateEmbeddingInjective :
      (x y : Half.HalfTrit) →
      coordinateEmbedding x ≡ coordinateEmbedding y →
      x ≡ y

    duplicateFreedomStatus :
      HalfTritIndexedDuplicateFreedomStatus

    e8DuplicateFreedomClosedHere :
      Bool

    residualObligations :
      List HalfTritIndexedResidualObligation

    residualObligationsAreCanonical :
      residualObligations ≡ canonicalHalfTritIndexedResidualObligations

    constructsE8RootEnumeration :
      Bool

    constructsPromotionClaim :
      Bool

    noPromotionBoundary :
      List String

canonicalHalfTritIndexedReceipt :
  HalfTritIndexedReceipt
canonicalHalfTritIndexedReceipt =
  record
    { sourceHalfTrit =
        Half.canonicalHalfTritComplete
    ; coordinateCarrier =
        HalfTritIndexed
    ; coordinateEmbedding =
        embedIndexed
    ; coordinateEmbeddingInjective =
        embedIndexed-injective
    ; duplicateFreedomStatus =
        coordinateDuplicateFreedomEstablished
    ; e8DuplicateFreedomClosedHere =
        false
    ; residualObligations =
        canonicalHalfTritIndexedResidualObligations
    ; residualObligationsAreCanonical =
        refl
    ; constructsE8RootEnumeration =
        false
    ; constructsPromotionClaim =
        false
    ; noPromotionBoundary =
        "HalfTritIndexed establishes coordinate-level injectivity only"
        ∷ "It does not claim Half.embedTrit is injective"
        ∷ "E8 duplicate freedom still requires an eight-coordinate carrier, enumerator, and no-duplicates proof"
        ∷ "No E8 enumeration, empirical promotion, or physics promotion is claimed here"
        ∷ []
    }

halfTritIndexedCoordinateDuplicateFreedom :
  HalfTritIndexedReceipt.duplicateFreedomStatus
    canonicalHalfTritIndexedReceipt
  ≡
  coordinateDuplicateFreedomEstablished
halfTritIndexedCoordinateDuplicateFreedom = refl

halfTritIndexedDoesNotCloseE8DuplicateFreedom :
  HalfTritIndexedReceipt.e8DuplicateFreedomClosedHere
    canonicalHalfTritIndexedReceipt
  ≡
  false
halfTritIndexedDoesNotCloseE8DuplicateFreedom = refl

halfTritIndexedDoesNotPromote :
  HalfTritIndexedReceipt.constructsPromotionClaim canonicalHalfTritIndexedReceipt
  ≡
  false
halfTritIndexedDoesNotPromote = refl
