module DASHI.Foundations.PMCardinalProlegomenaCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (_×_; _,_)

------------------------------------------------------------------------
-- PM Volume I cardinal prolegomena sockets.
--
-- These are labels and receipts for class/relation infrastructure before
-- cardinal arithmetic.  Arithmetic authority remains closed here.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

UnitClass : Set → Set₁
UnitClass A =
  A → Set

Couple : Set → Set → Set
Couple A B =
  A × B

data RelationMultiplicityLabel : Set where
  oneOneRelation :
    RelationMultiplicityLabel

  oneManyRelation :
    RelationMultiplicityLabel

  manyOneRelation :
    RelationMultiplicityLabel

  manyManyRelation :
    RelationMultiplicityLabel

data CardinalPreludeSocketKind : Set where
  unitClassSocket :
    CardinalPreludeSocketKind

  coupleSocket :
    CardinalPreludeSocketKind

  multiplicityLabelSocket :
    CardinalPreludeSocketKind

  similaritySocket :
    CardinalPreludeSocketKind

  selectionSocket :
    CardinalPreludeSocketKind

  powersPosteritySocket :
    CardinalPreludeSocketKind

  inductionOverFieldSocket :
    CardinalPreludeSocketKind

canonicalCardinalPreludeSocketKinds : List CardinalPreludeSocketKind
canonicalCardinalPreludeSocketKinds =
  unitClassSocket
  ∷ coupleSocket
  ∷ multiplicityLabelSocket
  ∷ similaritySocket
  ∷ selectionSocket
  ∷ powersPosteritySocket
  ∷ inductionOverFieldSocket
  ∷ []

canonicalCardinalPreludeSocketKindCount : Nat
canonicalCardinalPreludeSocketKindCount =
  listCount canonicalCardinalPreludeSocketKinds

record SimilaritySocket (A B : Set) : Set₁ where
  constructor mkSimilaritySocket
  field
    forward :
      A → B

    backward :
      B → A

    oneOneLabel :
      RelationMultiplicityLabel

record SelectionSocket (A : Set) : Set₁ where
  constructor mkSelectionSocket
  field
    selectionPredicate :
      A → Set

    selectionAuthority :
      Bool

    selectionAuthorityIsFalse :
      selectionAuthority ≡ false

record PowersPosteritySocket (A : Set) : Set₁ where
  constructor mkPowersPosteritySocket
  field
    successorRelation :
      A → A → Set

    posterityAuthority :
      Bool

    posterityAuthorityIsFalse :
      posterityAuthority ≡ false

record InductionOverFieldSocket (A : Set) : Set₁ where
  constructor mkInductionOverFieldSocket
  field
    fieldPredicate :
      A → Set

    inductionAuthority :
      Bool

    inductionAuthorityIsFalse :
      inductionAuthority ≡ false

record CardinalArithmeticAuthorityBoundary : Set where
  constructor mkCardinalArithmeticAuthorityBoundary
  field
    boundaryLabel :
      String

    cardinalPreludeSocketPresent :
      Bool

    cardinalPreludeSocketPresentIsTrue :
      cardinalPreludeSocketPresent ≡ true

    cardinalArithmeticAuthority :
      Bool

    cardinalArithmeticAuthorityIsFalse :
      cardinalArithmeticAuthority ≡ false

    infiniteCardinalAuthority :
      Bool

    infiniteCardinalAuthorityIsFalse :
      infiniteCardinalAuthority ≡ false

canonicalCardinalArithmeticAuthorityBoundary :
  CardinalArithmeticAuthorityBoundary
canonicalCardinalArithmeticAuthorityBoundary =
  mkCardinalArithmeticAuthorityBoundary
    "pm-cardinal-prolegomena-boundary"
    true
    refl
    false
    refl
    false
    refl

BoolSimilaritySocket : SimilaritySocket Bool Bool
BoolSimilaritySocket =
  mkSimilaritySocket
    (λ b → b)
    (λ b → b)
    oneOneRelation

BoolSelectionSocket : SelectionSocket Bool
BoolSelectionSocket =
  mkSelectionSocket
    (λ b → b ≡ true)
    false
    refl

cardinalPreludeDoesNotPromoteArithmetic :
  CardinalArithmeticAuthorityBoundary.cardinalArithmeticAuthority
    canonicalCardinalArithmeticAuthorityBoundary
  ≡
  false
cardinalPreludeDoesNotPromoteArithmetic =
  refl
