module DASHI.Core.FiniteReceiptList where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

finiteListCount : ∀ {a : Level} {A : Set a} → List A → Nat
finiteListCount =
  listCount

emptyList : ∀ {a : Level} {A : Set a} → List A
emptyList =
  []

singletonList : ∀ {a : Level} {A : Set a} → A → List A
singletonList x =
  x ∷ []

pairList : ∀ {a : Level} {A : Set a} → A → A → List A
pairList x y =
  x ∷ y ∷ []

tripleList : ∀ {a : Level} {A : Set a} → A → A → A → List A
tripleList x y z =
  x ∷ y ∷ z ∷ []

record CanonicalFiniteList {a : Level} (A : Set a) : Set a where
  constructor mkCanonicalFiniteList
  field
    canonicalItems :
      List A

    canonicalCount :
      Nat

    canonicalCountIsExact :
      canonicalCount ≡ listCount canonicalItems

open CanonicalFiniteList public

canonicalEmptyList :
  ∀ {a : Level} {A : Set a} → CanonicalFiniteList A
canonicalEmptyList =
  mkCanonicalFiniteList emptyList zero refl

canonicalSingletonList :
  ∀ {a : Level} {A : Set a} →
  A → CanonicalFiniteList A
canonicalSingletonList x =
  mkCanonicalFiniteList (singletonList x) (suc zero) refl

canonicalPairList :
  ∀ {a : Level} {A : Set a} →
  A → A → CanonicalFiniteList A
canonicalPairList x y =
  mkCanonicalFiniteList (pairList x y) (suc (suc zero)) refl

canonicalTripleList :
  ∀ {a : Level} {A : Set a} →
  A → A → A → CanonicalFiniteList A
canonicalTripleList x y z =
  mkCanonicalFiniteList (tripleList x y z) (suc (suc (suc zero))) refl

data AllFalseBy {a : Level} {A : Set a}
  (flag : A → Bool) : List A → Set a where
  allFalseNil :
    AllFalseBy flag []

  allFalseCons :
    ∀ {x : A} {xs : List A} →
    flag x ≡ false →
    AllFalseBy flag xs →
    AllFalseBy flag (x ∷ xs)

AllFalse : List Bool → Set
AllFalse =
  AllFalseBy (λ x → x)

allFalseEmpty :
  AllFalse []
allFalseEmpty =
  allFalseNil

allFalseSingleton :
  AllFalse (singletonList false)
allFalseSingleton =
  allFalseCons refl allFalseNil

allFalsePair :
  AllFalse (pairList false false)
allFalsePair =
  allFalseCons refl (allFalseCons refl allFalseNil)

allFalseTriple :
  AllFalse (tripleList false false false)
allFalseTriple =
  allFalseCons refl (allFalseCons refl (allFalseCons refl allFalseNil))

record BoolBearingItem : Set where
  constructor mkBoolBearingItem
  field
    itemFlag :
      Bool

open BoolBearingItem public

canonicalFalseItem :
  BoolBearingItem
canonicalFalseItem =
  mkBoolBearingItem false

canonicalTrueItem :
  BoolBearingItem
canonicalTrueItem =
  mkBoolBearingItem true

allBoolBearingItemsFalse :
  List BoolBearingItem → Set
allBoolBearingItemsFalse =
  AllFalseBy itemFlag

canonicalFalseItemList :
  CanonicalFiniteList BoolBearingItem
canonicalFalseItemList =
  canonicalSingletonList canonicalFalseItem

canonicalFalseItemListAllFalse :
  allBoolBearingItemsFalse (canonicalItems canonicalFalseItemList)
canonicalFalseItemListAllFalse =
  allFalseCons refl allFalseNil

canonicalBoolPairList :
  CanonicalFiniteList Bool
canonicalBoolPairList =
  canonicalPairList false true

canonicalBoolPairListCountIsTwo :
  canonicalCount canonicalBoolPairList ≡ suc (suc zero)
canonicalBoolPairListCountIsTwo =
  refl

canonicalBoolTripleAllFalse :
  CanonicalFiniteList Bool
canonicalBoolTripleAllFalse =
  canonicalTripleList false false false

canonicalBoolTripleAllFalseProof :
  AllFalse (canonicalItems canonicalBoolTripleAllFalse)
canonicalBoolTripleAllFalseProof =
  allFalseTriple
